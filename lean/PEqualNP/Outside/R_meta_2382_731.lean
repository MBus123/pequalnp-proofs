import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2382_731
    (routingPositive : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.Ustar G C).Nonempty →
      0 < 2 * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (largeResidual : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → 4 ≤ x7.card → x7.card ≤ x8) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  dsimp only
  intro C hsize hleast htop hjunk hcover hdouble
  let G := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
  let U := PEqualNP.TopForm.Ustar G C
  let j := (PEqualNP.TopForm.junk G C).card
  let c := (PEqualNP.TopForm.centreless G C).card
  let r := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
  change 2 ≤ j at hjunk
  change U.card ≤ 2 * c + j + r
  by_cases small : U.card ≤ 3
  · by_cases empty : U.card = 0
    · omega
    · have nonempty : U.Nonempty := Finset.card_pos.mp (by omega)
      have positive := routingPositive 11 G C hleast htop nonempty
      change 0 < 2 * c + r at positive
      omega
  · have four : 4 ≤ U.card := by omega
    exact largeResidual C hsize hleast htop hjunk hcover hdouble four
