module

public import CFSG.ClassicalGroups.Orthogonal.FixedHypPair
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

namespace CFSG.RankThree.PartOne.CTP

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.Timmesfeld.ClassicalOrders

variable {K : Type} [Field K]

theorem card_hypPairs_congr {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] {Q : QuadraticForm K V} {Q' : QuadraticForm K W} (e : Q.IsometryEquiv Q') :
    Nat.card {x : V × V // Q x.1 = 0 ∧ Q x.2 = 0 ∧ polar Q x.1 x.2 = 1} =
      Nat.card {x : W × W // Q' x.1 = 0 ∧ Q' x.2 = 0 ∧ polar Q' x.1 x.2 = 1} := by
  have hpolar : ∀ x y : V, polar Q' (e x) (e y) = polar Q x y := by
    intro x y
    have h1 : e (x + y) = e x + e y := e.toLinearEquiv.map_add x y
    simp only [polar]
    rw [← h1, e.map_app, e.map_app, e.map_app]
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toLinearEquiv.toEquiv.prodCongr
    e.toLinearEquiv.toEquiv) fun x => ?_)
  change _ ↔ Q' (e x.1) = 0 ∧ Q' (e x.2) = 0 ∧ polar Q' (e x.1) (e x.2) = 1
  rw [e.map_app, e.map_app, hpolar]

variable [Finite K] [CharP K 2]

theorem card_hypPairs_quadMinus_four {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ×
          (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) //
        quadMinus 4 K b c x.1 = 0 ∧ quadMinus 4 K b c x.2 = 0 ∧
          polar (quadMinus 4 K b c) x.1 x.2 = 1} =
      (Nat.card K ^ 4 + 1) * (Nat.card K ^ 3 - 1) * Nat.card K ^ 6 := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hnd : (polarBilin (quadMinus 3 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have hW : Nat.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) = Nat.card K ^ 6 := by
    rw [card_coord_fun]
    simp
  have hS : (Nat.card {v // quadMinus 4 K b c v = 0} : ℤ) =
      1 + ((Nat.card K : ℤ) ^ 4 + 1) * ((Nat.card K : ℤ) ^ 3 - 1) :=
    (card_quadMinus 3 hirr).1
  have e := minusIsometry K 2 b c
  rw [card_hypPairs_congr e]
  rw [card_hypPairs hnd CharTwo.two_eq_zero, ← card_singular_congr e, hW]
  congr 1
  have h1 : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ hq
  have h2 : (Nat.card {v // quadMinus 4 K b c v = 0} : ℤ) - 1 =
      ((Nat.card K ^ 4 + 1) * (Nat.card K ^ 3 - 1) : ℕ) := by
    push_cast [h1]
    rw [hS]
    ring
  have h3 := one_le_card_singular (quadMinus 4 K b c)
  zify [h3]
  exact h2

omit [Finite K] [CharP K 2] in
theorem not_dvd_hypPairs_count {q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h4 : (q : ZMod p) ^ 4 = 1) (h1 : (q : ZMod p) ≠ 1) (hq : 1 ≤ q) :
    ¬ p ∣ (q ^ 4 + 1) * (q ^ 3 - 1) * q ^ 6 := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · have h0 : ((q ^ 4 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
      push_cast at h0
      rw [h4] at h0
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        rw [← h0]
        norm_num
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        ((ZMod.natCast_eq_zero_iff 2 p).1 h2))
    · have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
      have h0 : ((q ^ 3 - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
      rw [Nat.cast_sub h3] at h0
      push_cast at h0
      have h3' : (q : ZMod p) ^ 3 = 1 := sub_eq_zero.1 h0
      apply h1
      calc (q : ZMod p) = (q : ZMod p) * (q : ZMod p) ^ 3 := by rw [h3', mul_one]
        _ = (q : ZMod p) ^ 4 := by ring
        _ = 1 := h4
  · have h0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_of_dvd_pow hd)
    rw [h0] at h4
    norm_num at h4

theorem exists_fixed_hypPair_quadMinus_four {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K))}
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hexp : ∀ x ∈ E, x ^ p = 1) (h4 : ((Nat.card K : ℕ) : ZMod p) ^ 4 = 1)
    (h1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1) :
    ∃ P : HypPair (quadMinus 4 K b c), ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f := by
  have : Fact p.Prime := ⟨hp⟩
  refine exists_fixed_hypPair hE hexp ?_
  rw [card_hypPairs_quadMinus_four hirr]
  exact not_dvd_hypPairs_count hp hp2 h4 h1 (Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne')

end CFSG.RankThree.PartOne.CTP
