module

public import CFSG.RankThree.PartOne.KF.SU5Fixed

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.RankThree.PartOne.KFSU5

variable {n : ℕ} {K : Type} [Field K]

theorem mulVec_mem_fixSub_of_inv_conj {S : Subgroup (GL (Fin n) K)} {P : GL (Fin n) K}
    (hP : ∀ s ∈ S, P⁻¹ * s * P ∈ S) {v : Fin n → K} (hv : v ∈ fixSub S) :
    ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ fixSub S := by
  intro s hs
  have h1 := hP s hs
  have h2 : s * P = P * (P⁻¹ * s * P) := by group
  have h3 : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ * s * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_mul, ← Units.val_mul, h2]
  rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, hv _ h1]

theorem exists_ne_zero_mem_fixSub (hn : 1 ≤ n) [Finite K] (hK2 : 2 ∣ Nat.card K)
    {S : Subgroup (GL (Fin n) K)} (hS2 : IsPGroup 2 S) : ∃ v ∈ fixSub S, v ≠ 0 := by
  classical
  let P : SubMulAction ↥S (Fin n → K) :=
    { carrier := Set.univ
      smul_mem' := fun _ _ _ => trivial }
  have hdvd : 2 ∣ Nat.card P := by
    have h1 : Nat.card P = Nat.card (Fin n → K) := Nat.card_congr (Equiv.Set.univ _)
    rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact dvd_pow hK2 (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := inferInstance
  have h0 : (⟨0, trivial⟩ : P) ∈ MulAction.fixedPoints ↥S P := by
    rw [MulAction.mem_fixedPoints]
    intro s
    apply Subtype.ext
    show ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K) = 0
    exact Matrix.mulVec_zero _
  obtain ⟨b, hb, hb0⟩ := hS2.exists_fixed_point_of_prime_dvd_card_of_fixed_point P hdvd h0
  refine ⟨(b : Fin n → K), ?_, fun h => hb0 (Subtype.ext h.symm)⟩
  intro s hs
  have := (MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem eq_bot_of_fixSub_eq_top {S : Subgroup (GL (Fin n) K)} (h : fixSub S = ⊤) : S = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.ext
  intro k j
  have h1 : Pi.single j (1 : K) ∈ fixSub S := by rw [h]; trivial
  have h2 := congrFun (h1 s hs) k
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.one_apply, Pi.single_apply] using h2

end CFSG.RankThree.PartOne
