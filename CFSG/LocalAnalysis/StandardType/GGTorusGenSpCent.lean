module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (coords gram gram_apply mat_transpose_mul_gram_mul par sgn)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

private theorem exists_unit_orderOf_eq_prime {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ≠ 1 ∧ ζ ≠ ζ⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpK' : p ∣ Nat.card Kˣ := by
    rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK'
  refine ⟨ζ, hζo, ?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  · intro h
    have hsq : ζ ^ 2 = ζ * ζ⁻¹ := by
      rw [sq]
      exact (mul_right_inj ζ).mpr h
    have h2 : ζ ^ 2 = 1 := by rw [hsq, mul_inv_cancel]
    have hdvd : p ∣ 2 := by
      rw [← hζo]
      exact orderOf_dvd_of_pow_eq_one h2
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)

private theorem exists_diagSpEntry_ne {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}
    (hζ1 : ζ ≠ 1) (hζinv : ζ ≠ ζ⁻¹) (hζp : ζ ^ p = 1)
    {a b : Fin m ⊕ Fin m} (hab : a ≠ b) :
    ∃ t : Fin m → Kˣ, t ^ p = 1 ∧ diagSpEntry t a ≠ diagSpEntry t b := by
  have hζ1K : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hζinvK : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun h => hζinv (Units.ext h)
  have hζinv1K : ((ζ⁻¹ : Kˣ) : K) ≠ 1 := fun h =>
    hζ1 (inv_eq_one.mp (Units.ext h))
  have hpow : ∀ i : Fin m, (Pi.mulSingle i ζ : Fin m → Kˣ) ^ p = 1 := by
    intro i
    rw [← Pi.mulSingle_pow, hζp, Pi.mulSingle_one]
  rcases a with i | i <;> rcases b with j | j
  · have hji : j ≠ i := fun h => hab (congrArg Sum.inl h.symm)
    exact ⟨Pi.mulSingle i ζ, hpow i, by
      rw [diagSpEntry_mulSingle_inl_self,
        diagSpEntry_mulSingle_of_not_mem i ζ (by simp [coords, hji])]
      exact hζ1K⟩
  · by_cases hji : j = i
    · rw [hji]
      exact ⟨Pi.mulSingle i ζ, hpow i, by
        rw [diagSpEntry_mulSingle_inl_self, diagSpEntry_mulSingle_inr_self]
        exact hζinvK⟩
    · exact ⟨Pi.mulSingle i ζ, hpow i, by
        rw [diagSpEntry_mulSingle_inl_self,
          diagSpEntry_mulSingle_of_not_mem i ζ (by simp [coords, hji])]
        exact hζ1K⟩
  · by_cases hji : j = i
    · rw [hji]
      exact ⟨Pi.mulSingle i ζ, hpow i, by
        rw [diagSpEntry_mulSingle_inr_self, diagSpEntry_mulSingle_inl_self]
        exact fun h => hζinvK h.symm⟩
    · exact ⟨Pi.mulSingle i ζ, hpow i, by
        rw [diagSpEntry_mulSingle_inr_self,
          diagSpEntry_mulSingle_of_not_mem i ζ (by simp [coords, hji])]
        exact hζinv1K⟩
  · have hji : j ≠ i := fun h => hab (congrArg Sum.inr h.symm)
    exact ⟨Pi.mulSingle i ζ, hpow i, by
      rw [diagSpEntry_mulSingle_inr_self,
        diagSpEntry_mulSingle_of_not_mem i ζ (by simp [coords, hji])]
      exact hζinv1K⟩

theorem mem_range_diagSp_of_commute_pTorsion {K : Type} [Field K] {m : ℕ} [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) {g : StatedSp m K}
    (hg : ∀ t : Fin m → Kˣ, t ^ p = 1 → Commute g (diagSp K m t)) :
    g ∈ (diagSp K m).range := by
  obtain ⟨ζ, hζo, hζ1, hζinv⟩ := exists_unit_orderOf_eq_prime hp hp2 hpK
  have hζp : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hzero : ∀ a b : Fin m ⊕ Fin m, a ≠ b → mat m K g a b = 0 := by
    intro a b hab
    obtain ⟨t, htp, hsep⟩ := exists_diagSpEntry_ne hζ1 hζinv hζp hab
    have hmat : mat m K g * mat m K (diagSp K m t) =
        mat m K (diagSp K m t) * mat m K g := by
      simpa only [map_mul] using congrArg (mat m K) (hg t htp).eq
    have h1 : mat m K g a b * diagSpEntry t b = diagSpEntry t a * mat m K g a b := by
      have h := congrFun (congrFun hmat a) b
      rwa [mat_diagSp, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h2 : mat m K g a b * (diagSpEntry t b - diagSpEntry t a) = 0 := by
      rw [mul_sub, h1, sub_eq_zero]
      exact mul_comm _ _
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hsep
  let v : Fin m ⊕ Fin m → K := fun a => mat m K g a a
  have hdiag : mat m K g = Matrix.diagonal v := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [v]
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact hzero a b hab
  have hsymp : (Matrix.diagonal v).transpose * gram K m * Matrix.diagonal v = gram K m := by
    rw [← hdiag]
    exact mat_transpose_mul_gram_mul g
  have hprod : ∀ i : Fin m, v (Sum.inl i) * v (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun hsymp (Sum.inl i)) (Sum.inr i)
    rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hg1 : gram K m (Sum.inl i) (Sum.inr i) = 1 := by
      simp [gram_apply, par, sgn]
    rw [hg1] at h
    simpa using h
  let x : Fin m → Kˣ := fun i =>
    Units.mk (v (Sum.inl i)) (v (Sum.inr i)) (hprod i) (by rw [mul_comm]; exact hprod i)
  have hx : mat m K g = mat m K (diagSp K m x) := by
    rw [hdiag, mat_diagSp]
    congr 1
    funext a
    rcases a with i | i <;> rfl
  exact ⟨x, (mat_injective hx).symm⟩

end CFSG.StandardType
