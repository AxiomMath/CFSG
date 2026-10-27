module

public import CFSG.Quasithin.Vol2.Ch11SecBK7B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace K7

variable {K : Type} [Field K]

theorem eq_trv_of_fix [CharP K 2] {γ : ↥(StatedSp 2 K)} {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hγ : ∀ x, Matrix.toBilin' (spJ K) x y = 0 → mat 2 K γ *ᵥ x = x) :
    ∃ c : K, γ = trv y c := by
  obtain ⟨x₀, hx₀⟩ := exists_bil_eq_one hy
  set δ := mat 2 K γ *ᵥ x₀ - x₀ with hδ
  have hperp : ∀ x, Matrix.toBilin' (spJ K) (x - Matrix.toBilin' (spJ K) x y • x₀) y = 0 :=
    fun x => by rw [sub_eq_add_neg, bil_add_left, ← neg_smul, bil_smul_left, hx₀]; ring
  have h1 : ∀ x, mat 2 K γ *ᵥ x = x + Matrix.toBilin' (spJ K) x y • δ := by
    intro x
    have e : x = (x - Matrix.toBilin' (spJ K) x y • x₀) + Matrix.toBilin' (spJ K) x y • x₀ := by
      abel
    conv_lhs => rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, hγ _ (hperp x)]
    rw [hδ, smul_sub]
    abel
  have h2 : ∀ x, Matrix.toBilin' (spJ K) x y = 0 → Matrix.toBilin' (spJ K) δ x = 0 := by
    intro x hx
    have := spB_mat γ x₀ x
    rw [hγ x hx, show mat 2 K γ *ᵥ x₀ = x₀ + δ by rw [hδ]; abel, bil_add_left] at this
    linear_combination this
  have h3 : δ = Matrix.toBilin' (spJ K) δ x₀ • y := by
    rw [← sub_eq_zero]
    apply toBilin'_spJ_nondegenerate.1
    intro x
    have := h2 _ (hperp x)
    rw [sub_eq_add_neg, bil_add_right, ← neg_smul, bil_smul_right] at this
    rw [sub_eq_add_neg, bil_add_left, ← neg_smul, bil_smul_left, bil_comm y x]
    linear_combination this
  obtain ⟨c, hc⟩ : ∃ c : K, δ = c • y := ⟨_, h3⟩
  refine ⟨c, sp_ext fun x => ?_⟩
  rw [h1, hc, trv_mulVec, smul_smul, mul_comm]

theorem fix_perp_of_plane {γ : ↥(StatedSp 2 K)} (hP : ∀ x ∈ spPlane K, mat 2 K γ *ᵥ x = x)
    {k : Fin 2 ⊕ Fin 2 → K} (hk : mat 2 K γ *ᵥ k = k) (hkP : k ∉ spPlane K) {x : Fin 2 ⊕ Fin 2 → K}
    (hx : Matrix.toBilin' (spJ K) x (vec4 (k (.inr 1)) (-k (.inr 0)) 0 0) = 0) :
    mat 2 K γ *ᵥ x = x := by
  have hx' : x (.inr 1) * k (.inr 0) = x (.inr 0) * k (.inr 1) := by
    rw [toBilin'_spJ_apply] at hx
    simp only [Fin.sum_univ_two, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1] at hx
    linear_combination hx
  obtain ⟨t, ht⟩ : ∃ t : K, x - t • k ∈ spPlane K := by
    by_cases h0 : k (.inr 0) = 0
    · have h1 : k (.inr 1) ≠ 0 := fun h1 => hkP ⟨h0, h1⟩
      refine ⟨x (.inr 1) / k (.inr 1), ?_, ?_⟩
      · have : x (.inr 0) = 0 := by
          rw [h0, mul_zero] at hx'
          exact (mul_eq_zero.mp hx'.symm).resolve_right h1
        simp [this, h0]
      · simp [div_mul_cancel₀ _ h1]
    · refine ⟨x (.inr 0) / k (.inr 0), ?_, ?_⟩
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination hx'
  have e : x = (x - t • k) + t • k := by abel
  rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, hP _ ht, hk]

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem bil_eq_zero_of_trv_fix (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {c : K} (hc : c ≠ 0) {w : W}
    (hw : ((π (trv y c) : ↥H) : MulAut W) w = w) : Matrix.toBilin' (spJ K) (f w) y = 0 := by
  have h := congrArg f hw
  rw [hf.act4, trv_mulVec, add_eq_left, smul_eq_zero] at h
  exact (mul_eq_zero.mp (h.resolve_right hy)).resolve_left hc

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
