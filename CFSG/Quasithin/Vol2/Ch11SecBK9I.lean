module

public import CFSG.Quasithin.Vol2.Ch11SecBK9H
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.Quasithin.Vol2.Ch11SecBK7C

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem eq_top_of_trv_mem {S : Subgroup ↥(StatedSp 2 K)} (h : ∀ y t, K7.trv y t ∈ S) :
    S = ⊤ := by
  have hle : Subgroup.closure {g | ∃ (a : Fin 2 ⊕ Fin 2 → K) (c : K),
      g = CFSG.RankThree.SubgroupLists.spTrans a c} ≤ S.map (StatedSp 2 K).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, c, rfl⟩
    refine ⟨K7.trv a c, h a c, ?_⟩
    apply CFSG.RankThree.SubgroupLists.gl_ext_mulVec
    intro x
    rw [CFSG.RankThree.SubgroupLists.spTrans_mulVec]
    exact K7.trv_mulVec a c x
  rw [eq_top_iff]
  intro γ _
  obtain ⟨s, hs, hsγ⟩ :=
    hle ((CFSG.RankThree.SubgroupLists.statedSp_eq_closure_spTrans (n := 2) (K := K)).le γ.2)
  rwa [show s = γ from Subtype.ext hsγ] at hs

variable [CharP K 2] [Finite K]

namespace RootCocycle

variable (R : RootCocycle K) (hK : Nat.card K = 4)

@[expose] noncomputable def alpha (y : Fin 2 ⊕ Fin 2 → K) : K := (R.coef hK y).1

include hK in
theorem alpha_zero : R.alpha hK 0 = 0 := by
  rw [alpha, R.coef_zero hK]

variable (hβ : ∀ y : Fin 2 ⊕ Fin 2 → K, y ≠ 0 → (R.coef hK y).2 = 0)

include hβ in
theorem c_trv {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t : K) :
    R.c (K7.trv y t) = (R.alpha hK y * t) • y := by
  rw [R.rho_spec hy, R.rho_eq hK hy, hβ y hy, zero_mul, add_zero]
  rfl

include hβ in
theorem alpha_add_of_bil {y y' : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (hb : spB K y y' ≠ 0) : R.alpha hK (y + y') = R.alpha hK y + R.alpha hK y' := by
  set γ := K7.trv y' (spB K y y')⁻¹ with hγ
  have hγy : mat 2 K γ *ᵥ y = y + y' := by
    rw [hγ, K7.trv_mulVec, inv_mul_cancel₀ hb, one_smul]
  have h := (R.coef_conj hK γ hy).1
  rw [hγy] at h
  show (R.coef hK (y + y')).1 = (R.coef hK y).1 + (R.coef hK y').1
  rw [h, hγ, R.c_trv hK hβ hy', K7.bil_smul_left, K7.bil_add_right, K7.bil_self, add_zero,
    K7.bil_comm y' y, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  rfl

include hβ in
theorem alpha_add (y y' : Fin 2 ⊕ Fin 2 → K) :
    R.alpha hK (y + y') = R.alpha hK y + R.alpha hK y' := by
  have h2v : ∀ v : Fin 2 ⊕ Fin 2 → K, v + v = 0 := fun v => by
    rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  by_cases hy : y = 0
  · rw [hy, zero_add, R.alpha_zero hK, zero_add]
  by_cases hy' : y' = 0
  · rw [hy', add_zero, R.alpha_zero hK, add_zero]
  by_cases hdep : ∃ μ : K, y' = μ • y
  · obtain ⟨μ, rfl⟩ := hdep
    have hμ : μ ≠ 0 := by
      rintro rfl
      exact hy' (zero_smul K y)
    have e : y + μ • y = (1 + μ) • y := by rw [add_smul, one_smul]
    rw [e]
    simp only [alpha]
    rw [R.alpha_smul hK hy hμ]
    by_cases h1 : 1 + μ = 0
    · have hμ1 : μ = 1 := by
        have := eq_neg_of_add_eq_zero_right h1
        rwa [CharTwo.neg_eq] at this
      rw [h1, zero_smul, R.coef_zero hK, hμ1, one_mul]
      exact (CharTwo.add_self_eq_zero _).symm
    · rw [R.alpha_smul hK hy h1]
      ring
  push Not at hdep
  by_cases hb : spB K y y' = 0
  · obtain ⟨ω, hω, -⟩ := exists_omega hK
    have hω0 : ω ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero, zero_add] at hω
      exact zero_ne_one hω
    have hω1 : 1 + ω ≠ 0 := by
      intro h
      have : ω = 1 := by
        have := eq_neg_of_add_eq_zero_right h
        rwa [CharTwo.neg_eq] at this
      rw [this, one_pow, CharTwo.add_self_eq_zero] at hω
      exact one_ne_zero hω
    obtain ⟨u, hu1, huω⟩ := K7.exists_bil_pair hy (fun μ h => hdep μ h) hb ω
    have hu : u ≠ 0 := by
      rintro rfl
      rw [map_zero] at hu1
      exact zero_ne_one hu1
    have hyu : y + u ≠ 0 := by
      intro h
      have : u = y := by
        have := eq_neg_of_add_eq_zero_right h
        rwa [CharTwo.neg_eq] at this
      rw [this, K7.bil_self] at hu1
      exact zero_ne_one hu1
    have hy'u : y' + u ≠ 0 := by
      intro h
      have : u = y' := by
        have := eq_neg_of_add_eq_zero_right h
        rwa [CharTwo.neg_eq] at this
      rw [this, K7.bil_self] at huω
      exact hω0 huω.symm
    have hbb : spB K (y + u) (y' + u) ≠ 0 := by
      rw [K7.bil_add_left, K7.bil_add_right, K7.bil_add_right, hb, hu1, K7.bil_self,
        K7.bil_comm u y', huω, zero_add, add_zero]
      exact hω1
    have e : y + y' = (y + u) + (y' + u) := by
      rw [show (y + u) + (y' + u) = (y + y') + (u + u) by abel, h2v, add_zero]
    rw [e, R.alpha_add_of_bil hK hβ hyu hy'u hbb,
      R.alpha_add_of_bil hK hβ hy hu (by rw [hu1]; exact one_ne_zero),
      R.alpha_add_of_bil hK hβ hy' hu (by rw [huω]; exact hω0)]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination R.alpha hK u * h2
  · exact R.alpha_add_of_bil hK hβ hy hy' hb

include hβ in
theorem exists_coboundary : ∃ d : Fin 2 ⊕ Fin 2 → K, ∀ γ, R.c γ = mat 2 K γ *ᵥ d - d := by
  let ell : Module.Dual K (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := R.alpha hK
      map_add' := R.alpha_add hK hβ
      map_smul' := fun a y => by
        by_cases hy : y = 0
        · rw [hy, smul_zero, R.alpha_zero hK, smul_eq_mul, mul_zero]
        by_cases ha : a = 0
        · rw [ha, zero_smul, R.alpha_zero hK, RingHom.id_apply, zero_smul]
        rw [alpha, R.alpha_smul hK hy ha]
        rfl }
  set d := ((spB K).toDual KGNat.toBilin'_spJ_nondegenerate).symm ell with hd
  have hdα : ∀ y, spB K d y = R.alpha hK y := fun y => by
    have h := LinearMap.BilinForm.toDual_def (b := KGNat.toBilin'_spJ_nondegenerate)
      (m := d) (n := y)
    rw [hd, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨d, fun γ => ?_⟩
  let S : Subgroup ↥(StatedSp 2 K) :=
    { carrier := {γ | R.c γ = mat 2 K γ *ᵥ d - d}
      one_mem' := by
        show R.c 1 = _
        rw [R.c_one, map_one, one_mulVec, sub_self]
      mul_mem' := fun {γ δ} hγ hδ => by
        show R.c (γ * δ) = _
        rw [R.mul, show R.c γ = _ from hγ, show R.c δ = _ from hδ, mulVec_sub, mulVec_mulVec,
          ← map_mul]
        abel
      inv_mem' := fun {γ} hγ => by
        show R.c γ⁻¹ = _
        have h1 := R.c_inv γ
        rw [show R.c γ = _ from hγ] at h1
        have h2 := congrArg (fun v => mat 2 K γ⁻¹ *ᵥ v) h1
        simp only [KGNat.mat_inv_mulVec] at h2
        rw [h2, mulVec_neg, mulVec_sub, KGNat.mat_inv_mulVec]
        abel }
  have hS : S = ⊤ := eq_top_of_trv_mem fun y t => by
    show R.c (K7.trv y t) = _
    by_cases hy : y = 0
    · rw [hy, show K7.trv 0 t = 1 from by
        rw [show (0 : Fin 2 ⊕ Fin 2 → K) = (0 : K) • (0 : Fin 2 ⊕ Fin 2 → K) from
          (zero_smul K _).symm, K7.trv_smul, zero_pow two_ne_zero, zero_mul, K7.trv_zero],
        R.c_one, map_one, one_mulVec, sub_self]
    rw [R.c_trv hK hβ hy, K7.trv_mulVec, add_sub_cancel_left, hdα, mul_comm]
  have hγ : γ ∈ S := hS ▸ Subgroup.mem_top γ
  exact hγ

end RootCocycle

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
