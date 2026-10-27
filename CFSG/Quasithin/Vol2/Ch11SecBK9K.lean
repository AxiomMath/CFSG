module

public import CFSG.Quasithin.Vol2.Ch11SecBK9J
public import CFSG.Quasithin.Vol2.Ch11SecBK9G
public import CFSG.Quasithin.Vol2.Ch11SecBK9I

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2]

namespace RootCocycle

@[expose] noncomputable def subSmul (R R' : RootCocycle K) (μ : K) : RootCocycle K where
  c γ := R.c γ - μ • R'.c γ
  mul γ δ := by
    rw [R.mul, R'.mul, smul_add, mulVec_sub, mulVec_smul]
    abel
  root y hy t := by
    obtain ⟨a, ha⟩ := R.root y hy t
    obtain ⟨b, hb⟩ := R'.root y hy t
    exact ⟨a - μ * b, by rw [ha, hb, smul_smul, sub_smul]⟩

theorem subSmul_c (R R' : RootCocycle K) (μ : K) (γ : ↥(StatedSp 2 K)) :
    (R.subSmul R' μ).c γ = R.c γ - μ • R'.c γ := rfl

theorem coef_subSmul [Finite K] (hK : Nat.card K = 4) (R R' : RootCocycle K) (μ : K)
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    ((R.subSmul R' μ).coef hK y).2 = (R.coef hK y).2 - μ * (R'.coef hK y).2 := by
  refine (lin_frob_unique hK (α := ((R.subSmul R' μ).coef hK y).1)
    (α' := (R.coef hK y).1 - μ * (R'.coef hK y).1) fun t => ?_).2
  rw [← (R.subSmul R' μ).rho_eq hK hy]
  apply smul_left_cancel hy
  rw [← (R.subSmul R' μ).rho_spec hy, subSmul_c, R.rho_spec hy, R'.rho_spec hy,
    R.rho_eq hK hy, R'.rho_eq hK hy, smul_smul, ← sub_smul]
  congr 1
  ring

end RootCocycle

namespace CovData

variable {W : Type*} [CommGroup W] (C : CovData K W) [Finite K] (hK : Nat.card K = 4)

@[expose] noncomputable def kapCocycle : RootCocycle K where
  c := C.kappa hK
  mul := C.kappa_mul hK
  root _ hy t := C.exists_kappa_trv hK hy t

@[expose] noncomputable def beta : K := ((C.kapCocycle hK).coef hK (KGNat.vec4 1 0 0 0)).2

theorem e0_ne : (KGNat.vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
  (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))

theorem coef_kap {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    ((C.kapCocycle hK).coef hK y).2 = C.beta hK :=
  (C.kapCocycle hK).beta_eq hK e0_ne hy

include hK in
theorem chi_trv {y d : Fin 2 ⊕ Fin 2 → K} {α t : K}
    (hκ : C.kappa hK (K7.trv y t) = (α * t) • y) (hd : spB K d y = α) (w : W) :
    C.chi d (C.pi' (K7.trv y t) w) = C.chi d w := by
  have hinv : (K7.trv y t)⁻¹ = K7.trv y t := inv_eq_of_mul_eq_one_right (trv_mul_self y t)
  have hsymm : (C.pi' (K7.trv y t)).symm w = C.pi' (K7.trv y t) w := by
    rw [show (C.pi' (K7.trv y t)).symm = (C.pi' (K7.trv y t))⁻¹ from rfl, ← C.pi'_inv, hinv]
  have h1 := C.ind_symm hK (K7.trv y t) w
  rw [hsymm, chi, hκ, K7.bil_smul_left] at h1
  rw [chi, h1, C.f_pi, K7.trv_mulVec, chi, map_add, map_smul, smul_eq_mul, hd, tr_add,
    K7.bil_comm (C.f w) y]
  have h2 : tr (t * spB K y (C.f w) * α) = tr (α * t * spB K y (C.f w)) := by
    congr 1
    ring
  have h3 := CharTwo.add_self_eq_zero (tr (α * t * spB K y (C.f w)))
  rw [h2]
  linear_combination h3

include hK in
theorem beta_ne_zero (hcomm : commV C.H = ⊤) : C.beta hK ≠ 0 := by
  intro hβ
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_add] at hω
    exact zero_ne_one hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [one_pow, CharTwo.add_self_eq_zero] at hω
    exact one_ne_zero hω
  set y : Fin 2 ⊕ Fin 2 → K := KGNat.vec4 1 0 0 0
  have hy : y ≠ 0 := e0_ne
  set α := ((C.kapCocycle hK).coef hK y).1
  have hκ : ∀ t, C.kappa hK (K7.trv y t) = (α * t) • y := fun t => by
    have h := (C.kapCocycle hK).rho_spec hy t
    rw [(C.kapCocycle hK).rho_eq hK hy, C.coef_kap hK hy, hβ, zero_mul, add_zero] at h
    exact h
  obtain ⟨x₀, hx₀⟩ := K7.exists_bil_eq_one hy
  set d := α • x₀
  have hd : spB K d y = α := by rw [K7.bil_smul_left, hx₀, mul_one]
  have hle : K7.acomm C.π y ≤ C.compl d := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨t, w, rfl⟩
    show C.chi d (C.pi' (K7.trv y t) w * w⁻¹) = 0
    rw [C.inv_eq, C.chi_mul, C.chi_trv hK (hκ t) hd, CharTwo.add_self_eq_zero]
  have hZ := K7.le_acomm C.coord C.fixZ hcomm C.sq hω0 hω1 hy
  exact C.z_not_mem_compl d (hle (hZ C.z_mem))

include hK in
theorem exists_psi (hcomm : commV C.H = ⊤) :
    ∃ Ψ : (Fin 2 ⊕ Fin 2 → K) ≃ (Fin 2 ⊕ Fin 2 → K),
      ∀ γ a, Ψ (mat 2 K γ *ᵥ a + C.kappa hK γ) = mat 2 K γ *ᵥ Ψ a + bm hK γ := by
  set β := C.beta hK
  have hβ : β ≠ 0 := C.beta_ne_zero hK hcomm
  set R := (C.kapCocycle hK).subSmul (bmCocycle hK) β
  have hR : ∀ y : Fin 2 ⊕ Fin 2 → K, y ≠ 0 → (R.coef hK y).2 = 0 := fun y hy => by
    rw [RootCocycle.coef_subSmul hK _ _ _ hy, C.coef_kap hK hy, bmCocycle_coef hK hy, mul_one,
      sub_self]
  obtain ⟨d, hd⟩ := R.exists_coboundary hK hR
  have hdγ : ∀ γ, C.kappa hK γ = β • bm hK γ + (mat 2 K γ *ᵥ d - d) := fun γ => by
    have h := hd γ
    rw [RootCocycle.subSmul_c] at h
    change C.kappa hK γ - β • bm hK γ = _ at h
    rw [← h]
    abel
  refine ⟨{ toFun := fun a => β⁻¹ • (a + d)
            invFun := fun e => β • e - d
            left_inv := fun a => by
              simp only [smul_smul, mul_inv_cancel₀ hβ, one_smul, add_sub_cancel_right]
            right_inv := fun e => by
              simp only [sub_add_cancel, smul_smul, inv_mul_cancel₀ hβ, one_smul] },
    fun γ a => ?_⟩
  simp only [Equiv.coe_fn_mk]
  rw [hdγ, mulVec_smul, mulVec_add]
  rw [show mat 2 K γ *ᵥ a + (β • bm hK γ + (mat 2 K γ *ᵥ d - d)) + d =
    (mat 2 K γ *ᵥ a + mat 2 K γ *ᵥ d) + β • bm hK γ by abel, smul_add, smul_smul,
    inv_mul_cancel₀ hβ, one_smul]

end CovData

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
