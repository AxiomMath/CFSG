module

public import CFSG.Sporadic.Co1Patterson.TwistNativeType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (ind)

theorem mem_QG_of_centEmb {x : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hx : centEmb x ∈ twoAQ) : (x : NativeSporadic.Co1) ∈ nativeSetting.QG :=
  ⟨x, by rw [nativeSetting_Q]; exact hx, rfl⟩

theorem yH_mem_QG (i : ℕ) : (yH i : NativeSporadic.Co1) ∈ nativeSetting.QG :=
  mem_QG_of_centEmb (by rw [centEmb_yH]; exact yG_mem_twoAQ i)

theorem yprodH_mem_QG (c : ℕ) : (yprodH c : NativeSporadic.Co1) ∈ nativeSetting.QG :=
  mem_QG_of_centEmb (by rw [centEmb_yprodH]; exact yprodG_mem_twoAQ c)

theorem coe_comm_iff {x y : centralizer ({aNC} : Set NativeSporadic.Co1)} :
    (x : NativeSporadic.Co1) * y = y * x ↔ centEmb x * centEmb y = centEmb y * centEmb x := by
  rw [← map_mul, ← map_mul, centEmb_injective.eq_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    Subtype.coe_inj]

@[expose] noncomputable def coordL : nativeSetting.Qt →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearMap.pi fun i : Fin 8 =>
    QuadraticMap.polarBilin nativeSetting.q
      (nativeSetting.cl (yH (((i : ℕ) + 4) % 8) : NativeSporadic.Co1))

theorem coordL_apply (v : nativeSetting.Qt) (i : Fin 8) :
    coordL v i = QuadraticMap.polar nativeSetting.q
      (nativeSetting.cl (yH (((i : ℕ) + 4) % 8) : NativeSporadic.Co1)) v := rfl

theorem finrank_Qt_native : Module.finrank (ZMod 2) nativeSetting.Qt = 8 := by
  rw [nativeSetting.finrank_Qt_eq_two_mul_width, width_nativeSetting]

theorem nativeOmega :
    nativeSetting.Mbar.map nativeSetting.O.subtype = CFSG.Open.timmesfeldOmega nativeSetting.q :=
  map_Mbar_eq_omega_of_card nativeSetting width_nativeSetting card_Mbar_nativeSetting

theorem coordL_cl_yprod (c : ℕ) :
    coordL (nativeSetting.cl (yprodH c : NativeSporadic.Co1)) = bv c := by
  rw [← yprodH_mod, ← bv_mod]
  have hc : c % 256 < 256 := Nat.mod_lt _ (by norm_num)
  funext i
  rw [coordL_apply, bv_apply]
  have hcomm := yprodG_comm_iff hc i.2
  have hpol := nativeSetting.polar_cl_eq_zero_iff (yH_mem_QG (((i : ℕ) + 4) % 8))
    (yprodH_mem_QG (c % 256))
  rw [coe_comm_iff, centEmb_yH, centEmb_yprodH] at hpol
  rcases zmod_two_cases (QuadraticMap.polar nativeSetting.q
    (nativeSetting.cl (yH (((i : ℕ) + 4) % 8) : NativeSporadic.Co1))
    (nativeSetting.cl (yprodH (c % 256) : NativeSporadic.Co1))) with h0 | h1
  · rw [h0]
    have := hcomm.1 (hpol.1 h0).symm
    rw [this]
    rfl
  · rw [h1]
    have hne : ¬ ((c % 256).testBit i = false) := fun hb => by
      have := hpol.2 (hcomm.2 hb).symm
      rw [h1] at this
      exact one_ne_zero this
    rw [Bool.not_eq_false] at hne
    rw [hne]
    rfl

theorem coordL_surjective : Function.Surjective coordL := fun v => by
  obtain ⟨c, -, rfl⟩ := exists_bv v
  exact ⟨_, coordL_cl_yprod c⟩

theorem coordL_injective : Function.Injective coordL :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_Qt_native, Module.finrank_fin_fun])).2 coordL_surjective

theorem q₀_coordL (v : nativeSetting.Qt) : q₀ (coordL v) = nativeSetting.q v := by
  obtain ⟨x, hx, rfl⟩ := nativeSetting.exists_cl v
  obtain ⟨c, hc, hcv⟩ := exists_bv (coordL (nativeSetting.cl x))
  have hcl : nativeSetting.cl x = nativeSetting.cl (yprodH c : NativeSporadic.Co1) :=
    coordL_injective (by rw [coordL_cl_yprod, hcv])
  rw [← hcv, q₀_bv, hcl]
  have hq := nativeSetting.q_cl_eq_zero_iff (yprodH_mem_QG c)
  have hsq : (yprodH c : NativeSporadic.Co1) ^ 2 = 1 ↔ yprodG c * yprodG c = 1 := by
    rw [sq, ← centEmb_yprodH, ← map_mul, ← Subgroup.coe_mul, ← map_one centEmb,
      centEmb_injective.eq_iff, ← Subgroup.coe_one, Subtype.coe_inj]
  rw [hsq, yprodG_sq_eq_one_iff hc] at hq
  rcases zmod_two_cases (nativeSetting.q (nativeSetting.cl (yprodH c : NativeSporadic.Co1)))
    with h0 | h1
  · rw [h0, ind_eq_zero_iff]
    exact hq.1 h0
  · rw [h1, ind_eq_one_iff]
    cases hb : CFSG.EvenSmallLie.OmegaEight.qNat c
    · have := hq.2 hb
      rw [h1] at this
      exact absurd this one_ne_zero
    · rfl

@[expose] noncomputable def coordIso : nativeSetting.q.IsometryEquiv q₀ where
  toLinearEquiv := LinearEquiv.ofBijective coordL ⟨coordL_injective, coordL_surjective⟩
  map_app' := q₀_coordL

theorem coordIso_cl_yprod (c : ℕ) :
    coordIso (nativeSetting.cl (yprodH c : NativeSporadic.Co1)) = bv c :=
  coordL_cl_yprod c

theorem coordIso_symm_bv (c : ℕ) :
    coordIso.symm (bv c) = nativeSetting.cl (yprodH c : NativeSporadic.Co1) := by
  rw [QuadraticMap.IsometryEquiv.symm_apply_eq, coordIso_cl_yprod]

@[expose] noncomputable def typeSystemC :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀
      (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  Setting.typeSystemOf nativeSetting coordIso nativeOmega

theorem typeSystemC_vec (m : centralizer ({aNC} : Set NativeSporadic.Co1)) :
    typeSystemC.vec m = coordIso (nativeSetting.cl (m : NativeSporadic.Co1)) := rfl

theorem vec_yprodH (c : ℕ) : typeSystemC.vec (yprodH c) = bv c := coordIso_cl_yprod c

theorem vec_yprodH_mul_z (c : ℕ) : typeSystemC.vec (yprodH c * typeSystemC.z) = bv c := by
  rw [typeSystemC_vec, Subgroup.coe_mul]
  exact (congrArg coordIso (nativeSetting.cl_mul_z (yprodH_mem_QG c))).trans
    (coordIso_cl_yprod c)

theorem phi_bv_of_conj (h : centralizer ({aNC} : Set NativeSporadic.Co1)) (m : List ℕ)
    (hm : ∀ k < 8, h * yH k * h⁻¹ = yprodH (m.getD k 0) ∨
      h * yH k * h⁻¹ = yprodH (m.getD k 0) * typeSystemC.z) (v : ℕ) :
    ((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv v) =
      bv (colsApply m v) := by
  refine apply_bv_of_cols (((typeSystemC.φ h : L₀) :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] _) m
    (fun k hk => ?_) v
  change ((Setting.phiV₀ nativeSetting coordIso nativeOmega h : L₀) :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv (2 ^ k)) = _
  rw [Setting.coe_phiV₀_apply nativeSetting coordIso nativeOmega h, coordIso_symm_bv,
    yprodH_two_pow hk, nativeSetting.ρ_cl h (yH_mem_QG k)]
  have e : (h : NativeSporadic.Co1) * (yH k : NativeSporadic.Co1) * (h : NativeSporadic.Co1)⁻¹ =
      ((h * yH k * h⁻¹ : centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) :=
    rfl
  rw [e]
  rcases hm k hk with h1 | h1
  · rw [h1, coordIso_cl_yprod]
  · rw [h1, Subgroup.coe_mul]
    exact (congrArg coordIso (nativeSetting.cl_mul_z (yprodH_mem_QG _))).trans
      (coordIso_cl_yprod _)

end CFSG.Sporadic.Co1Patterson.TwistNative
