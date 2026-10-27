module

public import CFSG.Monster.B.Rep4371.FourEigen
public import CFSG.Monster.B.Cbar.GenData
public import CFSG.Monster.B.Cbar.Correspondence

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.B.Short Matrix

noncomputable abbrev Vst : Submodule ℚ SpaceB := V4 rStar

theorem apply_aStar_of_mem_Cgen
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Cgen) : g aStar = aStar := by
  have h := Cgen_le hg
  have hc : g * rhoEquiv rStar = rhoEquiv rStar * g :=
    Subgroup.mem_centralizer_singleton_iff.1 h.2
  exact concrete_axis_centralizer_correspondence.2.2.2.2 rStar isShortCoord_rStar g h.1 hc

theorem mem_Vst_of_mem_Cgen
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Cgen) {v : SpaceB}
    (hv : v ∈ Vst) : g v ∈ Vst := by
  rw [mem_V4] at hv ⊢
  have hA : g ∈ AutO := Gmat_le_AutO (Cgen_le_Gmat hg)
  have h := (mem_AutO.1 hA).1 (axis rStar) v
  rw [show g (axis rStar) = axis rStar from apply_aStar_of_mem_Cgen hg] at h
  rw [← h, hv, map_smul]

@[expose] noncomputable def resV (g : Cgen) : Vst ≃ₗ[ℚ] Vst where
  toFun v := ⟨(g : SpaceB ≃ₗ[ℚ] SpaceB) v, mem_Vst_of_mem_Cgen g.2 v.2⟩
  invFun v := ⟨((g⁻¹ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) v, mem_Vst_of_mem_Cgen (g⁻¹).2 v.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  left_inv v := Subtype.ext (by
    change ((g⁻¹ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) ((g : SpaceB ≃ₗ[ℚ] SpaceB) v) = v
    rw [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply])
  right_inv v := Subtype.ext (by
    change (g : SpaceB ≃ₗ[ℚ] SpaceB) (((g⁻¹ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) v) = v
    rw [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply])

theorem coe_resV_apply (g : Cgen) (v : Vst) :
    ((resV g v : Vst) : SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) v := rfl

@[expose] noncomputable def chiC : Cgen →* (Vst ≃ₗ[ℚ] Vst) where
  toFun := resV
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem coe_chiC_apply (g : Cgen) (v : Vst) :
    ((chiC g v : Vst) : SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) v := rfl

theorem tAxis_apply_of_eigen4 (a v : SpaceB) (hv : gmul a v = (4 : ℚ) • v) : tAxis a v = v := by
  have h16 : (gmul a - (16 : ℚ) • 1) v = (-12 : ℚ) • v := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv]
    module
  have h4 : (gmul a - (4 : ℚ) • 1) ((-12 : ℚ) • v) = 0 := by
    rw [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self,
      smul_zero]
  change v - (16 / 217 : ℚ) • (gmul a ((gmul a - (4 : ℚ) • 1) ((gmul a - (16 : ℚ) • 1) v))) = v
  rw [h16, h4, map_zero, smul_zero, sub_zero]

theorem tStar_apply_of_mem_Vst {v : SpaceB} (hv : v ∈ Vst) : tStar v = v := by
  have h := LinearMap.congr_fun (tAxis_axis isShortCoord_rStar) v
  change tAxis (axis rStar) v = rhoEquiv rStar v at h
  rw [tStar, ← h]
  exact tAxis_apply_of_eigen4 _ _ (mem_V4.1 hv)

theorem chiC_tStarC : chiC tStarC = 1 :=
  LinearEquiv.ext fun v => Subtype.ext (tStar_apply_of_mem_Vst v.2)

theorem Zstar_le_ker_chiC : Zstar ≤ chiC.ker := by
  rw [Zstar, Subgroup.zpowers_le, MonoidHom.mem_ker]
  exact chiC_tStarC

@[expose] noncomputable def chi : Cbar →* (Vst ≃ₗ[ℚ] Vst) :=
  QuotientGroup.lift Zstar chiC Zstar_le_ker_chiC

theorem chi_kappa (g : Cgen) : chi (kappa g) = chiC g := rfl

theorem coe_chi_kappa_apply (g : Cgen) (v : Vst) :
    ((chi (kappa g) v : Vst) : SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) v := rfl

theorem exists_ne_zero_mem_Splus : ∃ q ∈ Splus rStar, q ≠ 0 := by
  set R : Matrix SpinIdx SpinIdx ℚ := ((rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) with hR
  have hR2 : R * R = 1 := by
    have h := sq_eq_one_of_isShort isShortCoord_rStar
    rw [sq] at h
    have h' := congrArg (fun g : Q => ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) h
    simpa [hR] using h'
  have hRne : R ≠ -1 := by
    intro h
    have hz : rStar = zQ := by
      apply Subtype.ext
      apply Units.ext
      change R = ((zQ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)
      rw [h, coe_coe_zQ]
    have h0 : coordOf rStar = 0 := by
      rw [hz]
      exact (mem_zpowers_zQ_iff zQ).1 (Subgroup.mem_zpowers zQ)
    exact not_isShortCoord_zero (h0 ▸ isShortCoord_rStar)
  have hex : ∃ e : SpinIdx → ℚ, e ᵥ* R ≠ -e := by
    by_contra hall
    push Not at hall
    apply hRne
    ext i j
    have h := congrFun (hall (Pi.single i 1)) j
    rw [single_one_vecMul] at h
    rw [Matrix.neg_apply, Matrix.one_apply]
    rw [show R i j = R.row i j from rfl, h, Pi.neg_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  obtain ⟨e, he⟩ := hex
  refine ⟨e + e ᵥ* R, ?_, ?_⟩
  · change (e + e ᵥ* R) ᵥ* R = e + e ᵥ* R
    rw [add_vecMul, vecMul_vecMul, hR2, vecMul_one, add_comm]
  · intro h0
    apply he
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h0

theorem chi_xbar_ne_one : chi xbar ≠ 1 := by
  obtain ⟨q, hq, hq0⟩ := exists_ne_zero_mem_Splus
  have hv : tensorLin (uQ (shortCls isShortCoord_rStar)) q ∈ Vst :=
    Tplus_le_V4 isShortCoord_rStar ⟨q, hq, rfl⟩
  intro h
  have h1 := congrArg (fun f : Vst ≃ₗ[ℚ] Vst => ((f ⟨_, hv⟩ : Vst) : SpaceB)) h
  change xmat (tensorLin (uQ (shortCls isShortCoord_rStar)) q) =
    tensorLin (uQ (shortCls isShortCoord_rStar)) q at h1
  rw [xmat_eq_xB, xB_apply] at h1
  have h2 : -vecMulVec q (uQ (shortCls isShortCoord_rStar)) =
      vecMulVec q (uQ (shortCls isShortCoord_rStar)) :=
    congrArg (fun w : SpaceB => w.2.2) h1
  have h3 : vecMulVec q (uQ (shortCls isShortCoord_rStar)) = 0 := by
    have : (2 : ℚ) • vecMulVec q (uQ (shortCls isShortCoord_rStar)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h2]
      rw [neg_add_cancel]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hu : uQ (shortCls isShortCoord_rStar) ≠ 0 := by
    intro h0
    have := uQ_dotProduct_uQ_self (shortCls isShortCoord_rStar)
    rw [h0, zero_dotProduct] at this
    norm_num at this
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hu
  apply hq0
  funext i
  have := congrFun (congrFun h3 i) j
  rw [vecMulVec_apply, Matrix.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_right hj

theorem chi_injective
    [IsSimpleGroup Cbar] : Function.Injective chi := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal chi.ker with h | h
  · exact h
  · exfalso
    apply chi_xbar_ne_one
    have hx : xbar ∈ chi.ker := h ▸ Subgroup.mem_top xbar
    exact hx

end CFSG.Monster.B
