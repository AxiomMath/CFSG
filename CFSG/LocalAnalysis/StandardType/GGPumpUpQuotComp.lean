module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Transfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.HOutDiagLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1pp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType

private theorem pptp4_autFix_eq_fixSubgroup {K : Type} [Group K] (ζ : MulAut K) :
    autFix ζ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ζ :=
  Subgroup.ext fun _ => Iff.rfl

private theorem pptp4_center_eq_bot_of_center_trivial {K : Type} [Group K] {W : Subgroup K}
    (hW : ∀ k ∈ W, (∀ y ∈ W, k * y = y * k) → k = 1) :
    Subgroup.center W = ⊥ := by
  apply le_antisymm
  · intro k hk
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hW (k : K) k.2 (fun y hy => ?_))
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hk ⟨y, hy⟩)).symm
  · exact bot_le

private theorem pptp4_quotient_injective {K : Type} [Group K] {W : Subgroup K}
    (hW : ∀ k ∈ W, (∀ y ∈ W, k * y = y * k) → k = 1) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center K)).comp W.subtype) := by
  intro a b hab
  apply Subtype.ext
  have hmem : (a : K) * (b : K)⁻¹ ∈ Subgroup.center K := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center K), MonoidHom.mem_ker]
    show QuotientGroup.mk' (Subgroup.center K) ((a : K) * (b : K)⁻¹) = 1
    have hab' : QuotientGroup.mk' (Subgroup.center K) (a : K) =
        QuotientGroup.mk' (Subgroup.center K) (b : K) := hab
    rw [map_mul, map_inv, hab', mul_inv_cancel]
  have hmemW : (a : K) * (b : K)⁻¹ = 1 :=
    hW _ (mul_mem a.2 (inv_mem b.2)) (fun y hy => (Subgroup.mem_center_iff.1 hmem y).symm)
  rwa [mul_inv_eq_one] at hmemW

theorem pumpUp_quotient_component
    {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) :
    let S := K ⧸ Subgroup.center K
    let β := CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ
    let J := W.map (QuotientGroup.mk' (Subgroup.center K))
    β ^ 3 = 1 ∧
      CFSG.Open.GLAPComponent 3
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J ∧
      CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J
        (fun l => l = ⟨.twA, 4, 1⟩) := by
  have hWcent : ∀ k ∈ W, (∀ y ∈ W, k * y = y * k) → k = 1 :=
    center_trivial_of_U52 h.W_model
  have hWcenter : Subgroup.center W = ⊥ := pptp4_center_eq_bot_of_center_trivial hWcent
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center K)).comp W.subtype) :=
    pptp4_quotient_injective hWcent
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let φ : ↥W →* ↥(W.map π) :=
    (π.comp W.subtype).codRestrict (W.map π) (fun w => Subgroup.mem_map_of_mem π w.2)
  have hφinj : Function.Injective φ := fun a b hab => hinj (Subtype.ext_iff.mp hab)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  let e : ↥W ≃* ↥(W.map π) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hJquasi : CFSG.Open.IsQuasisimple ↥(W.map π) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isQuasisimple_of_mulEquiv' e.symm h.W_comp.2.2
  have h3W : 3 ∣ Nat.card W := by
    have hcard : Nat.card W = 13685760 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
        (CFSG.Models.LieModel.statedClassicalModel h.W_model (by decide))
    rw [hcard]
    norm_num
  have hJcomp : CFSG.Open.GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ζ) W := by
    have h0 := CFSG.HardMathSupport.Solomon.Coordinator.i253_glaPComponent_of_subnormal
      h.W_comp.1 h.W_comp.2.1 h.W_comp.2.2 h3W
    simpa only [pptp4_autFix_eq_fixSubgroup ζ] using h0
  have hWblue : CFSG.Blueprint.LieModel W .PSU 5 2 1 :=
    CFSG.Models.LieModel.toBlueprint (by decide) h.W_model
  have hWquot : CFSG.Blueprint.LieModel (W ⧸ Subgroup.center W) .PSU 5 2 1 :=
    CFSG.Blueprint.LieModel.quotient_center hWcenter hWblue
  have hJquot : CFSG.Blueprint.LieModel
      (↥(W.map π) ⧸ Subgroup.center ↥(W.map π)) .PSU 5 2 1 :=
    CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e hWquot
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot
    hJquasi.1 hJquot
  have hlab := CFSG.StandardType.Canonical.largeEvenMarking_mono
    (fun lab _ _ _ _ _ hlab =>
      CFSG.LocalAnalysis.GLTheoremA.S171.hod_lab_triple_twA
        ⟨hlab.1, hlab.2.1, hlab.2.2.2⟩) hmark
  have hK144 := CFSG.LocalAnalysis.GLTheoremA.K144.centerQuot_component h.ζ_cube hJcomp
  exact ⟨hK144.1, hK144.2.1, hlab⟩

end CFSG.GGQ2Prime

end
