module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB
public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstarTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

@[expose] def W4Lem11_9b : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W),
      L ≤ Y → T ≤ Y → L ⊔ T = Y → (L.subgroupOf Y).Normal →
      IsComponentOf L Y → IsSylowIn 2 T Y → IsSpor ↥L .HS →
      fixV T ≠ fixV Y → bParam L Y ≤ 2

variable {W : Type} [CommGroup W] [Finite W]

theorem centralizer_inf_eq_bot_of_center_eq_bot {X P Y : Subgroup (MulAut W)}
    (hXY : X ≤ Y) (hPY : P ≤ Y) (hXP : X ⊔ P = Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) (hP : IsPGroup 2 ↥P)
    (hZ : Subgroup.center ↥X = ⊥) (hO2 : O2Trivial Y) :
    Subgroup.centralizer (X : Set (MulAut W)) ⊓ Y = ⊥ := by
  classical
  apply hO2 _ inf_le_right
  · refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun c y hc hy => ?_
    refine Subgroup.mem_inf.mpr ⟨?_, Y.mul_mem (Y.mul_mem hy hc.2) (Y.inv_mem hy)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : y⁻¹ * l * y⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem hy)) l).mp hl
    have hcomm : (y⁻¹ * l * y⁻¹⁻¹) * c = c * (y⁻¹ * l * y⁻¹⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hc.1) _ hl'
    calc l * (y * c * y⁻¹) = y * ((y⁻¹ * l * y⁻¹⁻¹) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * l * y⁻¹⁻¹)) * y⁻¹ := by rw [hcomm]
      _ = y * c * y⁻¹ * l := by group
  · rintro ⟨c, hc⟩
    have hNn : (X.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
    have hsup : X.subgroupOf Y ⊔ P.subgroupOf Y = ⊤ := by
      have h := Subgroup.subgroupOf_sup (A := X) (A' := P) (B := Y) hXY hPY
      rw [hXP, Subgroup.subgroupOf_self] at h
      rw [← h]
    let g : ↥Y := ⟨c, hc.2⟩
    have hmem : g ∈ X.subgroupOf Y ⊔ P.subgroupOf Y := by
      rw [hsup]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hpP : (p : MulAut W) ∈ P := Subgroup.mem_subgroupOf.mp hp
    obtain ⟨m, hm⟩ := hP ⟨(p : MulAut W), hpP⟩
    have hpm : p ^ 2 ^ m = 1 := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val hm
      simpa using h1
    have hqn : (QuotientGroup.mk' (X.subgroupOf Y)) n = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    have hqg : (QuotientGroup.mk' (X.subgroupOf Y)) (g ^ 2 ^ m) = 1 := by
      rw [← hnp, map_pow, map_mul, hqn, one_mul, ← map_pow, hpm, map_one]
    have hgX : g ^ 2 ^ m ∈ X.subgroupOf Y := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqg
      exact hqg
    have hcX : c ^ 2 ^ m ∈ X := by
      have h1 := Subgroup.mem_subgroupOf.mp hgX
      simpa [g] using h1
    have hcC : c ^ 2 ^ m ∈ Subgroup.centralizer (X : Set (MulAut W)) := pow_mem hc.1 _
    have hcZ : (⟨c ^ 2 ^ m, hcX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hcC) x x.2
    rw [hZ, Subgroup.mem_bot] at hcZ
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hcZ
    simpa using h1

theorem w4Lem11_9b_of_w4Lem11_9 (h : W4Lem11_9) :
    W4Lem11_9b := by
  intro W _ _ hw Y L T hLY hTY hLT hLN hcomp hsyl hHS hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup W := fixV (pCoreOf 2 Y)
  let Lb : Subgroup (MulAut ↥U) := autSub L U
  let Tb : Subgroup (MulAut ↥U) := autSub T U
  let Yb : Subgroup (MulAut ↥U) := autSub Y U
  have hst : Y ≤ stabSub U := B1Red.le_stabSub_fixV_pCoreOf Y
  have hker : Y ⊓ centSub U = pCoreOf 2 Y :=
    inf_centSub_fixV_pCoreOf_eq hw hLY hTY hLT hcomp hsyl
  have hQleT : pCoreOf 2 Y ≤ T :=
    hsyl.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hLs : IsSimpleGroup ↥L := by
    obtain ⟨e⟩ := hHS
    exact e.isSimpleGroup_congr.mpr CFSG.Sporadic.HS.isSimpleGroup_HS
  have hZL : Subgroup.center ↥L = ⊥ := uc22p21k_center_eq_bot hcomp.2.2
  have hLQ : L ⊓ pCoreOf 2 Y = ⊥ :=
    inf_pCoreOf_eq_bot_of_odd_center hcomp (by rw [hZL, Subgroup.card_bot]; exact odd_one)
  have hLnc : ¬ L ≤ centSub U := by
    intro hLc
    have hLQ' : L ≤ pCoreOf 2 Y := by
      intro x hx
      have hx' : x ∈ Y ⊓ centSub U := ⟨hLY hx, hLc hx⟩
      rwa [hker] at hx'
    have hq : CFSG.IsQuasisimple ↥L :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hcomp.2.2
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥L
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hLQ').isNilpotent
  have hLperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hcomp.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcompb : IsComponentOf Lb Yb := isComponentOf_autSub hLY hst hcomp hLnc
  have hsylb : IsSylowIn 2 Tb Yb := isSylowIn_autSub hTY hQleT hker hsyl
  have hfixb : fixV Tb ≠ fixV Yb := fixV_autSub_ne hTY hQleT hfix
  have hO2b : O2Trivial Yb := o2Trivial_autSub hw hLY hTY hLT hcomp hsyl
  have hLbYb : Lb ≤ Yb := autSub_mono hLY U
  have hTbYb : Tb ≤ Yb := autSub_mono hTY U
  have hsupb : Lb ⊔ Tb = Yb := by
    show autSub L U ⊔ autSub T U = autSub Y U
    rw [← hLT]
    exact (CFSG.CGT.PushingUpLit.BHS.autSub_sup (hLY.trans hst) (hTY.trans hst)).symm
  have hbne : bParam L Y ≤ bParam Lb Yb :=
    bParam_le_autSub hLY hst fun k A hA hne =>
      commutator_autSub_ne_bot_of_centralizer hLY hA.1 hst hker
        (CFSG.Quasithin.H13.Ch4.commutator_eq_bot_of_isComponentOf hcomp
          (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
        (inf_pCoreOf_le_centralizer_of_isComponent hcomp) hLperf hne
  have hLst : L ≤ stabSub U := hLY.trans hst
  have hfaith : L ⊓ centSub U = ⊥ := by
    calc L ⊓ centSub U = L ⊓ (Y ⊓ centSub U) := by rw [← inf_assoc, inf_eq_left.mpr hLY]
      _ = L ⊓ pCoreOf 2 Y := by rw [hker]
      _ = ⊥ := hLQ
  have hinj : Function.Injective (resHomOn U hLst) := resHomOn_injective_of_faithful hLst hfaith
  let eL : ↥L ≃* ↥Lb :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLst).symm)
  have hHSb : IsSpor ↥Lb .HS := by
    obtain ⟨f⟩ := hHS
    exact ⟨eL.symm.trans f⟩
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLN
  have hYbN : Yb ≤ Subgroup.normalizer (Lb : Set (MulAut ↥U)) :=
    CFSG.CGT.PushingUpLit.BHS.autSub_le_normalizer hYN
  have hLbN : (Lb.subgroupOf Yb).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYbN
  have hLbq : CFSG.Open.IsQuasisimple ↥Lb := hcompb.2.2
  have hLbqC : CFSG.IsQuasisimple ↥Lb := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLbq
  have hZLb : Subgroup.center ↥Lb = ⊥ := by
    rw [← Subgroup.map_center_eq eL, hZL, Subgroup.map_bot]
  have hO2Lb : O2Trivial Lb := by
    intro P hPY hPN hP2
    exact (Subgroup.subgroupOf_eq_bot.mp
      (CFSG.SeitzReduction.UnitaryPilot.forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center
        hLbqC (by rw [hZLb, Subgroup.card_bot]; exact odd_one) (P.subgroupOf Lb) hPN
        (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm))).eq_bot_of_le hPY
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (Lb : Set (MulAut ↥U)) ⊓ Yb)) := by
    rw [centralizer_inf_eq_bot_of_center_eq_bot hLbYb hTbYb hsupb hYbN hsylb.isPGroup hZLb hO2b,
      Subgroup.card_bot]
    exact odd_one
  have hgf := CFSG.GroupTheory.generalizedFitting_sup_eq_of_isPGroup_two hLbqC hLbYb hTbYb hLbN
    hsylb.isPGroup hCodd
  have hF : Fstar Yb = Lb := by
    have h' := fstar_eq_of_generalizedFitting_eq (le_sup_left : Lb ≤ Lb ⊔ Tb) hgf
    rwa [hsupb] at h'
  have h11 := h ↥U (fun u => Subtype.ext (hw (u : W))) Yb Lb Tb hLbYb hLbN hF hLbqC hO2Lb
    hHSb hTbYb hsylb hfixb
  exact hbne.trans (bParam_le_aParam.trans h11)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

