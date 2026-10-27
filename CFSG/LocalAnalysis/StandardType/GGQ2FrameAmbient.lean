module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagRed
import CFSG.LocalAnalysis.StandardType.GGXInLDispatch
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGCSRHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclRed

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

private theorem l02qfra_innerDiagMarking {G : Type} [Group G] {Bs X : Subgroup G}
    (h : GGInnerDiagOn Bs X) : CFSG.Yardstones.Md0ec50421ce4.InnerDiagMarking Bs X := by
  dsimp only [GGInnerDiagOn, CFSG.Yardstones.Md0ec50421ce4.InnerDiagMarking] at h ⊢
  obtain ⟨hperf, lab, hlam, hrawLeg⟩ := h
  refine ⟨hperf, lab, hlam, ?_⟩
  refine CFSG.StandardType.largeEvenRawDatum_canonical_of_legacy_mono ?_ hrawLeg
  intro R _ I I' F hII' hQ
  obtain ⟨hs, hna, θ, hN, hφ⟩ := hQ
  exact ⟨hs, hna, θ, hN, fun b hb => by
    obtain ⟨φ, hφI, hind⟩ := hφ b hb
    exact ⟨φ, hII' hφI, hind⟩⟩

theorem ggG0_innerDiag_n_eq_one {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    ∃ lab : LargeEvenLabel, lab.n = 1 ∧
      GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs (ggG0 3 B x L D J) := by
  set H : Subgroup G := ggG0 3 B x L D J with hHdef
  have hHmark : GGInnerDiagOn Bs H := hS.1.2.2.2.2
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hStar : LargeEvenSStar 3 B x L := hThmI.2.2.2.2.2.2.1
  have hStdType : LargeEvenStandardType 3 B x L := hThmI.2.2.2.2.2.2.2
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hxB : x ∈ B := hStar.2.1
  have hx1 : x ≠ 1 := hStar.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hxB
  have hBsE : IsElemAbelian 3 Bs := hBstar.2.1
  have hLcompG : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hStar.2.2.2.1
  have hBSNH : Bs ≤ Subgroup.normalizer (H : Set G) := by
    have hmark' := hHmark
    dsimp only [GGInnerDiagOn] at hmark'
    obtain ⟨-, _lab, -, hraw⟩ := hmark'
    obtain ⟨R, _inst, I, F, _hs, _hna, _θ, hBSNH, -⟩ :=
      CFSG.StandardType.largeEvenRawDatum_exists hraw
    exact hBSNH
  have hHcan : CFSG.Assembly.LargeEvenMarking H
      (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (H : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
          (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    l02qfra_innerDiagMarking hHmark
  have hHquasi : CFSG.Open.IsQuasisimple ↥H :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_isQuasisimple
      (CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hHcan)
  obtain ⟨labH, hInnAll⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.FStdDiag.fstd_innDiagKind hHquasi hBSNH hHcan
  let β : MulAut (↥H ⧸ Subgroup.center ↥H) :=
    (normalizerToCenterQuotientAut H Bs hBSNH) ⟨x, hxBs⟩
  have hInn : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
      (↥H ⧸ Subgroup.center ↥H) labH β := hInnAll ⟨x, hxBs⟩
  have hcenS : Subgroup.center (↥H ⧸ Subgroup.center ↥H) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hHquasi
  have hHasS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel
      (↥H ⧸ Subgroup.center ↥H) (· = labH) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hInn
  have hlamH : LargeEvenInLambda2 labH :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hHasS
  have hhas : GGHasLabel labH (↥H ⧸ Subgroup.center ↥H) := by
    have hInn' := hInn
    dsimp only [CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind] at hInn'
    obtain ⟨-, lab0, _hlam, hraw0⟩ := hInn'
    obtain ⟨R, _inst, I, F, hs, hna, θ, hEq, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw0
    subst hEq
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw0
    rintro R' _ I' F' ⟨hs', hna', θ', -⟩
    exact ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcenS).symm.trans θ'⟩
  have hx_not_cent : x ∉ Subgroup.centralizer (H : Set G) := by
    intro hxH
    have hzle : Subgroup.zpowers x ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.zpowers_le.mpr hxH
    have hdvd : Nat.card (Subgroup.zpowers x) ∣
        Nat.card (Subgroup.centralizer (H : Set G)) :=
      Subgroup.card_dvd_of_le hzle
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hBsE.2 x hxBs) hx1
    rw [hcard] at hdvd
    exact not_dvd_card_centralizer_ggG0_of_stdSub Nat.prime_three hStar hStdType hStdSub hdvd
  have hβ1 : β ≠ 1 := by
    intro h
    have hxmem := (normalizerToCenterQuotientAut_eq_one_iff ⟨hHquasi.1⟩ hBSNH ⟨x, hxBs⟩).1 h
    exact hx_not_cent hxmem.2
  have hβ3 : β ^ 3 = 1 := by
    have hx3 : (⟨x, hxBs⟩ : ↥Bs) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hBsE.2 x hxBs, Subgroup.coe_one]
    have hmap := map_pow (normalizerToCenterQuotientAut H Bs hBSNH) (⟨x, hxBs⟩ : ↥Bs) 3
    rw [hx3, map_one] at hmap
    exact hmap.symm
  have hLleH : L ≤ H := by rw [hHdef]; exact le_sup_left
  have hLcompH : CFSG.Assembly.IsComponentOf L (H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hLcompG (le_inf hLleH hLcompG.1) inf_le_right
  have hLcompOpen : CFSG.Open.IsComponentOf L (H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hLcompH
  obtain ⟨hJcomp, hJiso⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.FStdDiag.fstd_image hHquasi hBSNH hxBs hLcompOpen
  have hleg : GGInnerDiagOnLabel GGLabQTwo 3 Bs L := hS.2.1
  dsimp only [GGInnerDiagOnLabel] at hleg
  obtain ⟨hLperf, labL, hlamL, hrawLleg⟩ := hleg
  have hrawLcan : CFSG.Assembly.LargeEvenRawDatum labL
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          GGLabQTwo 3 labL ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
            (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    refine CFSG.StandardType.largeEvenRawDatum_canonical_of_legacy_mono ?_ hrawLleg
    intro R _ I I' F hII' hQ
    obtain ⟨hs, hna, θ, hQ2, hN, hφ⟩ := hQ
    exact ⟨hs, hna, θ, hQ2, hN, fun b hb => by
      obtain ⟨φ, hφI, hind⟩ := hφ b hb
      exact ⟨φ, hII' hφI, hind⟩⟩
  have hnL : labL.n = 1 := by
    have hQ2 : GGLabQTwo 3 labL := by
      obtain ⟨R, _inst, I, F, _hs, _hna, _θ, hQ2, -⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawLcan
      exact hQ2
    have h1 : 1 ≤ labL.n := hlamL.1
    have h2 : labL.n < 2 := hQ2
    omega
  by_cases hB2 : labL.tag = .B2der
  · exact (CFSG.StandardType.GGXInL.lup8g_rank_contra hS hLperf hrawLleg
      (CFSG.StandardType.ggCSR_B2der hlamL hB2)).elim
  by_cases hG2 : labL.tag = .G2der
  · exact (CFSG.StandardType.GGXInL.lup8g_rank_contra hS hLperf hrawLleg
      (CFSG.StandardType.ggCSR_G2der hlamL hG2)).elim
  by_cases htw : labL.tag = .twD ∧ labL.rank = 2
  · exact (CFSG.StandardType.GGXInL.lup8g_rank_contra hS hLperf hrawLleg
      (CFSG.StandardType.largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num)
        hlamL (Or.inr htw))).elim
  have hchar : markChar labL = 2 := by
    rcases labL with ⟨tag, rank, n⟩
    cases tag
    case A => rfl
    case twA => rfl
    case B => rfl
    case C => rfl
    case D => rfl
    case twD => rfl
    case E6 => rfl
    case E7 => rfl
    case E8 => rfl
    case F4 => rfl
    case twE6 => rfl
    case triD4 => rfl
    case G2 => rfl
    case twB2 => rfl
    case twF4 => rfl
    case B2der => exact (hB2 rfl).elim
    case G2der => exact (hG2 rfl).elim
    case twF4der => rfl
  have hdeg : markDeg labL = 1 := by
    rcases labL with ⟨tag, rank, n⟩
    cases tag
    case twD =>
      by_cases hr : rank = 2
      · exact absurd ⟨rfl, hr⟩ htw
      · rw [markDeg, if_neg hr]
        exact hnL
    case B2der => exact (hB2 rfl).elim
    case G2der => rfl
    case A => rw [markDeg]; exact hnL
    case twA => rw [markDeg]; exact hnL
    case B => rw [markDeg]; exact hnL
    case C => rw [markDeg]; exact hnL
    case D => rw [markDeg]; exact hnL
    case E6 => rw [markDeg]; exact hnL
    case E7 => rw [markDeg]; exact hnL
    case E8 => rw [markDeg]; exact hnL
    case F4 => rw [markDeg]; exact hnL
    case twE6 => rw [markDeg]; exact hnL
    case triD4 => rw [markDeg]; exact hnL
    case G2 => rw [markDeg]; exact hnL
    case twB2 => rw [markDeg]; exact hnL
    case twF4 => rw [markDeg]; exact hnL
    case twF4der => rw [markDeg]; exact hnL
  have hLHas : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel L (· = labL) :=
    ⟨hLperf, labL, hlamL,
      CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, -⟩ := h
        exact ⟨hs, hna, θ, rfl⟩) hrawLcan⟩
  have hLModel : CFSG.StandardType.MarkedModel labL (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hLHas
  have hLModel21 : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L)
      (markTag labL) (markRank labL) 2 1 := by
    unfold CFSG.StandardType.MarkedModel at hLModel
    rw [hchar, hdeg] at hLModel
    exact hLModel
  obtain ⟨eJiso⟩ := hJiso
  have hJModel : CFSG.Blueprint.LieModel
      (↥((L.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H))) ⧸
        Subgroup.center ↥((L.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H))))
      (markTag labL) (markRank labL) 2 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv eJiso.symm hLModel21
  by_cases hnd : labH.tag ≠ .B2der ∧ labH.tag ≠ .G2der ∧ labH.tag ≠ .twF4der
  · have hnH : labH.n = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.S265C.DynO.n_eq_one_of_component_over_two
        hcenS hInn hβ3 hβ1 hnd hJcomp hJModel
    exact ⟨labH, hnH, ggInnerDiagOn_relabel ggLabelRigidInput_holds hHmark hlamH hhas⟩
  · have hder : labH.tag = .B2der ∨ labH.tag = .G2der ∨ labH.tag = .twF4der := by
      by_contra hc
      push Not at hc
      exact hnd ⟨hc.1, hc.2.1, hc.2.2⟩
    have hnH : labH.n = 1 := by
      rcases hder with h | h | h <;> (simp only [LargeEvenInLambda2, h] at hlamH <;> exact hlamH.2.2)
    exact ⟨labH, hnH, ggInnerDiagOn_relabel ggLabelRigidInput_holds hHmark hlamH hhas⟩

end CFSG.StandardType.GGQ2Frame
