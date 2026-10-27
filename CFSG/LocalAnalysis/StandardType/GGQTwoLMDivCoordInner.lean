module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerSu
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerPsu
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedVariables false in
theorem qTwoLMSkel_divCoord_suInner {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .suInner m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoHm m h3) ↥(sumZero m 3) Bs L x hN,
      IsHmModel m h3 (QTwoHm m h3) C.permV ∧
        IsAugModel m ↥(sumZero m 3) C.permVT := by
  letI := hFrameL.fieldF0
  letI := hFrameL.finiteF0
  letI := hFrameL.charF0
  letI := hFrameL.groupL0
  subst hFm
  exact qTwoLMDivCoordInner_su_assembly hG hBs hN hm h3 (F0 := hFrameL.F0) (L0 := hFrameL.L0)
    (c := hFrameL.c) (π := hFrameL.πSU) (ρ := hFrameL.ρ)
    ⟨hFrameL.hcardF0, hFrameL.hc_surj, hFrameL.hc_ker, hFrameL.hc_two, hFrameL.hπ_surj,
      hFrameL.hπ_ker, hFrameL.hdiag, hFrameL.hρ_induced⟩ hk

set_option linter.unusedVariables false in
theorem qTwoLMSkel_divCoord_psuInner {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .psuInner m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoHm m h3) (QTwoHm m h3) Bs L x hN,
      IsHmModel m h3 (QTwoHm m h3) C.permV ∧
        IsHmModel m h3 (QTwoHm m h3) C.permVT := by
  letI := hFrameL.fieldF0
  letI := hFrameL.finiteF0
  letI := hFrameL.charF0
  letI := hFrameL.groupL0
  subst hFm
  exact qTwoLMDivCoordInner_psu_assembly hG hBs hN hm h3 (F0 := hFrameL.F0) (L0 := hFrameL.L0)
    (c := hFrameL.c) (π := hFrameL.πSU) (ρ := hFrameL.ρ)
    ⟨hFrameL.hcardF0, hFrameL.hc_surj, hFrameL.hc_ker, hFrameL.hc_two, hFrameL.hπ_surj,
      hFrameL.hπ_ker, hFrameL.hdiag, hFrameL.hρ_induced⟩ hk

end CFSG.StandardType.QTwo

end
