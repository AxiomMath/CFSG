module

public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoRowDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivLinkLift
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux2
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullW

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_divCoord_suFull
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .suFull m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoQm m) ↥(sumZero m 3) Bs L x hN,
      IsQmModel m (QTwoQm m) C.permV ∧
        IsAugModel m ↥(sumZero m 3) C.permVT := by
  obtain ⟨Θ, hnorm, hind⟩ := qTwoLMDivF_fullW hG hBs hN hm h3 hL hFrameL hFm hk.2
  letI := hFrameL.fieldF0
  letI := hFrameL.finiteF0
  letI := hFrameL.charF0
  letI := hFrameL.groupL0
  subst hFm
  have hU : QTwoDivInnerFrame hFrameL.m Bs L hN hFrameL.F0 hFrameL.L0 hFrameL.c hFrameL.πSU
      hFrameL.ρ :=
    ⟨hFrameL.hcardF0, hFrameL.hc_surj, hFrameL.hc_ker, hFrameL.hc_two, hFrameL.hπ_surj,
      hFrameL.hπ_ker, hFrameL.hdiag, hFrameL.hρ_induced⟩
  obtain ⟨ΘT, hnormT, hindT⟩ := qTwoLMDivF_fullT_suFull hG hBs hN hm h3
    (qTwoLMSkel_div_link hBs hN h3 hFrameL rfl) hU hk
  exact ⟨{ permV := qTwoLMDivF_permQHom hFrameL.m
           permVT := permAutVHom hFrameL.m 3
           theta := Θ
           norm_perm := hnorm
           perm_ind := hind
           thetaT := ΘT
           normT := hnormT
           indT := hindT },
    qTwoLMDivF_isQmModel hFrameL.m, qTwoLMDivF_isAugModel hFrameL.m⟩

theorem qTwoLMSkel_divCoord_psuFull
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .psuFull m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoQm m) (QTwoHm m h3) Bs L x hN,
      IsQmModel m (QTwoQm m) C.permV ∧
        IsHmModel m h3 (QTwoHm m h3) C.permVT := by
  obtain ⟨Θ, hnorm, hind⟩ := qTwoLMDivF_fullW hG hBs hN hm h3 hL hFrameL hFm hk.2
  letI := hFrameL.fieldF0
  letI := hFrameL.finiteF0
  letI := hFrameL.charF0
  letI := hFrameL.groupL0
  subst hFm
  have hU : QTwoDivInnerFrame hFrameL.m Bs L hN hFrameL.F0 hFrameL.L0 hFrameL.c hFrameL.πSU
      hFrameL.ρ :=
    ⟨hFrameL.hcardF0, hFrameL.hc_surj, hFrameL.hc_ker, hFrameL.hc_two, hFrameL.hπ_surj,
      hFrameL.hπ_ker, hFrameL.hdiag, hFrameL.hρ_induced⟩
  obtain ⟨ΘT, hnormT, hindT⟩ := qTwoLMDivF_fullT_psuFull hG hBs hN hm h3
    (qTwoLMSkel_div_link hBs hN h3 hFrameL rfl) hU hk
  exact ⟨{ permV := qTwoLMDivF_permQHom hFrameL.m
           permVT := qTwoLMDivF_permHHom hFrameL.m h3
           theta := Θ
           norm_perm := hnorm
           perm_ind := hind
           thetaT := ΘT
           normT := hnormT
           indT := hindT },
    qTwoLMDivF_isQmModel hFrameL.m, qTwoLMDivF_isHmModel hFrameL.m h3⟩

end CFSG.StandardType.QTwo

end
