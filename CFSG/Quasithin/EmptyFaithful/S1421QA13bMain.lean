module

public import CFSG.Quasithin.EmptyFaithful.S1421QA13bHyp
public import CFSG.Quasithin.H13.A5S136r
public import CFSG.Quasithin.EmptyFaithful.S1421STDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem false_of_hypF918_L34
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    {T V L V₁ Vp H K : Subgroup G} (hF : HypF918 T V L V₁ Vp H K) (hSQ : SQTKGroup ↥H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hL : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := H13.A5.isSimpleGroup_of_isPSL34 hL
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirr := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFe := factElem hF hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by
    rw [H13.L1295B.conjClosure_eq hTK]
  have hqM := hA.qhat_M hD.sylow.1
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF (le_of_mem_cComp hF.K_cComp)]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eI⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS hne
  exact H13.A5.false_of_insp4_L34 hA21 hG2 h42 h45 hD310 ⟨hD, hA.qhat_VT hD.exp, hirr'⟩ hMp hqM
    (hA.qOf_VT hD.exp) (H13.A5.isPSL_of_mulEquiv eI.symm hL)

end Core

end S1421

theorem l34F98Impossible_of_inputs
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) (hD310 : D310) :
    L34F98Impossible := by
  intro G _ _ T M H K1 st cfg hF98
  have hU := S1421.isMulCommutative_uOfL22_of_hypF98 hF98
  have hL : IsPSL 3 2 2 (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) :=
    H13.A5.isPSL_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥(oTwoUpper H))) cfg.psl
  have hF := S1421.hypF918_of_cfg st hU cfg.cComp_mem (H13.A5.isQuasisimple_of_isPSL34 hL)
  exact S1421.false_of_hypF918_L34 hA21 hG2 h42 h45 hD310 hF (S1421.sqtkGroup_of_inH st)
    (S1421.le_normalizer_oTwoUpper_of_setting st) hL

end CFSG.Quasithin
