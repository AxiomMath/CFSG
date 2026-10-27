module

public import CFSG.RankThree.GF2n.Tim79aClassicalSp
public import CFSG.Timmesfeld.Transvection.ModelSUGen
public import CFSG.Timmesfeld.Transvection.ModelSUGeometry
public import CFSG.RankThree.GF2n.Tim79aRootTransportSU
public import CFSG.RankThree.GF2n.Tim79aSURootS1
public import CFSG.RankThree.GF2n.Tim79aSURootS1Quotient
public import CFSG.RankThree.GF2n.Tim79aSURootIrr
public import CFSG.RankThree.GF2n.Tim79aSUOpen

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem suModelS1_holds : SUModelS1 := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ d, d + unitaryInvolution F 2 f d = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  have hG : SUGenStmt F f m := fun {L} h => eq_top_of_forall_isUTransGroup_le hF hm h
  have hP : SUPartnerStmt (unitaryInvolution F 2 f) m :=
    fun ha haa => exists_isotropic_partner hσ htr ha haa
  have hB : SUBothStmt (unitaryInvolution F 2 f) m :=
    fun ha hu haa huu => exists_isotropic_both hσ htr ha hu haa huu
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  exact rootS1Model_su hF hPerp hΦ hker ha haa hT
    (fun {_} hg {_} hx hx1 => uRad_sup_zpowers_eq_top hF hG hP hB ha haa hT hg hx hx1)

theorem classicalRootSUS1Statement_holds : ClassicalRootSUS1Statement :=
  classicalRootSUS1Statement_of_model suModelS1_holds

theorem classicalRootS1Statement_holds : ClassicalRootS1Statement :=
  classicalRootS1Statement_of_sp_su classicalRootSpS1Statement_holds
    classicalRootSUS1Statement_holds

theorem suModelIrr_of_statements (hC : SUCoreStatement) (hI : SUIrrStatement) : SUModelIrr := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ d, d + unitaryInvolution F 2 f d = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  exact rootIrrModel_su hF hΦ hker ha haa hT
    (fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk)
    (hC m F f hF hm a T ha haa hT) (hI m F f hF hm a T ha haa hT)

theorem classicalRootIrrStatement_of_su_statements (hC : SUCoreStatement) (hI : SUIrrStatement) :
    ClassicalRootIrrStatement :=
  classicalRootIrrStatement_of_sp_su classicalRootSpIrrStatement_holds
    (classicalRootSUIrrStatement_of_model (suModelIrr_of_statements hC hI))

theorem classicalRootInnerStatement_of_suModel (h : SUModelInner) :
    ClassicalRootInnerStatement :=
  classicalRootInnerStatement_of_sp_su classicalRootSpInnerStatement_holds
    (classicalRootSUInnerStatement_of_model h)

theorem classicalRootS2Statement_of_suModel (h : SUModelS2) : ClassicalRootS2Statement :=
  classicalRootS2Statement_of_sp_su classicalRootSpS2Statement_holds
    (classicalRootSUS2Statement_of_model h)

end CFSG.RankThree.GF2n.Tim79a
