module

public import CFSG.RankThree.GF2n.Tim79aClassicalSU
public import CFSG.Timmesfeld.Transvection.ModelSUIrr
public import CFSG.Timmesfeld.Transvection.ModelSUCore
public import CFSG.RankThree.GF2n.Tim79aSURootS2
public import CFSG.RankThree.GF2n.Tim79aSURootInner

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open

theorem exists_suFacts {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 4 ≤ m) {a : Fin m → F} (ha : a ≠ 0)
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T) :
    ∃ d : Fin m → F, uForm (unitaryInvolution F 2 f) d d = 0 ∧
      uForm (unitaryInvolution F 2 f) a d = 1 ∧
      SUThetaFacts (unitaryInvolution F 2 f) a d T ∧ SUGeomFacts (unitaryInvolution F 2 f) a d := by
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  have hnorm : ∀ c, unitaryInvolution F 2 f c = c → ∃ l, unitaryInvolution F 2 f l * l = c :=
    fun c hc => exists_sigma_mul_self_eq hF hc
  obtain ⟨d, hdd, had⟩ := exists_isotropic_partner hσ htr ha haa
  exact ⟨d, hdd, had, suThetaFacts_holds hσ htr haa hdd had hT,
    suGeomFacts_holds hσ htr hnorm hm haa hdd had⟩

theorem suCoreStatement_holds : SUCoreStatement := by
  intro m F _ _ _ f hF hm a T ha haa hT
  obtain ⟨d, hdd, had, Θ, G⟩ := exists_suFacts hF hm ha haa hT
  exact pCoreOf_normalizer_eq_uRad (unitaryInvolution_involutive hF) ha hT Θ G

theorem suIrrStatement_holds : SUIrrStatement := by
  intro m F _ _ _ f hF hm a T ha haa hT R hTR hRU hRn
  obtain ⟨d, hdd, had, Θ, G⟩ := exists_suFacts hF hm ha haa hT
  exact eq_or_eq_uRad_of_normalized (unitaryInvolution_involutive hF) haa hdd had Θ G
    (suTorusStmt_holds (unitaryInvolution_involutive hF)) hTR hRU hRn

theorem suModelS2_holds : SUModelS2 := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had, Θ, G⟩ := exists_suFacts hF hm ha haa hT
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  have hnormK : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
    fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk
  have hcore := pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnormK
    (suCoreStatement_holds m F f hF hm a T ha haa hT)
  exact rootS2Model_su hσ htr hΦ hker hT haa hdd had Θ G
    (suModelS1_holds m F f hF hm K Φ hΦ hker a T ha haa hT) hcore

theorem suModelInner_holds : SUModelInner := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had, Θ, G⟩ := exists_suFacts hF hm ha haa hT
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  have hnormK : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
    fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk
  have hcore := pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnormK
    (suCoreStatement_holds m F f hF hm a T ha haa hT)
  exact rootInnerModel_su_of_s2 hσ hker hT haa had Θ G hcore
    (suModelS2_holds m F f hF hm K Φ hΦ hker a T ha haa hT)

theorem classicalRootIrrStatement_holds : ClassicalRootIrrStatement :=
  classicalRootIrrStatement_of_su_statements suCoreStatement_holds suIrrStatement_holds

theorem classicalRootS2Statement_holds : ClassicalRootS2Statement :=
  classicalRootS2Statement_of_suModel suModelS2_holds

end CFSG.RankThree.GF2n.Tim79a
