module

public import CFSG.LocalAnalysis.StandardType.GGTWZK
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6RankDichotomy
public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds

public import CFSG.LocalAnalysis.StandardType.GGDepED4Weyl
public import CFSG.LocalAnalysis.StandardType.GGDepED4Automizer
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelKnownHolds

public import CFSG.LocalAnalysis.StandardType.GGDepED4PrimeJ
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6Three
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel
public import CFSG.LocalAnalysis.StandardType.GGGammaHypsK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.TableB
open CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem GGResHyp.innerDiagOn_J_of_quotient_components_K
    {G : Type} [Group G] [Finite G] {r : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hJK : J ≤ K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hInd : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hcard : 3 ^ r ≤ Nat.card (ggGamma K hN).range)
    (supplier : ∀ {E : Subgroup (MulAut R)}, IsElemAbelian 3 E →
      (∀ a ∈ E, a ∈ I) → 3 ^ r ≤ Nat.card E →
      ∀ {v : MulAut R}, v ∈ E → v ≠ 1 → ∀ {C : Subgroup R},
      IsComponentOf C (ggAutFixedSubgroup v) →
      (∀ a ∈ E, ∀ j ∈ C, a j ∈ C) ∧
        LargeEvenMarking C (fun _ _ _ I' _ θC => GGAutsInduceOn E C θC I')) :
    GGInnerDiagOn Bs J := by
  classical
  let A : Subgroup (MulAut K) := (ggGamma K hN).range
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hH.1.tableB_facts.2.2.1
  let u : MulAut K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hLocal : GGTPNLocalCore 3 A u (J.subgroupOf K) :=
    ggTPNTrLocalCore_holds G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
      (hH.2.2.1.2 y K hH.2.2.2.2.1) hH.2.2.2.2.1 hJK hN hxN
  have hKperf := (hH.2.2.1.2 y K hH.2.2.2.2.1).1
  have hAI : ∀ a ∈ A, ggInducedAut θ a ∈ I := ggInducedInn_of_clause3 hN θ hInd
  obtain ⟨hnorm, hpart⟩ := componentMarking_of_quotient_components hKperf θ
    hLocal.1 hcard hAI hLocal.2.1 hLocal.2.2.1 hLocal.2.2.2.1 supplier
  have hconc : Q1ComponentConclusion 3 ⟨.E6, 0, 1⟩ A (J.subgroupOf K)
      (fun _ _ _ => True) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, hnorm, h⟩) hpart
  have hfinal := q1_marking_of_component_conclusion hN hJK hH.Bs_le_normalizer_J hconc
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hfinal

theorem GGResHyp.cube_le_card_gamma_J_of_card_six
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
  have hBcap := hH.1.2.1.2.2.1
  rw [hcard, hH.1.card_B_eq] at hBcap
  have hm : 5 ≤ LargeEvenTwoLocalRank 3 G := by
    have hpow : 3 ^ 6 ≤ 3 ^ (LargeEvenTwoLocalRank 3 G + 1) := by
      simpa only [pow_succ, mul_comm] using hBcap
    have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (3 : ℕ))).mp hpow
    omega
  exact (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ _ - 2)).trans
    (hH.1.pow_le_card_gamma_J hN)

section Certs


theorem five_le_card_gamma_of_E6_three
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hHas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma K hN).range := by
  have hKi := hH.2.2.1.2 y K hH.2.2.2.2.1
  have hKperf : commutator K = ⊤ := hKi.1
  have hLift := largeEvenLabelAll_torusLift_E6_three htag h3 _ hHas
  obtain ⟨R, _, I, F, ⟨θ⟩, hT⟩ := largeEvenRawDatum_exists hLift
  have hnb := hH.2.2.2.2.1
  have hS : LargeEvenSHat 3 B y K := hnb.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hH.1.2.1.1.trans hN
  have hcA := card_range_ggGamma_mul_of_sHat Nat.prime_three hS hBN
  have h6 := succ_le_twoLocalRank_of_torusLift Nat.prime_three
    hS.2.2.2.1 (hS.1.1.2 y hS.2.1) hS.2.2.1 hKperf θ hT
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma K hBN).range := by
    have hpow : 3 ^ 6 ≤ Nat.card (ggGamma K hBN).range * 3 := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right (by norm_num) h6
    norm_num at hpow ⊢
    omega
  exact hr.trans (Subgroup.card_le_of_le (by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hH.1.2.1.1 b.2⟩, rfl⟩))

theorem five_le_card_gamma_of_twE6_three_of_card_six
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hHas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .twE6) (h3 : 3 ∣ 2 ^ lab.n + 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma K hN).range := by
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hHas
  have hmark' := largeEvenMarking_and_labelAll
    (S := fun l => l = lab)
    (P' := fun R _ _ _ => IsSimpleGroup R → GGTwE6LocalRank R)
    (fun l hlab heq => by
      subst l
      exact TwE6Delta.labelAll htag fun F _ _ hF hsimple =>
        ggTwE6LocalRankInput_holds lab.n hΛ.1 h3 F hF hsimple)
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨hKperf, l, hl, hraw⟩ := hmark'
  obtain ⟨R, _, I, F, hs, hna, θ, hP, hLR⟩ := largeEvenRawDatum_exists hraw
  have hcyc : ∀ E : Subgroup K, E ≤ Subgroup.center K → IsElemAbelian 3 E →
      Nat.card E ≤ 3 :=
    fun E hE hEa => ggLabelCenterPCyclicInput_holds 3 Nat.prime_three (by decide)
      lab hΛ K hKperf hHas E hE hEa
  rcases ggNbr_rank_dichotomy_twE6 hH.1 hH.2.2.2.2.1 hKperf θ
      (hLR hs) hcyc hN with h5 | ⟨hBBs, hBs5, hm, h4, hC⟩
  · exact h5
  · rw [hcard] at hBs5
    norm_num at hBs5

theorem GGResHyp.innerDiagOn_J_of_E6_three
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hJK : J ≤ K)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hHas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1) : GGInnerDiagOn Bs J := by
  classical
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hHas
  obtain ⟨hKperf, l, hl, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hs, hna, θ0, heq, hN0, hInd0⟩ := largeEvenRawDatum_exists hraw
  subst l
  obtain ⟨t, rk, n⟩ := lab
  dsimp only at htag h3
  subst t
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFcard, hsF, hnaF, θF, heqF, hN, hInd⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hFcard
  let ε := TableBExc.recipeEquiv .E6 F
  let θ := θF.trans ε
  have hIraw : ∀ (b : G) (hb : b ∈ Bs), ggBeta K θ hN ⟨b, hb⟩ ∈
      (hatAut .E6 F).range := by
    intro b hb
    obtain ⟨φ, hφ, hind⟩ := hInd b⁻¹ (Bs.inv_mem hb)
    have heq : φ = ggLAut K θF ⟨b, hN hb⟩ := by
      ext q
      obtain ⟨z, rfl⟩ := θF.surjective q
      induction z using QuotientGroup.induction_on with
      | H l =>
        rw [ggLAut_apply]
        apply hind l (K.normalizerMonoidHom ⟨b, hN hb⟩ l)
        change b * (l : G) * b⁻¹ = (b⁻¹)⁻¹ * (l : G) * b⁻¹
        rw [inv_inv]
    change ggLAut K (θF.trans ε) ⟨b, hN hb⟩ ∈ _
    rw [NbrLangTypeA.ggLAut_trans θF ε ⟨b, hN hb⟩]
    exact (E6ThreeModel.recipeID_iff_hatAut _).mp (heq ▸ hφ)
  have hI : ∀ b ∈ Bs, ∃ φ ∈ (hatAut .E6 F).range,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    refine ⟨ggLAut K θ ⟨b⁻¹, hN (Bs.inv_mem hb)⟩,
      hIraw b⁻¹ (Bs.inv_mem hb), ?_⟩
    exact largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))
  have h5 := five_le_card_gamma_of_E6_three hH hΛ hHas rfl h3 hN
  refine hH.innerDiagOn_J_of_quotient_components_K hJK hN θ hI h5 ?_
  intro E hE hEI hEc v hv hv1 C hC
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact h3
  exact Q1E6ThreeModel.q1E6ThreeModel_holds h3F hE hEI hEc hv hv1 hC

theorem GGResHyp.innerDiagOn_J_of_twE6_three_of_card_six
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6) (hJK : J ≤ K)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hHas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .twE6) (h3 : 3 ∣ 2 ^ lab.n + 1) : GGInnerDiagOn Bs J := by
  classical
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hHas
  obtain ⟨hKperf, l, hl, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hs, hna, θ0, heq, hN0, hInd0⟩ := largeEvenRawDatum_exists hraw
  subst l
  obtain ⟨t, rk, n⟩ := lab
  dsimp only at htag h3
  subst t
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFcard, hsF, hnaF, θF, heqF, hN, hInd⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hn : 1 ≤ n := hΛ.1
  have : CharP F 2 := charP_two_of_card (m := n * 2) (by rw [hFcard, pow_mul])
  let σ : F ≃+* F := iterateFrobeniusEquiv F 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def _ 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hFcard σ hσ
  let e : TwE6Delta.RecipeR F n ≃* twistedE6RootGroup F σ := ε.symm
  let θ := θF.trans e
  have hI : ∀ b ∈ Bs, ∃ φ ∈ twistedE6Inn F σ ⊔ twistedE6Diag F σ,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    obtain ⟨φ, hφ, hind⟩ := hInd b hb
    have hφe : MulAut.congr e φ ∈ (RecipeExcLang.twConj F σ).range := by
      apply (hε (MulAut.congr e φ)).1
      change MulAut.congr ε (MulAut.congr ε.symm φ) ∈ TwE6Delta.RecipeI F n
      have hinv : MulAut.congr ε (MulAut.congr ε.symm φ) = φ := by
        ext z
        change ε (ε.symm (φ (ε (ε.symm z)))) = φ z
        simp only [MulEquiv.apply_symm_apply]
      rw [hinv]
      exact hφ
    have hφinner : MulAut.congr e φ ∈ twistedE6Inn F σ ⊔ twistedE6Diag F σ := by
      obtain ⟨w, hw⟩ := hφe
      rw [← range_twistedE6InndiagConj]
      refine ⟨⟨w.1, NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, ?_⟩
      rw [← hw]
      ext z : 1
      apply Subtype.ext
      rfl
    refine ⟨MulAut.congr e φ, hφinner, ?_⟩
    intro l l' hh
    change ((MulAut.congr e) φ) ((θF.trans e) (QuotientGroup.mk l)) =
      (θF.trans e) (QuotientGroup.mk l')
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
      congrArg e (hind l l' hh)
  have h5 := five_le_card_gamma_of_twE6_three_of_card_six hRig hH hcard hΛ hHas rfl h3 hN
  refine hH.innerDiagOn_J_of_quotient_components_K hJK hN θ hI h5 ?_
  intro E hE hEI hEc v hv hv1 C hC
  exact Q1TwE6ThreeModel.q1TwE6ThreeModel_holds hn hFcard σ hσ h3
    hE hEI hEc hv hv1 hC

theorem GGResHyp.weylOfType_E6_of_card_gamma_five
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hHas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hlabel : GGE6DepLabel lab) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcard : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range) :
    GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer K Bs) := by
  classical
  have hmodel : LargeEvenLabelAll lab (fun R _ I _ => GGE6ThreeModelSCr R I) := by
    rcases hlabel with ⟨htag, h3⟩ | ⟨htag, h3⟩
    · exact LargeEvenLabelAll.mono (fun R _ I F h => h.2)
        (largeEvenLabelAll_e6Div_of htag hΛ h3
          (fun F _ _ n hn hF h3F => E6ThreeModel.e6ThreeModel_holds.1 F n hn hF h3F))
    · exact TwE6Delta.labelAll htag (fun F _ _ hF =>
        E6ThreeModel.e6ThreeModel_holds.2 F lab.n hΛ.1 hF h3)
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hHas
  have hmark' := largeEvenMarking_and_labelAll
    (S := fun l => l = lab) (P' := fun R _ I _ => GGE6ThreeModelSCr R I)
    (fun l hlab heq => by subst l; exact hmodel)
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨hKperf, l, hl, hraw⟩ := hmark'
  obtain ⟨R, _, I, F, hs, hna, θ, hP, hM⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, hN0, hInd⟩ := hP
  obtain ⟨hA, hAI, hthree, hsc⟩ := ggGamma_range_hypsSC_K hH θ hN hInd
  obtain ⟨Φ, T, w, hData⟩ := (hM K (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hKperf (ggGamma K hN).range hA hAI hcard hsc).exists_data
  have hZ := card_inf_center_le_of_hasLabel ggLabelCenterPCyclicInput_holds
    Nat.prime_three (by decide) hH.1.tableB_facts.2.1 hKperf hΛ hHas
  exact ggWeylOfType_of_frame Nat.prime_three (by decide) hH.1.tableB_facts.2.1
    hH.1.2.1.2.2.2 hH.2.2.2.1 hN hZ hData.weylFrame

theorem not_ggResSideDatum_of_E6_three_of_label_D4
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6)
    {labJ labK : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hKΛ : LargeEvenInLambda2 labK) (hKHas : GGHasLabel labK (K ⧸ Subgroup.center K))
    (hKtag : labK.tag = .E6) (h3 : 3 ∣ 2 ^ labK.n - 1)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  have hJK := J_le_K_of_label_D4 hLB hH hJΛ hJtag hJrank hJHas
  have hN := ggInnerDiagOn_le_normalizer (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have h5 := five_le_card_gamma_of_E6_three hH hKΛ hKHas hKtag h3 hN
  obtain ⟨eK, heK⟩ := hH.weylOfType_E6_of_card_gamma_five hRig hKΛ hKHas
    (Or.inl ⟨hKtag, h3⟩) hN h5
  have hJinner := hH.innerDiagOn_J_of_E6_three hRig hJK hKΛ hKHas hKtag h3
  have hN_J := hH.Bs_le_normalizer_J
  have hJ3 := hH.cube_le_card_gamma_J_of_card_six hcard hN_J
  have hupper := card_ggAutomizer_le_of_innerDiagOn_D4 hRig rfl
    hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1 hJinner
    hJΛ hJHas hJtag hJrank hN_J hJ3
  have hlower := sevenTwenty_le_card_ggAutomizer_of_e6_oneNode eK hSide
  omega

theorem not_ggResSideDatum_of_twE6_three_of_label_D4
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6)
    {labJ labK : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hKΛ : LargeEvenInLambda2 labK) (hKHas : GGHasLabel labK (K ⧸ Subgroup.center K))
    (hKtag : labK.tag = .twE6) (h3 : 3 ∣ 2 ^ labK.n + 1)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  have hJK := J_le_K_of_label_D4 hLB hH hJΛ hJtag hJrank hJHas
  have hN := ggInnerDiagOn_le_normalizer (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have h5 := five_le_card_gamma_of_twE6_three_of_card_six hRig hH hcard hKΛ hKHas hKtag h3 hN
  obtain ⟨eK, heK⟩ := hH.weylOfType_E6_of_card_gamma_five hRig hKΛ hKHas
    (Or.inr ⟨hKtag, h3⟩) hN h5
  have hJinner := hH.innerDiagOn_J_of_twE6_three_of_card_six hRig hcard hJK hKΛ hKHas hKtag h3
  have hN_J := hH.Bs_le_normalizer_J
  have hJ3 := hH.cube_le_card_gamma_J_of_card_six hcard hN_J
  have hupper := card_ggAutomizer_le_of_innerDiagOn_D4 hRig rfl
    hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1 hJinner
    hJΛ hJHas hJtag hJrank hN_J hJ3
  have hlower := sevenTwenty_le_card_ggAutomizer_of_e6_oneNode eK hSide
  omega

end Certs

end CFSG.StandardType

end
