module

public import CFSG.Quasithin.H13.A6S13825g
public import CFSG.Quasithin.H13.A6S13825s
public import CFSG.Quasithin.H13.A6S13825t
public import CFSG.Quasithin.H13.A6S1385b
public import CFSG.Quasithin.H13.A6S13816d
public import CFSG.Quasithin.Background.S1549CStar
public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.Quasithin.EmptyFaithful.SzN19Par
public import CFSG.Quasithin.Background.FLcSL
public import CFSG.Quasithin.EmptyFaithful.S151S8C2C
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.S1549CBasic
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151ZF
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S13813g
public import CFSG.Quasithin.H13.A6S13827a
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.H13.A6.L13825

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem coprime_dvd_card_comap {H : Subgroup G} {M : Type*} [Group M] [Finite M] (φ : ↥H →* M)
    (hker : ∀ x : ↥H, φ x = 1 → (x : G) ∈ pCoreOf 2 H) {P : Subgroup M} {q : ℕ}
    (hq : Nat.Coprime q 2) (hdvd : q ∣ Nat.card ↥((P.comap φ).map H.subtype)) :
    q ∣ Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
  set ψ : ↥(P.comap φ) →* ↥P := (φ.comp (P.comap φ).subtype).codRestrict P (fun x => x.2) with hψ
  refine dvd_card_of_isPGroup_ker ψ (fun y => ?_) hq hdvd
  have hy : φ ((y : ↥(P.comap φ)) : ↥H) = 1 := by
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp y.2)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hker _ hy⟩
  refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
  have := congrArg Subtype.val hk
  simpa using this

end L13825

namespace Setting4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem kst_eq {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G}
    (hXH : X ≤ H) : S.KSt H X = (X.subgroupOf H).map (S1549C.starHom hF) :=
  S1549C.autOn_tilde_eq_map_starHom hF hXH

theorem kst_top {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) :
    S.KSt H H = (S1549C.starHom hF).range := by
  rw [S.kst_eq hF le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

theorem kst_mono {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X Z : Subgroup G}
    (hXZ : X ≤ Z) (hZH : Z ≤ H) : S.KSt H X ≤ S.KSt H Z := by
  rw [S.kst_eq hF (hXZ.trans hZH), S.kst_eq hF hZH]
  exact Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hXZ (Subgroup.mem_subgroupOf.mp hx))

theorem kst_sup {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X Z : Subgroup G}
    (hXH : X ≤ H) (hZH : Z ≤ H) : S.KSt H (X ⊔ Z) = S.KSt H X ⊔ S.KSt H Z := by
  rw [S.kst_eq hF (sup_le hXH hZH), S.kst_eq hF hXH, S.kst_eq hF hZH,
    Subgroup.subgroupOf_sup hXH hZH, Subgroup.map_sup]

theorem kst_le_normalizer {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    {X Z : Subgroup G} (hXH : X ≤ H) (hZH : Z ≤ H) (hZX : Z ≤ Subgroup.normalizer (X : Set G)) :
    S.KSt H Z ≤ Subgroup.normalizer (S.KSt H X : Set _) := by
  rw [S.kst_eq hF hXH, S.kst_eq hF hZH]
  exact L32Case.map_le_normalizer_map hZX _

theorem kst_isPGroup {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G}
    (hXH : X ≤ H) (hX : IsPGroup 2 ↥X) : IsPGroup 2 ↥(S.KSt H X) := by
  rw [S.kst_eq hF hXH]
  exact (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm).map _

theorem kst_isSolvable {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G}
    (hXH : X ≤ H) (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥(S.KSt H X) := by
  rw [S.kst_eq hF hXH]
  have : Group.IsSolvable ↥(X.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXH).toMonoidHom) (MulEquiv.injective _)
  exact Group.isSolvable_of_surjective (f := (S1549C.starHom hF).subgroupMap (X.subgroupOf H))
    (MonoidHom.subgroupMap_surjective _ _)

theorem card_kst_dvd {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G}
    (hXH : X ≤ H) : Nat.card ↥(S.KSt H X) ∣ Nat.card ↥X := by
  rw [hF.card_autOn_tilde hXH]
  exact Subgroup.relIndex_dvd_card _ _

theorem kst_le_iff {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X Z : Subgroup G}
    (hXH : X ≤ H) (hZH : Z ≤ H) :
    S.KSt H X ≤ S.KSt H Z ↔ X ≤ Z ⊔ pCoreOf 2 H := by
  have hker : ∀ x : ↥H, S1549C.starHom hF x = 1 ↔ (x : G) ∈ pCoreOf 2 H :=
    S1549C.starHom_eq_one_iff hF
  have hQH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  rw [S.kst_eq hF hXH, S.kst_eq hF hZH]
  constructor
  · intro h x hx
    obtain ⟨z, hz, hzx⟩ := h ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h1 : S1549C.starHom hF (z⁻¹ * ⟨x, hXH hx⟩) = 1 := by
      rw [map_mul, map_inv, hzx, inv_mul_cancel]
    have h2 := (hker _).1 h1
    have e : x = (z : G) * ((z⁻¹ * ⟨x, hXH hx⟩ : ↥H) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hz) h2
  · rintro h _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ pCoreOf 2 H ⊔ Z := by
      rw [sup_comm]
      exact h (Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨q, hq, z, hz, hqz⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (hZH.trans hQn)).mp hx'
    refine ⟨⟨z, hZH hz⟩, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
    have hq1 : S1549C.starHom hF ⟨q, hQH hq⟩ = 1 := (hker _).2 hq
    have e : x = (⟨q, hQH hq⟩ : ↥H) * ⟨z, hZH hz⟩ := Subtype.ext hqz
    rw [e, map_mul, hq1, one_mul]

theorem isSylowTwoOf_kst {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    (hTH : T ≤ H) (hT : IsSylowTwoOf T H) : IsSylowTwoOf (S.KSt H T) (S.KSt H H) := by
  rw [S.kst_eq hF hTH, S.kst_eq hF le_rfl, Subgroup.subgroupOf_self]
  exact CFSG.Quasithin.S151S8C2.isSylowTwoOf_map' (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) _

theorem kst_O2 {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) :
    ∀ Q : Subgroup _, Q ≤ S.KSt H H → (Q.subgroupOf (S.KSt H H)).Normal → IsPGroup 2 ↥Q →
      Q = ⊥ := by
  rw [S.kst_top hF]
  exact A6Tv.range_o2_eq_bot hF _ (S1549C.starHom_eq_one_iff hF)

end Setting4

namespace L13825

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

open Setting4 in
theorem false_of_pb (h21 : Lem13821) {T L V : Subgroup G} {S : Setting4 G T L V} (hS : S.Hyp138)
    (hno3 : ∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 3 2 1 ↥(S.KSt H' K'))
    {H : Subgroup G} (hH : H ∈ S.Hz)
    {P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
    (hPH : P ≤ S.KSt H H) (hLP : S.KSt H S.L1 ≤ P) (hTP : S.KSt H T ≤ P)
    (hPs : ¬ Group.IsSolvable ↥P) (hPN : ¬ P ≤ Subgroup.normalizer (S.KSt H S.L1 : Set _))
    (h5 : ¬ 5 ∣ Nat.card ↥P) (h27 : ¬ 27 ∣ Nat.card ↥P) : False := by
  have hF := (hS.hF H hH).toHypF91
  set ρ := S1549C.starHom hF with hρ
  have hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := S1549C.starHom_eq_one_iff hF
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  set H₁ := (P.comap ρ).map H.subtype with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.map_subtype_le _
  have hmem : ∀ x : ↥H, (x : G) ∈ H₁ ↔ ρ x ∈ P := fun x => by
    rw [hH₁, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hsub : ∀ {X : Subgroup G}, X ≤ H → S.KSt H X ≤ P → X ≤ H₁ := fun {X} hX hXP x hx =>
    (hmem ⟨x, hX hx⟩).2 (hXP (by
      rw [S.kst_eq hF hX]
      exact ⟨⟨x, hX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩))
  have hL1T : S.L1 ⊔ T ≤ H₁ := sup_le (hsub hL1H hLP) (hsub hTH hTP)
  have hQH₁ : pCoreOf 2 H ≤ H₁ := fun x hx => (hmem ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 H hx⟩).2
    (by rw [(hker _).2 hx]; exact P.one_mem)
  have hO2 : pCoreOf 2 H₁ ≠ ⊥ := by
    intro h0
    apply hH.1.2
    refine le_bot_iff.mp ?_
    rw [← h0]
    exact fun x hx => inf_pCoreOf_le hH₁H ⟨hQH₁ hx, hx⟩
  have hPeq : (P.comap ρ).map ρ = P :=
    Subgroup.map_comap_eq_self ((hPH.trans (S.kst_top hF).le))
  have hc : H₁.subgroupOf H = P.comap ρ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hmem x
  have hM : ¬ H₁ ≤ Subgroup.normalizer (L : Set G) := by
    intro hH₁M
    apply hPN
    have hN1 : H₁ ≤ Subgroup.normalizer (S.L1 : Set G) :=
      A5.le_normalizer_oTwoRes_of_le_normalizer
        (F7.le_normalizer_inf hH₁M ((hH₁H.trans hF.H_normalizes_V₁).trans Subgroup.le_normalizer))
    have h1 := L32Case.map_le_normalizer_map hN1 ρ
    rw [← S.kst_eq hF hL1H, hc, hPeq] at h1
    exact h1
  have hH₁z : H₁ ∈ S.Hz := ⟨⟨hL1T, hO2⟩, hH₁H.trans hH.2.1, hM⟩
  have hns : ¬ Group.IsSolvable ↥H₁ := by
    intro hs
    apply hPs
    rw [← hPeq]
    have : Group.IsSolvable ↥(P.comap ρ) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective (P.comap ρ) H.subtype H.subtype_injective).toMonoidHom)
        (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (f := ρ.subgroupMap (P.comap ρ))
      (MonoidHom.subgroupMap_surjective _ _)
  obtain ⟨K₁, hK₁, -⟩ := exists_cComp_le_of_not_solvable (le_refl H₁)
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hns
  have hF₁ := (hS.hF H₁ hH₁z).toHypF91
  have hdvd : Nat.card ↥(S.KSt H₁ K₁) ∣ Nat.card ↥H₁ :=
    (S.card_kst_dvd hF₁ (le_of_mem_cComp hK₁)).trans
      (Subgroup.card_dvd_of_le (le_of_mem_cComp hK₁))
  have hodd : ∀ q, Nat.Coprime q 2 → q ∣ Nat.card ↥(S.KSt H₁ K₁) → q ∣ Nat.card ↥P :=
    fun q hq h => coprime_dvd_card_comap ρ (fun x hx => (hker x).1 hx) hq (h.trans hdvd)
  rcases (h21 G T L V S hS H₁ hH₁z K₁ hK₁).2.1 with h | h | h | h | h | h
  · exact hno3 H₁ hH₁z K₁ hK₁ h
  · exact h5 (hodd 5 (by norm_num) (by rw [card_of_isPSL_two (by norm_num) h]; decide))
  · exact h5 (hodd 5 (by norm_num) (by rw [card_of_isPSL_two (by norm_num) h]; decide))
  · refine h5 (hodd 5 (by norm_num) ?_)
    rw [card_of_isAlt h, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · refine h5 (hodd 5 (by norm_num) ?_)
    rw [card_of_isAlt h, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · exact h27 (hodd 27 (by norm_num) (by rw [card_of_isPSU33 h]; decide))

end CFSG.Quasithin.H13.A6.L13825
