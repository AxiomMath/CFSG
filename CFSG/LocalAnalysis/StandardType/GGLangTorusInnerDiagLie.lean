module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusLieAlt
public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagE6
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeAction

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.GroupActions
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_exists_f)

theorem langTorus_connectedModelAction
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : LangSetup τ L 5) (b : Fin τ.rank → Lˣ)
    (hb : rootDiagUnit τ b ∈ S.D.torus) (hap : ∀ j, b j ^ p = 1)
    (h1 : rootDiagUnit τ b ≠ 1) (E X : Subgroup (ModGL τ L))
    (hE : E ≤ S.D.model) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hconn : E ≤ familyGroup (fun _ : Unit => b))
    (hX : CFSG.Assembly.IsComponentOf X
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ b})) :
    GGE0Concl E X := by
  classical
  have hτne : τ ≠ .G2 := by
    rintro rfl
    rcases hτ with h | h | h <;> exact absurd h (by decide)
  have hdisj : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    Or.inr (Or.inr (Or.inr hτ))
  have hpL : (p : L) ≠ 0 := by
    refine natCast_ne_zero_of_ringChar_ne hp ?_
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  obtain ⟨i, hQS, hXeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S hτne hp hpL hb hap h1 (CFSG.Assembly.isComponentOf_iff_open.mp hX)
  rw [hXeq]
  set R : Subgroup (ModGL τ L) := rationalComponent S.ρ S.Γ (rootCharHom b) i with hR
  have hRle : R ≤ S.D.model :=
    (Subgroup.commutator_le_self _).trans (inf_le_right.trans
      (Subgroup.commutator_le_self S.D.model))
  let G := ↥S.D.model
  haveI : Finite G := S.finite
  let J : Subgroup G := R.subgroupOf S.D.model
  let E' : Subgroup G := E.subgroupOf S.D.model
  have hJmap : J.map S.D.model.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRle
  let eJ : ↥J ≃* ↥R :=
    (Subgroup.equivMapOfInjective J S.D.model.subtype S.D.model.subtype_injective).trans
      (MulEquiv.subgroupCongr hJmap)
  have heJcoe : ∀ y : ↥J, ((eJ y : ↥R) : ModGL τ L) = ((y : G) : ModGL τ L) :=
    fun _ => rfl
  have hQSJ : CFSG.IsQuasisimple ↥J := (CFSG.IsQuasisimple.congr eJ).2 hQS
  have hJq_open : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).2 hQSJ
  have hdvdZ : 2 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.two_dvd_card_of_simple_nonabelian
      hQSJ.2.1 hQSJ.2.2
  have hdvd : 2 ∣ Nat.card ↥J := hdvdZ.trans (Subgroup.card_quotient_dvd_card _)
  have hker : familyKernel (fun _ : Unit => b) = rootCharKernel b := by
    ext α
    simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  have hE_Nmod : E ≤ Subgroup.normalizer (R : Set (ModGL τ L)) := by
    intro g hg
    have hgZ : g ∈ toralRootGroup τ L b := by
      simpa only [familyGroup, hker, toralRootGroup] using hconn hg
    have h1n := toralRootGroup_le_normalizer_rationalRoots S hb i hgZ
    have h2n : g ∈ Subgroup.normalizer (S.Γ : Set (ModGL τ L)) :=
      Subgroup.normalizer_commutator_ge_right S.D.model S.D.model (hE hg)
    exact shapeAct_mem_normalizer_commutator_self
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨h1n, h2n⟩)
  have hN' : E' ≤ Subgroup.normalizer (J : Set G) :=
    (shapeAct_map_le_normalizer_iff S.D.model.subtype S.D.model.subtype_injective E' J).mp (by
      rwa [Subgroup.map_subgroupOf_eq_of_le hE, hJmap])
  have hS2' : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥J (fun lab _ _ _ _ _ => GGChevStTag lab) := by
    intro _
    obtain ⟨t, n, f, hLM_X, hADE, -⟩ :=
      langComp_lieModel_alternative hτ S hp hp2 hb hap i hQS (y := 1)
        (Subgroup.one_mem _) (map_one _) (by simpa using Subgroup.one_mem _)
    have hLM_J := shapeAct_lieModel_centerQuot_transport eJ hLM_X
    have htne := shapeAct_tag_ne_of_ade hADE
    exact shapeAct_largeEvenMarking_chevSt hQSJ.1.commutator_eq_top hLM_J
      htne.2.1 htne.2.2 htne.1
  have hI' : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E', InnDiagOn 2 (Subgroup.zpowers ε) J := by
    intro _ ε hε
    let εm : ModGL τ L := S.D.model.subtype ε
    have hEmem : εm ∈ E := Subgroup.mem_subgroupOf.mp hε
    have hεZ : εm ∈ toralRootGroup τ L b := by
      simpa only [familyGroup, hker, toralRootGroup] using hconn hEmem
    have hεR : εm ∈ Subgroup.normalizer (R : Set (ModGL τ L)) := hE_Nmod hEmem
    have hεstabR : MulAut.conj εm ∈ subgroupStabAut R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hεR
    have hεstep : S.D.step εm = εm := (S.D.mem_model.mp (hE hEmem)).2
    obtain ⟨t, n, f, hLM_X, hADE, hcaseX⟩ :=
      langComp_lieModel_alternative hτ S hp hp2 hb hap i hQS hεZ hεstep hεstabR
    have h360X := shapeAct_card_ne_360 hLM_X
    have hcenterX := excKernelCompAction_holds S (by norm_num) (by norm_num)
      (p := p) hp hp2 hdisj hb hap
      (rootDiagUnit_pow_eq_one_of_forall hap) h1 (fun h => absurd h hτne) i hQS h360X
      hεZ hεstep hεstabR
    have hN : ε ∈ Subgroup.normalizer (J : Set G) := hN' hε
    have hact : ∀ y : ↥J,
        eJ (subgroupStabRestrict J ⟨MulAut.conj ε,
            Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩ y) =
          subgroupStabRestrict R ⟨MulAut.conj εm, hεstabR⟩ (eJ y) := by
      intro y
      apply Subtype.ext
      rw [heJcoe (subgroupStabRestrict J _ y)]
      simp only [subgroupStabRestrict_apply, MulAut.conj_apply]
      rw [heJcoe y]
      rfl
    have hαβ := shapeAct_congr_subgroupStabRestrict eJ hN hεR hact
    have hLMJ : CFSG.Blueprint.LieModel (PSimple 2 J) t n 2 f :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        (pSimpleEquivCenterQuot Nat.prime_two hQSJ hdvdZ).symm
        (shapeAct_lieModel_centerQuot_transport eJ hLM_X)
    have hmemJ : indAut 2 J ε hN ∈ innAutDerived (PSimple 2 J) :=
      (indAut_mem_innAutDerived_iff_centerQuotientHom Nat.prime_two hJq_open hdvd hN).mpr
        (shapeAct_centerQuot_mem_transport eJ hαβ hcenterX)
    have hcaseJ : ¬ (t = .POmegaPlus ∧ n = 4) ∨
        indAut 2 J ε hN ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 2 J) := by
      rcases hcaseX with hnot | hinn
      · exact Or.inl hnot
      · exact Or.inr
          ((indAut_mem_inner_iff_centerQuotientHom Nat.prime_two hJq_open hdvd hN).mpr
            (shapeAct_centerQuot_mem_inner_transport eJ hαβ hinn))
    exact shapeAct_innDiagOn Nat.prime_two hN hJq_open hdvdZ hLMJ hcaseJ
      (shapeAct_tag_ne_of_ade hADE).1 hmemJ
  have hE'exp : ∀ ε ∈ E', ε ^ p = 1 := by
    intro ε hε
    refine Subtype.ext ?_
    change ((ε : ModGL τ L) ^ p = 1)
    exact hEp (ε : ModGL τ L) (Subgroup.mem_subgroupOf.mp hε)
  have hconcl' : GGE0Concl E' J :=
    ggE0Concl_of_innDiagOn_family hp hp2 hE'exp hN' hS2' hI'
  rw [← Subgroup.map_subgroupOf_eq_of_le hE, ← Subgroup.map_subgroupOf_eq_of_le hRle]
  exact (ggE0Concl_map_iff S.D.model.subtype S.D.model.subtype_injective E' J).mpr hconcl'

theorem langTorus_innerDiagOn_lie
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {d t : Fin τ.rank → Lˣ} (hd : rootDiagUnit τ d ∈ S.D.torus)
    (ht : rootDiagUnit τ t ∈ S.D.torus) (hdp : ∀ j, d j ^ p = 1) (htp : ∀ j, t j ^ p = 1)
    (hd1 : rootDiagUnit τ d ≠ 1) {K : Subgroup (ModGL τ L)}
    (hK : CFSG.Open.IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ d})) :
    GGInnerDiagOn (Subgroup.zpowers (rootDiagUnit τ t)) K := by
  classical
  obtain ⟨f, hf1, hqf⟩ := ssTw_exists_f S (ℓ := 2)
  obtain ⟨S5, hD5, -⟩ :=
    CFSG.StandardType.LieCore.exists_langSetup_of_datum S.D S.ρ S.frob S.finite hf1 hqf
  have hΓ5 : S5.Γ = S.Γ := by
    show S5.D.Γ = S.D.Γ
    rw [hD5]
  have htor5 : S5.D.torus = S.D.torus := by rw [hD5]
  have hmod5 : S5.D.model = S.D.model := by rw [hD5]
  have hE : Subgroup.zpowers (rootDiagUnit τ t) ≤ S5.D.model := by
    rw [Subgroup.zpowers_le, hmod5]
    exact S.D.torus_le_model ht
  have hEp : ∀ e ∈ Subgroup.zpowers (rootDiagUnit τ t), e ^ p = 1 := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      rootDiagUnit_pow_eq_one_of_forall htp, one_zpow]
  have hconn : Subgroup.zpowers (rootDiagUnit τ t) ≤ familyGroup (fun _ : Unit => d) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup t)
  have hX : CFSG.Assembly.IsComponentOf K (S5.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ d}) := by
    rw [hΓ5]
    exact CFSG.Assembly.isComponentOf_iff_open.2 hK
  have hGE := langTorus_connectedModelAction (hτ.elim Or.inl fun h => Or.inr (Or.inr h)) hp hp2
    S5 d (by rw [htor5]; exact hd) hdp hd1 _ K hE hEp hconn hX
  have hpL : (p : L) ≠ 0 := by
    refine natCast_ne_zero_of_ringChar_ne hp ?_
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  have hτne : τ ≠ .G2 := by
    intro h
    rw [h] at hτ
    exact hτ.elim (fun h' => absurd h' (by decide)) (fun h' => absurd h' (by decide))
  obtain ⟨i, hQS, hXeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S5 hτne hp hpL (by rw [htor5]; exact hd) hdp hd1
        (CFSG.Assembly.isComponentOf_iff_open.mp hX)
  obtain ⟨t', n', f', hLM', -, -⟩ :=
    langComp_lieModel_alternative (hτ.elim Or.inl fun h => Or.inr (Or.inr h)) S5 hp hp2
      (by rw [htor5]; exact hd) hdp i hQS
      (y := 1) (Subgroup.one_mem _) (map_one _) (by simpa using Subgroup.one_mem _)
  have hmark : LargeEvenMarking ↥K (fun _ _ _ _ _ _ => True) := by
    rw [hXeq]
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hQS.1) hLM')
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨hGE.1, h.2⟩) (hGE.2 hmark)

end CFSG.StandardType

end
