module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeBruhat
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeLang
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeActionAux
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.AlgebraicGroups
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

theorem connected_model_action
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup .E6 L 5) (b : Fin Tag.E6.rank → Lˣ)
    (hb : rootDiagUnit .E6 b ∈ S.D.torus) (h3 : ∀ j, b j ^ 3 = 1)
    (h1 : rootDiagUnit .E6 b ≠ 1) (E X : Subgroup (ModGL .E6 L))
    (hE : E ≤ S.D.model) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hconn : E ≤ familyGroup (fun _ : Unit => b))
    (hX : CFSG.Assembly.IsComponentOf X
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b})) :
    GGE0Concl E X := by
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h
    norm_num at h2
  obtain ⟨i, hQS, hXeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S (by decide) Nat.prime_three hpL hb h3 h1 (CFSG.Assembly.isComponentOf_iff_open.mp hX)
  rw [hXeq]
  set R : Subgroup (ModGL .E6 L) := rationalComponent S.ρ S.Γ (rootCharHom b) i with hR
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
  have heJcoe : ∀ y : ↥J, ((eJ y : ↥R) : ModGL .E6 L) = ((y : G) : ModGL .E6 L) :=
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
  have hE_Nmod : E ≤ Subgroup.normalizer (R : Set (ModGL .E6 L)) := by
    intro g hg
    have hgZ : g ∈ toralRootGroup .E6 L b := by
      simpa only [familyGroup, hker, toralRootGroup] using hconn hg
    have h1n := toralRootGroup_le_normalizer_rationalRoots S hb i hgZ
    have h2n : g ∈ Subgroup.normalizer (S.Γ : Set (ModGL .E6 L)) :=
      Subgroup.normalizer_commutator_ge_right S.D.model S.D.model (hE hg)
    exact shapeAct_mem_normalizer_commutator_self
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨h1n, h2n⟩)
  have hN' : E' ≤ Subgroup.normalizer (J : Set G) :=
    (shapeAct_map_le_normalizer_iff S.D.model.subtype S.D.model.subtype_injective E' J).mp (by
      rwa [Subgroup.map_subgroupOf_eq_of_le hE, hJmap])
  have hS2' : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥J (fun lab _ _ _ _ _ => GGChevStTag lab) := by
    intro _
    obtain ⟨t, n, f, ht, hLM_X⟩ :=
      tagLie_rationalComponent_E6 S Nat.prime_three hb h3 h1 i hQS
    rw [show ringChar L = 2 from ringChar.eq L 2] at hLM_X
    have htne := shapeAct_tag_ne_of_ade ht
    have hLM_J := shapeAct_lieModel_centerQuot_transport eJ hLM_X
    exact shapeAct_largeEvenMarking_chevSt hQSJ.1.commutator_eq_top hLM_J htne.2.1 htne.2.2 htne.1
  have hI' : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E', InnDiagOn 2 (Subgroup.zpowers ε) J := by
    intro _ ε hε
    let εm : ModGL .E6 L := S.D.model.subtype ε
    have hEmem : εm ∈ E := Subgroup.mem_subgroupOf.mp hε
    have hεZ : εm ∈ toralRootGroup .E6 L b := by
      simpa only [familyGroup, hker, toralRootGroup] using hconn hEmem
    have hεR : εm ∈ Subgroup.normalizer (R : Set (ModGL .E6 L)) := hE_Nmod hEmem
    have hεstabR : MulAut.conj εm ∈ subgroupStabAut R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hεR
    have hεstep : S.D.step εm = εm := (S.D.mem_model.mp (hE hEmem)).2
    obtain ⟨t, n, f, hLM_X, htitsX, hszX, hcaseX⟩ :=
      e6_lieModel_alternative innerD4FixedPointsPerfect_holds S hb h3 h1 i hQS hεZ hεstep hεstabR
    have h360X := shapeAct_card_ne_360 hLM_X
    have hcenterX := excKernelCompAction_holds S (by norm_num) (by norm_num)
      (p := 3) (by norm_num) (by norm_num)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hb h3
      (rootDiagUnit_pow_eq_one_of_forall h3) h1 (fun h => by cases h) i hQS h360X
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
    exact shapeAct_innDiagOn Nat.prime_two hN hJq_open hdvdZ hLMJ hcaseJ htitsX hmemJ
  have hE'exp : ∀ ε ∈ E', ε ^ 3 = 1 := by
    intro ε hε
    refine Subtype.ext ?_
    change ((ε : ModGL .E6 L) ^ 3 = 1)
    exact hE3 (ε : ModGL .E6 L) (Subgroup.mem_subgroupOf.mp hε)
  have hconcl' : GGE0Concl E' J :=
    ggE0Concl_of_innDiagOn_family Nat.prime_three (by decide) hE'exp hN' hS2' hI'
  rw [← Subgroup.map_subgroupOf_eq_of_le hE, ← Subgroup.map_subgroupOf_eq_of_le hRle]
  exact (ggE0Concl_map_iff S.D.model.subtype S.D.model.subtype_injective E' J).mpr hconcl'

theorem shape_action
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (S : LangSetup .E6 L 5) (β : ModGL .E6 L) (E X : Subgroup (ModGL .E6 L))
    (hβ : β ∈ S.D.model) (hE : E ≤ S.D.model) (hpair : RigidPair β E)
    (hX : CFSG.Assembly.IsComponentOf X (S.Γ ⊓ Subgroup.centralizer {β})) :
    GGE0Concl E X := by
  classical
  rcases hpair with ⟨hβ1, hβ3, hEC, hrigid⟩
  obtain ⟨S', g, b, hg, hq, hmodel, hΓ, hconjβ, hbtorus, hb3⟩ :=
    lang_setup_centered_at halg S β hβ hβ3
  have hβadj : β ∈ adjointGroup .E6 L := (S.D.mem_model.mp hβ).1
  have hconn : E.map (MulAut.conj g).toMonoidHom ≤ familyGroup (fun _ : Unit => b) :=
    rigid_pair_in_connected halg hβadj ⟨hβ1, hβ3, hEC, hrigid⟩ g hg b hconjβ
  have hE' : E.map (MulAut.conj g).toMonoidHom ≤ S'.D.model := by
    rw [← hmodel]; exact Subgroup.map_mono hE
  have h1' : rootDiagUnit .E6 b ≠ 1 := by
    intro h
    apply hβ1
    have hg1 : g * β * g⁻¹ = 1 := hconjβ.trans h
    calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
      _ = 1 := by rw [hg1]; group
  have hE3mod : ∀ e ∈ E, e ^ 3 = 1 := by
    rcases hrigid with ⟨a, k, hk, ha3, hEk, hcard, hgood⟩
    have hpre : ∀ c ∈ Subgroup.closure (Set.range a), c ^ 3 = 1 := by
      let P : Subgroup (Fin Tag.E6.rank → Lˣ) :=
        { carrier := {c | c ^ 3 = 1}
          mul_mem' := by
            intro x y hx hy
            change (x * y) ^ 3 = 1
            rw [mul_pow x y 3, hx, hy, one_mul]
          one_mem' := by
            change (1 : Fin Tag.E6.rank → Lˣ) ^ 3 = 1
            exact one_pow 3
          inv_mem' := by
            intro x hx
            change (x⁻¹) ^ 3 = 1
            rw [inv_pow, hx, inv_one] }
      have hle : Subgroup.closure (Set.range a) ≤ P := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact funext (ha3 i)
      exact fun c hc => hle hc
    have hcl : ∀ x ∈ Subgroup.closure (Set.range fun i : Fin 2 => rootDiagUnit .E6 (a i)),
        x ^ 3 = 1 := by
      have hcl_eq : Subgroup.closure (Set.range fun i : Fin 2 => rootDiagUnit .E6 (a i)) =
          (Subgroup.closure (Set.range a)).map (rootDiagUnitHom .E6 L) := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨i, rfl⟩
          exact ⟨a i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
        · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
          rintro _ ⟨i, rfl⟩
          exact Subgroup.subset_closure ⟨i, rfl⟩
      rw [hcl_eq]
      rintro x ⟨c, hc, rfl⟩
      rw [← map_pow (rootDiagUnitHom .E6 L), hpre c hc, map_one]
    intro e he
    have hke : k * e * k⁻¹ ∈
        Subgroup.closure (Set.range fun i : Fin 2 => rootDiagUnit .E6 (a i)) := by
      rw [← hEk]; exact Subgroup.mem_map_of_mem _ he
    have h3 : (k * e * k⁻¹) ^ 3 = 1 := hcl _ hke
    calc e ^ 3 = k⁻¹ * (k * e * k⁻¹) ^ 3 * k := by rw [conj_pow]; group
      _ = 1 := by rw [h3]; group
  have hE3' : ∀ e ∈ E.map (MulAut.conj g).toMonoidHom, e ^ 3 = 1 := by
    rintro e ⟨e₀, he₀, rfl⟩
    change (g * e₀ * g⁻¹) ^ 3 = 1
    calc (g * e₀ * g⁻¹) ^ 3 = g * e₀ ^ 3 * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hE3mod e₀ he₀]; group
  have hX' : CFSG.Assembly.IsComponentOf (X.map (MulAut.conj g).toMonoidHom)
      (S'.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b}) := by
    have hmap := isComponentOf_map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective hX
    have hmapinf : (S.Γ ⊓ Subgroup.centralizer {β}).map (MulAut.conj g).toMonoidHom =
        S'.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b} := by
      rw [Subgroup.map_inf S.Γ (Subgroup.centralizer {β}) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective, hΓ,
        CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hconjβ]
    rw [hmapinf] at hmap
    exact hmap
  have hconcl' : GGE0Concl (E.map (MulAut.conj g).toMonoidHom)
      (X.map (MulAut.conj g).toMonoidHom) :=
    connected_model_action S' b hbtorus hb3 h1' _ _ hE' hE3' hconn hX'
  exact (ggE0Concl_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective E X).1 hconcl'

end CFSG.StandardType
