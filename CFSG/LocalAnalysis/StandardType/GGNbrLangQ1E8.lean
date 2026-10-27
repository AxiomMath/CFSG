module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Steinberg.CentralExt.E8Even
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagLie
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E8Model
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.StandardType.TableBExc.E6Three (hatAut)

theorem q1E8_equiv_of_marking {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K) :
    ∃ e : L ≃* adjointGroup .E8 K,
      ∀ l, e l = TableBExc.recipeEquiv .E8 K (ggQuotHom θ l) := by
  let : Group.IsPerfect L := ⟨hL⟩
  let π : L →* adjointGroup .E8 K :=
    (TableBExc.recipeEquiv .E8 K).toMonoidHom.comp (ggQuotHom θ)
  have hπ : Function.Surjective π :=
    (TableBExc.recipeEquiv .E8 K).surjective.comp (ggQuotHom_surjective θ)
  have hker : π.ker ≤ Subgroup.center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (TableBExc.recipeEquiv .E8 K).injective,
      ker_ggQuotHom θ]
  exact ⟨MulEquiv.ofBijective π
    (CFSG.LieType.Steinberg.CentralExt.e8_even_bijective_of_perfect π hπ hker), fun _ => rfl⟩

theorem q1E8_component_layer_of_equiv
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {C : Type} [Group C] (e : L ≃* C) :
    ∃ (y : Bs) (u : MulAut L),
      (y : G) ∈ D ∧ ggGamma L hN y = u ∧ orderOf u = p ∧
      (∀ b : Bs, Commute (ggGamma L hN b) u) ∧ J ≤ L ∧
      IsComponentOf ((J.subgroupOf L).map e.toMonoidHom)
        (ggAutFixedSubgroup (MulAut.congr e u)) ∧
      (J.subgroupOf L).map e.toMonoidHom =
        LargeEvenLayer (ggAutFixedSubgroup (MulAut.congr e u)) := by
  obtain ⟨y, u, hy, hyu, hu, hc, hJL, hJcomp, hJlayer⟩ :=
    q1_fixed_component_layer_data hcfg hN
  have hfixed : (ggAutFixedSubgroup u).map e.toMonoidHom =
      ggAutFixedSubgroup (MulAut.congr e u) := by
    ext c
    constructor
    · rintro ⟨l, hl, rfl⟩
      change (MulAut.congr e u) (e l) = e l
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        using congrArg e hl
    · intro hc
      change (MulAut.congr e u) c = c at hc
      refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
      change u (e.symm c) = e.symm c
      apply e.injective
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hc
  refine ⟨y, u, hy, hyu, hu, hc, hJL, ?_, ?_⟩
  · rw [← hfixed]
    exact isComponentOf_map_of_injective e.toMonoidHom e.injective
      (CFSG.Assembly.isComponentOf_iff_open.mpr hJcomp)
  · rw [hJlayer, ← largeEvenLayer_map_of_injective e.toMonoidHom e.injective, hfixed]

theorem q1E8_marking_of_equiv {X C : Type} [Group X] [Group C]
    (e : X ≃* C) {A : Subgroup (MulAut X)} {J : Subgroup X}
    {P : LargeEvenLabel → Prop}
    (h : LargeEvenMarking (J.map e.toMonoidHom) (fun lab _ _ I _ θ =>
      P lab ∧ (∀ a ∈ A.map (MulAut.congr e).toMonoidHom,
        ∀ j ∈ J.map e.toMonoidHom, a j ∈ J.map e.toMonoidHom) ∧
          GGAutsInduceOn (A.map (MulAut.congr e).toMonoidHom) (J.map e.toMonoidHom) θ I)) :
    LargeEvenMarking J (fun lab _ _ I _ θ => P lab ∧
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θ I) := by
  let eJ : J ≃* J.map e.toMonoidHom := J.equivMapOfInjective e.toMonoidHom e.injective
  have hcoe : ∀ j : J, ((eJ j : J.map e.toMonoidHom) : C) = e (j : X) :=
    fun j => Subgroup.coe_equivMapOfInjective_apply J e.toMonoidHom e.injective j
  refine largeEvenMarking_congr eJ ?_ h
  intro lab R _ I F θ hθ
  refine ⟨hθ.1, ?_, ?_⟩
  · intro a ha j hj
    have hmem := hθ.2.1 (MulAut.congr e a) (Subgroup.mem_map_of_mem _ ha)
      (e j) (Subgroup.mem_map_of_mem _ hj)
    obtain ⟨j', hj', heq⟩ := hmem
    have heq' : e j' = e (a j) := by
      change e j' = (MulAut.congr e a) (e j) at heq
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using heq
    exact e.injective heq' ▸ hj'
  · intro a ha
    obtain ⟨φ, hφ, hind⟩ := hθ.2.2 (MulAut.congr e a) (Subgroup.mem_map_of_mem _ ha)
    refine ⟨φ, hφ, ?_⟩
    have hrel : ∀ j j' : J, a (j : X) = (j' : X) ↔
        (MulAut.congr e a) ((eJ j : J.map e.toMonoidHom) : C) =
          ((eJ j' : J.map e.toMonoidHom) : C) := by
      intro j j'
      rw [hcoe, hcoe, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact e.injective.eq_iff.symm
    exact (largeEvenInduces_congr_equiv eJ θ _ _ hrel φ).2 hind

theorem q1E8_innerActors_of_marking {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hactors : ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID .E8 K,
      LargeEvenInduces θ (fun l l' : L => (l' : G) = b⁻¹ * l * b) φ)
    (e : L ≃* adjointGroup .E8 K)
    (he : ∀ l, e l = TableBExc.recipeEquiv .E8 K (ggQuotHom θ l)) :
    (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, rfl⟩ := ha
  obtain ⟨φ, hφ, hind⟩ := hactors (b : G)⁻¹ (Bs.inv_mem b.2)
  obtain ⟨z, hz⟩ := TableBExc.idImage_subset_inn_E8 K hφ
  refine ⟨TableBExc.recipeEquiv .E8 K z, ?_⟩
  refine MulEquiv.ext fun c => ?_
  obtain ⟨l, rfl⟩ := e.surjective c
  change MulAut.conj (TableBExc.recipeEquiv .E8 K z) (e l) =
    (MulAut.congr e (ggGamma L hN b)) (e l)
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  have hind' := hind l (ggGamma L hN b l) (by
    change (ggGamma L hN b l : G) = ((b : G)⁻¹)⁻¹ * (l : G) * (b : G)⁻¹
    rw [ggGamma_coe, inv_inv])
  rw [← hz, MulAut.conj_apply] at hind'
  rw [he l, he (ggGamma L hN b l), ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (TableBExc.recipeEquiv .E8 K) hind'

theorem q1E8_innerDiagOn_of_model
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hactors : ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID .E8 K,
      LargeEvenInduces θ (fun l l' : L => (l' : G) = b⁻¹ * l * b) φ)
    (supplier : ∀ {A : Subgroup (MulAut (adjointGroup .E8 K))},
      IsElemAbelian p A →
      A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
      ∀ {u : MulAut (adjointGroup .E8 K)}, u ∈ A → u ≠ 1 →
      ∀ {C : Subgroup (adjointGroup .E8 K)}, IsComponentOf C (ggAutFixedSubgroup u) →
      C = LargeEvenLayer (ggAutFixedSubgroup u) →
      LargeEvenMarking C (fun _ _ _ I _ θC =>
        (∀ a ∈ A, ∀ c ∈ C, a c ∈ C) ∧ GGAutsInduceOn A C θC I)) :
    GGInnerDiagOn Bs J := by
  classical
  obtain ⟨e, he⟩ := q1E8_equiv_of_marking hcfg.data_L.2.2.2 θ
  let A : Subgroup (MulAut L) := (ggGamma L hN).range
  let E : Subgroup (MulAut (adjointGroup .E8 K)) := A.map (MulAut.congr e).toMonoidHom
  have hA : IsElemAbelian p A :=
    isElemAbelian_range
      (fun a b => Subtype.ext (CFSG.StandardType.TableB.IsElemAbelian.comm hcfg.2.1.2.1 a.2 b.2))
      (fun a => Subtype.ext (hcfg.2.1.2.1.2 a a.2)) _
  have hE : IsElemAbelian p E := TableB.isElemAbelian_map hA _
  have hEI : E ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range :=
    q1E8_innerActors_of_marking θ hN hactors e he
  obtain ⟨y, u, hy, hyu, huord, hc, hJL, hJC, hJlayer⟩ :=
    q1E8_component_layer_of_equiv hcfg hN e
  have huA : u ∈ A := ⟨y, hyu⟩
  have huE : MulAut.congr e u ∈ E := Subgroup.mem_map_of_mem _ huA
  have hu1 : MulAut.congr e u ≠ 1 := by
    intro h
    have hu' : u = 1 := by
      refine MulEquiv.ext fun l => e.injective ?_
      have hl := congrArg (fun a : MulAut (adjointGroup .E8 K) => a (e l)) h
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, MulAut.one_apply] using hl
    rw [hu', orderOf_one] at huord
    exact hp.ne_one huord.symm
  have hm := supplier hE hEI huE hu1 hJC hJlayer
  have hm' : LargeEvenMarking ((J.subgroupOf L).map e.toMonoidHom)
      (fun lab _ _ I _ θC => True ∧
        (∀ a ∈ E, ∀ c ∈ (J.subgroupOf L).map e.toMonoidHom,
          a c ∈ (J.subgroupOf L).map e.toMonoidHom) ∧
            GGAutsInduceOn E ((J.subgroupOf L).map e.toMonoidHom) θC I) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hm
  have hconc : Q1ComponentConclusion p ⟨.E8, 0, 1⟩ A (J.subgroupOf L)
      (fun _ _ _ => True) := q1E8_marking_of_equiv e hm'
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub (fun a ha b hb =>
      CFSG.StandardType.TableB.IsElemAbelian.comm hcfg.2.1.2.1 ha hb)
      hcfg.2.1.1 hcfg.2.2.1 hN
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2)
    (q1_marking_of_component_conclusion hN hJL hBsJ hconc)

theorem q1E8_marking_of_langAction
    {K : Type} [Field K] [Finite K]
    {A : Subgroup (MulAut (adjointGroup .E8 K))} {L : Type} [Field L]
    (ψ : adjointGroup .E8 K →* ModGL .E8 L) (hψ : Function.Injective ψ)
    (ρ : A →* ModGL .E8 L)
    (hact : ∀ a : A, ∀ c : adjointGroup .E8 K,
      ψ ((a : MulAut (adjointGroup .E8 K)) c) = ρ a * ψ c * (ρ a)⁻¹)
    {J : Subgroup (adjointGroup .E8 K)}
    (hc : GGE0Concl ρ.range (J.map ψ))
    (hm : LargeEvenMarking (J.map ψ) (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking J (fun _ _ _ I _ θ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θ I) := by
  classical
  let eJ : J ≃* J.map ψ := J.equivMapOfInjective ψ hψ
  have hcoe : ∀ j : J, ((eJ j : J.map ψ) : ModGL .E8 L) = ψ (j : adjointGroup .E8 K) :=
    fun j => Subgroup.coe_equivMapOfInjective_apply J ψ hψ j
  refine largeEvenMarking_congr eJ ?_ (hc.2 hm)
  intro lab R _ I F θ hθ
  refine ⟨?_, ?_⟩
  · intro a ha j hj
    have hr : ρ ⟨a, ha⟩ ∈ ρ.range := ⟨⟨a, ha⟩, rfl⟩
    have hm := (Subgroup.mem_normalizer_iff.mp (hc.1 hr) (ψ j)).1
      (Subgroup.mem_map_of_mem ψ hj)
    obtain ⟨j', hj', heq⟩ := hm
    have heq' : ψ j' = ψ (a j) := by
      change ψ j' = ρ ⟨a, ha⟩ * ψ j * (ρ ⟨a, ha⟩)⁻¹ at heq
      exact heq.trans (hact ⟨a, ha⟩ j).symm
    exact hψ heq' ▸ hj'
  · intro a ha
    obtain ⟨φ, hφ, hind⟩ := hθ.2 (ρ ⟨a, ha⟩)⁻¹
      (ρ.range.inv_mem ⟨⟨a, ha⟩, rfl⟩)
    refine ⟨φ, hφ, ?_⟩
    have hrel : ∀ j j' : J, a (j : adjointGroup .E8 K) = (j' : adjointGroup .E8 K) ↔
        ((eJ j' : J.map ψ) : ModGL .E8 L) =
          ((ρ ⟨a, ha⟩)⁻¹)⁻¹ * ((eJ j : J.map ψ) : ModGL .E8 L) * (ρ ⟨a, ha⟩)⁻¹ := by
      intro j j'
      rw [hcoe, hcoe, inv_inv, ← hact]
      exact hψ.eq_iff.symm.trans eq_comm
    exact (largeEvenInduces_congr_equiv eJ θ _ _ hrel φ).2 hind

theorem q1E8_marking_of_componentLabel {G : Type} [Group G] {J : Subgroup G}
    (hJ : CFSG.IsQuasisimple J) {lab : LargeEvenLabel}
    (hlabel : TableCRes.GGCompLabelAt lab J) :
    LargeEvenMarking J (fun lab' _ _ _ _ _ => lab' = lab) := by
  obtain ⟨hΛ, -, hhas, -⟩ := hlabel
  refine ⟨hJ.1.commutator_eq_top, lab, hΛ, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F he => ?_) hhas
  obtain ⟨θ⟩ := he
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2.1
  have : IsSimpleGroup R := θ.symm.isSimpleGroup
  have hnonab : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJ.2.2
    refine ⟨θ a, θ b, ?_⟩
    intro h
    apply hab
    apply θ.injective
    simpa only [map_mul] using h
  exact ⟨inferInstance, hnonab, θ, rfl⟩

theorem q1E8_marking_of_component_field {G : Type} [Group G] {J : Subgroup G}
    (hJ : CFSG.IsQuasisimple J) {q : ℕ}
    (hfield : GGCompFieldAt q J) :
    LargeEvenMarking J (fun _ _ _ _ _ _ => True) := by
  obtain ⟨lab, hΛ, hc, hq, hvalid, hchar, htag, hhas, R, hRinst, hM, hθ⟩ := hfield
  have hlabel : TableCRes.GGCompLabelAt lab J := ⟨hΛ, hc, hhas, R, hRinst, hM, hθ⟩
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
    (q1E8_marking_of_componentLabel hJ hlabel)

theorem q1E8_marking_of_actual_lang_component
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (adjointGroup .E8 K))} {u : MulAut (adjointGroup .E8 K)}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup .E8 (AlgebraicClosure K) 5)
    (d : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ψ : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K)) (hψ : Function.Injective ψ)
    (ρ : A →* ModGL .E8 (AlgebraicClosure K))
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d ∈ S.D.torus)
    (hdp : ∀ j, d j ^ p = 1)
    (hfixmap : (ggAutFixedSubgroup u).map ψ = S.Γ ⊓ Subgroup.centralizer
      {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d})
    (hact : ∀ a : A, ∀ c : adjointGroup .E8 K,
      ψ ((a : MulAut (adjointGroup .E8 K)) c) = ρ a * ψ c * (ρ a)⁻¹)
    {J : Subgroup (adjointGroup .E8 K)} (hJ : IsComponentOf J (ggAutFixedSubgroup u))
    (hc : GGE0Concl ρ.range (J.map ψ)) :
    LargeEvenMarking J (fun _ _ _ I _ θ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θ I) := by
  classical
  let : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmap : IsComponentOf (J.map ψ) (S.Γ ⊓ Subgroup.centralizer
      {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d}) := by
    have hm := isComponentOf_map_of_injective ψ hψ hJ
    rwa [hfixmap] at hm
  have hmapO : CFSG.Open.IsComponentOf (J.map ψ) (S.Γ ⊓ Subgroup.centralizer
      {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hmap
  obtain ⟨i, -, hfield⟩ := TableCRes.langFamilyCompFieldSL_holds .E8 (AlgebraicClosure K) 5 p S
    (Or.inr (Or.inr rfl)) hp hp2 PUnit.{1} (fun _ => d) (fun _ => hT)
    (fun _ j => hdp j) (J.map ψ) (by
      have hr : (Set.range fun _ : PUnit.{1} =>
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d) =
        {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E8 d} := Set.range_const
      rw [hr]
      exact hmapO)
  have hq : CFSG.IsQuasisimple (J.map ψ) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native (J.map ψ)).1 hmap.2.2
  exact q1E8_marking_of_langAction ψ hψ ρ hact hc
    (q1E8_marking_of_component_field hq hfield.toAt)

theorem q1E8_model_marking_holds {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (adjointGroup .E8 K))} (hA : IsElemAbelian p A)
    (hAI : A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range)
    {u : MulAut (adjointGroup .E8 K)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (adjointGroup .E8 K)} (hJ : IsComponentOf J (ggAutFixedSubgroup u)) :
    LargeEvenMarking J (fun _ _ _ I _ θ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θ I) := by
  have hAI' : A ≤ (hatAut .E8 K).range := by
    rw [Q1E8Model.hatAut_E8_range_eq_conj]
    exact hAI
  obtain ⟨S, d, ψ, ρ, hq, hΦ, hT, hdp, hd1, hinj, hrange, hρu, hρrange,
    hρp, hact, hfixed, hconcl⟩ :=
    Q1E8Model.q1E8Model_exists_connectedAction hp hp2 hA hAI' hu hu1
  exact q1E8_marking_of_actual_lang_component hp hp2 S d ψ hinj ρ hT hdp hfixed hact hJ
    (hconcl J hJ)

theorem q1E8InnerDiag_holds : GGBstarInnerDiagJInputOn (fun _ lab => lab.tag = .E8) := by
  intro G _ _ p B Bs x L D J hcfg hmark
  classical
  obtain ⟨hL, lab, hΛ, hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, θ, ht, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst t
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  refine q1E8_innerDiagOn_of_model hp hcfg θK hN hactors ?_
  intro A hA hAI u hu hu1 C hJ _
  exact q1E8_model_marking_holds hp hp2 hA hAI hu hu1 hJ

theorem ggBstarInnerDiagJInput_of_not_e6Three_twE6Three_e8
    (hrest : GGBstarInnerDiagJInputOn
      (fun p lab => ¬ E6Three p lab ∧ ¬ TwE6Three p lab ∧ lab.tag ≠ .E8)) :
    GGBstarInnerDiagJInput := by
  classical
  apply ggBstarInnerDiagJInput_of_not_e6Three_twE6Three
  intro G _ _ p B Bs x L D J hcfg hmark
  have hboth := q1On_or hrest q1E8InnerDiag_holds
  apply hboth G p B Bs x L D J hcfg
  exact largeEvenMarking_mono (fun lab _ _ _ _ _ h =>
    ⟨by
      by_cases ht : lab.tag = .E8
      · exact Or.inr ht
      · exact Or.inl ⟨h.1.1, h.1.2, ht⟩,
      h.2⟩) hmark

end CFSG.StandardType
