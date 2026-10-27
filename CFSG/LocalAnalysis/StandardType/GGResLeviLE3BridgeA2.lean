module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSwap
public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwo
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdPair
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nBL_isTree {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) :
    (TauCeti.diagramGraph C).IsTree := by
  classical
  have hadj := l05nBL_graph_adj (M := M) (C := C) hW hC
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nBL_weylFixed hW) hC
  have hpre : (TauCeti.diagramGraph C).Preconnected := by
    intro i j
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact l05nBL_rtg_mono (fun u v huv => (hadj u v).2 huv) (ggRC_weyl_connected hW i j)
  have hconn : (TauCeti.diagramGraph C).Connected :=
    (SimpleGraph.connected_iff _).2 ⟨hpre, l05nBL_nonempty hW⟩
  exact TauCeti.IsFiniteType.isTree_diagramGraph hFT hconn

theorem l05nBL_rtg_map {α β : Type} {r : α → α → Prop} {p : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → p (f a) (f b)) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem l05nBL_reach_J {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) (a : Λa) {i j : Jn}
    (h : Relation.ReflTransGen (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j) :
    ((TauCeti.diagramGraph C).induce ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))).Reachable
      ⟨Sum.inl i, by simp⟩ ⟨Sum.inl j, by simp⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  refine l05nBL_rtg_map
    (fun u : Jn => (⟨Sum.inl u, by simp⟩ :
      {x : Jn ⊕ Λa // x ∈ ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))})) ?_ h
  intro u v huv
  rw [SimpleGraph.induce_adj]
  exact (l05nBL_graph_adj (M := M) (C := C) hW hC (Sum.inl u) (Sum.inl v)).2
    ⟨fun h => huv.1 (Sum.inl.inj h), huv.2⟩

theorem l05nBL_J_unique {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (a : Λa) (j j' : Jn) (hj : M.M (Sum.inr a) (Sum.inl j) ≠ 2)
    (hj' : M.M (Sum.inr a) (Sum.inl j') ≠ 2) : j = j' := by
  classical
  have htree := l05nBL_isTree (M := M) (C := C) hW hC
  have hadj := l05nBL_graph_adj (M := M) (C := C) hW hC
  have hnb1 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inl j) :=
    (hadj _ _).2 ⟨Sum.inr_ne_inl, hj⟩
  have hnb2 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inl j') :=
    (hadj _ _).2 ⟨Sum.inr_ne_inl, hj'⟩
  let x : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inl j, (SimpleGraph.mem_neighborSet _ _ _).2 hnb1⟩
  let y : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inl j', (SimpleGraph.mem_neighborSet _ _ _).2 hnb2⟩
  have heq : (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) x =
      (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) y := by
    rw [TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply,
      TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply]
    exact SimpleGraph.ConnectedComponent.sound
      (l05nBL_reach_J (M := M) (C := C) hW hC a (hJ j j'))
  have hval : (x : Jn ⊕ Λa) = (y : Jn ⊕ Λa) :=
    congrArg Subtype.val ((TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree
      (Sum.inr a)).injective heq)
  exact Sum.inl.inj hval

theorem l05nBL_attach_unique {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (v0 v1 : Λa) (j0 j1 : Jn)
    (hj0 : M.M (Sum.inr v0) (Sum.inl j0) ≠ 2)
    (hj1 : M.M (Sum.inr v1) (Sum.inl j1) ≠ 2)
    (hpath : Relation.ReflTransGen
      (fun u v : Λa => u ≠ v ∧ M.M (Sum.inr u) (Sum.inr v) ≠ 2) v0 v1) :
    v0 = v1 ∧ j0 = j1 := by
  classical
  have htree := l05nBL_isTree (M := M) (C := C) hW hC
  have hadj := l05nBL_graph_adj (M := M) (C := C) hW hC
  by_cases hv : v0 = v1
  · subst v1
    exact ⟨rfl, l05nBL_J_unique (M := M) (C := C) hW hC hJ v0 j0 j1 hj0 hj1⟩
  · exfalso
    let G := TauCeti.diagramGraph C
    let sAdd : Set (Jn ⊕ Λa) := Set.range (Sum.inr : Λa → Jn ⊕ Λa)
    have hpathH : Relation.ReflTransGen (G.induce sAdd).Adj
        (⟨Sum.inr v0, ⟨v0, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd})
        (⟨Sum.inr v1, ⟨v1, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd}) :=
      l05nBL_rtg_map (fun u : Λa => (⟨Sum.inr u, ⟨u, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd}))
        (fun a b hab => by
          rw [SimpleGraph.induce_adj]
          exact (hadj _ _).2 ⟨fun h => hab.1 (Sum.inr.inj h), hab.2⟩) hpath
    have hreachH : (G.induce sAdd).Reachable
        (⟨Sum.inr v0, ⟨v0, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd})
        (⟨Sum.inr v1, ⟨v1, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd}) :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).2 hpathH
    let Wh : (G.induce sAdd).Walk
        (⟨Sum.inr v0, ⟨v0, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd})
        (⟨Sum.inr v1, ⟨v1, rfl⟩⟩ : {x : Jn ⊕ Λa // x ∈ sAdd}) := Classical.choice hreachH
    let incl : SimpleGraph.Hom (G.induce sAdd) G :=
      { toFun := fun x => (x : Jn ⊕ Λa)
        map_rel' := by intro a b hab; rw [SimpleGraph.induce_adj] at hab; exact hab }
    let Wg : G.Walk (Sum.inr v0) (Sum.inr v1) := SimpleGraph.Walk.map incl Wh
    let Ph : G.Walk (Sum.inr v0) (Sum.inr v1) := Wg.bypass
    have hPh_path : Ph.IsPath := SimpleGraph.Walk.bypass_isPath Wg
    have hWg_supp : ∀ x ∈ Wg.support, x ∈ sAdd := by
      intro x hx
      rw [SimpleGraph.Walk.support_map] at hx
      rcases List.mem_map.1 hx with ⟨y, -, hxy⟩
      rw [← hxy]
      exact y.2
    have hPh_supp : ∀ x ∈ Ph.support, x ∈ sAdd :=
      fun x hx => hWg_supp x (SimpleGraph.Walk.support_bypass_subset Wg hx)
    have hPh_snd_mem : Ph.snd ∈ sAdd :=
      hPh_supp Ph.snd (by
        simpa only [SimpleGraph.Walk.snd] using SimpleGraph.Walk.getVert_mem_support Ph 1)
    have hPh_nonnil : ¬ Ph.Nil := by
      intro hnil
      exact hv (Sum.inr.inj (SimpleGraph.Walk.Nil.eq hnil))
    have hnot_tail : (Sum.inr v0 : Jn ⊕ Λa) ∉ Ph.tail.support := by
      have hcons : SimpleGraph.Walk.cons (SimpleGraph.Walk.adj_snd hPh_nonnil) Ph.tail = Ph :=
        SimpleGraph.Walk.cons_tail_eq Ph hPh_nonnil
      have hpath_cons :
          (SimpleGraph.Walk.cons (SimpleGraph.Walk.adj_snd hPh_nonnil) Ph.tail).IsPath :=
        hcons.symm ▸ hPh_path
      exact ((SimpleGraph.Walk.cons_isPath_iff
        (SimpleGraph.Walk.adj_snd hPh_nonnil) Ph.tail).1 hpath_cons).2
    have hSupp : ∀ x ∈ Ph.tail.support, x ∈ ({Sum.inr v0}ᶜ : Set (Jn ⊕ Λa)) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx0
      exact hnot_tail (hx0 ▸ hx)
    let WT := SimpleGraph.Walk.induce ({Sum.inr v0}ᶜ : Set (Jn ⊕ Λa)) Ph.tail hSupp
    have hv1ne : (Sum.inr v1 : Jn ⊕ Λa) ≠ Sum.inr v0 :=
      fun h => hv (Sum.inr.inj h).symm
    have hedge : (G.induce ({Sum.inr v0}ᶜ : Set (Jn ⊕ Λa))).Adj
        ⟨Sum.inr v1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hv1ne⟩
        ⟨Sum.inl j1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact Sum.inl_ne_inr⟩ := by
      rw [SimpleGraph.induce_adj]
      exact (hadj _ _).2 ⟨Sum.inr_ne_inl, hj1⟩
    have hreach_edge : (G.induce ({Sum.inr v0}ᶜ : Set (Jn ⊕ Λa))).Reachable
        ⟨Sum.inr v1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hv1ne⟩
        ⟨Sum.inl j1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact Sum.inl_ne_inr⟩ :=
      (SimpleGraph.Adj.toWalk hedge).reachable
    have hreach_all : (G.induce ({Sum.inr v0}ᶜ : Set (Jn ⊕ Λa))).Reachable
        ⟨Ph.snd, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (SimpleGraph.Walk.adj_snd hPh_nonnil).ne'⟩
        ⟨Sum.inl j0, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact Sum.inl_ne_inr⟩ :=
      WT.reachable.trans (hreach_edge.trans
        (l05nBL_reach_J (M := M) (C := C) hW hC v0 (hJ j1 j0)))
    let x : ↥(G.neighborSet (Sum.inr v0)) :=
      ⟨Sum.inl j0, (SimpleGraph.mem_neighborSet _ _ _).2
        ((hadj _ _).2 ⟨Sum.inr_ne_inl, hj0⟩)⟩
    let y : ↥(G.neighborSet (Sum.inr v0)) :=
      ⟨Ph.snd, (SimpleGraph.mem_neighborSet _ _ _).2
        (SimpleGraph.Walk.adj_snd hPh_nonnil)⟩
    have heq : (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr v0)) x =
        (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr v0)) y := by
      rw [TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply,
        TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply]
      exact SimpleGraph.ConnectedComponent.sound hreach_all.symm
    have hval : (x : Jn ⊕ Λa) = (y : Jn ⊕ Λa) :=
      congrArg Subtype.val ((TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree
        (Sum.inr v0)).injective heq)
    obtain ⟨a, ha⟩ := hPh_snd_mem
    exact Sum.inl_ne_inr (hval.trans ha.symm)

theorem l05nBL_mu {U : Type} [Group U] {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn]
    [Fintype Λa] [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)}
    {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ} (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn,
      Relation.ReflTransGen (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (c : Jn → U) :
    ∃ μ : Λa → U, (∀ a j, M.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (c j)⁻¹) ∧
      ∀ a a', a ≠ a' → M.M (Sum.inr a) (Sum.inr a') ≠ 2 → μ a = μ a' := by
  classical
  let ea : Λa → Λa → Prop := fun u v => u ≠ v ∧ M.M (Sum.inr u) (Sum.inr v) ≠ 2
  have hea_symm : ∀ u v, ea u v → ea v u := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [M.symmetric]
    exact h.2
  have hsymm : ∀ {b c : Λa}, Relation.ReflTransGen ea b c → Relation.ReflTransGen ea c b := by
    intro b c hbc
    induction hbc with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hcd ih => exact Relation.ReflTransGen.head (hea_symm _ _ hcd) ih
  have hattach : ∀ (v0 v1 : Λa) (j0 j1 : Jn),
      M.M (Sum.inr v0) (Sum.inl j0) ≠ 2 → M.M (Sum.inr v1) (Sum.inl j1) ≠ 2 →
      Relation.ReflTransGen ea v0 v1 → v0 = v1 ∧ j0 = j1 :=
    fun v0 v1 j0 j1 hj0 hj1 hp =>
      l05nBL_attach_unique (M := M) (C := C) hW hC hJ v0 v1 j0 j1 hj0 hj1 hp
  have hP_unique : ∀ (a : Λa) (p q : Λa × Jn),
      Relation.ReflTransGen ea a p.1 → M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2 →
      Relation.ReflTransGen ea a q.1 → M.M (Sum.inr q.1) (Sum.inl q.2) ≠ 2 →
      p.2 = q.2 := by
    intro a p q hp hjp hq hjq
    exact (hattach p.1 q.1 p.2 q.2 hjp hjq
      ((hsymm hp).trans hq)).2
  let P : Λa → Prop := fun a => ∃ p : Λa × Jn,
    Relation.ReflTransGen ea a p.1 ∧ M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2
  let mu : Λa → U := fun a => if h : P a then (c (Classical.choose h).2)⁻¹ else 1
  refine ⟨mu, ?_, ?_⟩
  · intro a j hj
    have hPa : P a := ⟨(a, j), Relation.ReflTransGen.refl, hj⟩
    have hmu : mu a = (c (Classical.choose hPa).2)⁻¹ := by
      dsimp only [mu]
      exact dif_pos hPa
    rw [hmu,
      hP_unique a (Classical.choose hPa) (a, j) (Classical.choose_spec hPa).1
        (Classical.choose_spec hPa).2 Relation.ReflTransGen.refl hj]
  · intro a a' haa' hadd
    have hea : ea a a' := ⟨haa', hadd⟩
    by_cases hpa : P a
    · by_cases hpa' : P a'
      · have hval_a : mu a = (c (Classical.choose hpa).2)⁻¹ := by
          dsimp only [mu]; exact dif_pos hpa
        have hval_a' : mu a' = (c (Classical.choose hpa').2)⁻¹ := by
          dsimp only [mu]; exact dif_pos hpa'
        rw [hval_a, hval_a',
          hP_unique a (Classical.choose hpa) (Classical.choose hpa')
            (Classical.choose_spec hpa).1 (Classical.choose_spec hpa).2
            ((Relation.ReflTransGen.single hea).trans (Classical.choose_spec hpa').1)
            (Classical.choose_spec hpa').2]
      · exfalso
        exact hpa' ⟨Classical.choose hpa,
          (Relation.ReflTransGen.single (hea_symm a a' hea)).trans
            (Classical.choose_spec hpa).1,
          (Classical.choose_spec hpa).2⟩
    · by_cases hpa' : P a'
      · exfalso
        exact hpa ⟨Classical.choose hpa',
          (Relation.ReflTransGen.single hea).trans
            (Classical.choose_spec hpa').1,
          (Classical.choose_spec hpa').2⟩
      · have hval_a : mu a = 1 := by dsimp only [mu]; exact dif_neg hpa
        have hval_a' : mu a' = 1 := by dsimp only [mu]; exact dif_neg hpa'
        rw [hval_a, hval_a']

section UnitaryRootTwoSubgroup

open CFSG Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {y : G} {K : Subgroup G}

omit [Finite G] in
theorem ggGamma_y_eq_of_le (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    {y : G} (hyB : y ∈ B) (hyBs : y ∈ Bs) :
    ggGamma L hNL ⟨y, hyBs⟩ = ggGamma L hBL ⟨y, hyB⟩ := by
  simp only [ggGamma, MonoidHom.comp_apply]
  congr 1

theorem GGResHyp.layer_ggFix_ggGamma_y
    (hH : GGResHyp p B Bs x L D J y K)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hyB : y ∈ B) :
    LargeEvenLayer (ggFix (ggGamma L hBL ⟨y, hyB⟩)) = J.subgroupOf L := by
  classical
  have hcfg := hH.1
  have hnb := hH.2.2.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.1
  have hJL : J ≤ L :=
    hJ ▸ sSup_le fun K hK => hK.1.trans inf_le_left
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    have hD : D = Subgroup.closure {x, y} := hnb.2.1
    rw [hD, Subgroup.centralizer_closure]
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hl, -, hy⟩
      exact ⟨hl, hy⟩
    · rintro ⟨hl, hy⟩
      exact ⟨hl, Subgroup.mem_centralizer_iff.mp (hLx hl) x (by simp), hy⟩
  have hmap := map_ggFix_ggGamma L hBL ⟨y, hyB⟩
  have hLHS : (LargeEvenLayer (ggFix (ggGamma L hBL ⟨y, hyB⟩))).map L.subtype = J := by
    rw [← largeEvenLayer_map_of_injective L.subtype L.subtype_injective, hmap]
    change LargeEvenLayer (L ⊓ Subgroup.centralizer ({y} : Set G)) = J
    rw [← hcent, ← hJ]
  apply Subgroup.map_injective L.subtype_injective
  rw [hLHS, Subgroup.map_subgroupOf_eq_of_le hJL]

theorem GGResHyp.isComponentOf_layer_ggFix_ggGamma_y
    (hH : GGResHyp p B Bs x L D J y K)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hyB : y ∈ B) :
    IsComponentOf
      (LargeEvenLayer (ggFix (ggGamma L hBL ⟨y, hyB⟩)))
      (ggFix (ggGamma L hBL ⟨y, hyB⟩)) := by
  classical
  have hcfg := hH.1
  have hnb := hH.2.2.2.2.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hcomp := isComponentOf_subgroupOf_ggFix_ggGamma_y hcfg hnb hNL hyBs
  have hEq := ggGamma_y_eq_of_le hNL hBL hyB hyBs
  rw [hEq] at hcomp
  rw [← GGResHyp.layer_ggFix_ggGamma_y hH hBL hyB] at hcomp
  exact hcomp

theorem exists_theta_center_of_unitary {G : Type} [Group G] {L : Subgroup G}
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    {φ : ↥(unitarySU 2 n F d) →* ↥L}
    (hM : UnitTB.Model φ) (hd : 4 ≤ d) :
    ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F d),
      ∀ s : ↥(unitarySU 2 n F d),
        θ ((QuotientGroup.mk' (Subgroup.center ↥L)) (φ s)) =
          LargeEvenProjMk (unitarySU 2 n F d) s := by
  classical
  have hK : Nat.card F = (2 ^ n) ^ 2 := by
    rw [hM.field.card, ← pow_mul, Nat.mul_comm]
  let SU := ↥(unitarySU 2 n F d)
  let R := LargeEvenProj (unitarySU 2 n F d)
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let π : SU →* R := LargeEvenProjMk (unitarySU 2 n F d)
  let ψ : SU →* ↥L ⧸ Z := (QuotientGroup.mk' Z).comp φ
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨s, rfl⟩ := hM.surj l
    exact ⟨s, rfl⟩
  have hker : π.ker = ψ.ker := by
    apply le_antisymm
    ·
      intro s hs
      obtain ⟨c, hc⟩ :=
        (UnitTB.projMk_eq_one_iff (n := n) (d := d) (K := F)
          (by omega : 0 < d)).mp hs
      have hcenter : s ∈ Subgroup.center SU := SmallU.mem_center_of_scalar hc
      have hφcenter : φ s ∈ Z := by
        rw [Subgroup.mem_center_iff]
        intro l
        obtain ⟨y, rfl⟩ := hM.surj l
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp hcenter y
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' Z) (φ s) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hφcenter
    ·
      intro s hs
      have hφs : φ s ∈ Z := by
        have hs' : (QuotientGroup.mk' Z) (φ s) = 1 := hs
        rw [QuotientGroup.mk'_apply] at hs'
        exact (QuotientGroup.eq_one_iff (N := Z) (x := φ s)).mp hs'
      have hcomm : ∀ y : SU, φ (s * y * s⁻¹) = φ y := by
        intro y
        have hc := (Subgroup.mem_center_iff.mp hφs) (φ y)
        rw [map_mul, map_mul, map_inv, ← hc]
        group
      obtain ⟨c, hc⟩ := UnitTB.scalar_of_map_conj_eq hM hK (by omega : 4 ≤ d) hcomm
      rw [MonoidHom.mem_ker]
      exact (UnitTB.projMk_eq_one_iff (n := n) (d := d) (K := F)
        (by omega : 0 < d)).mpr ⟨c, hc⟩
  let eψ : SU ⧸ ψ.ker ≃* (↥L ⧸ Z) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let eπ : SU ⧸ π.ker ≃* R :=
    QuotientGroup.quotientKerEquivOfSurjective π hπ
  let θ : (↥L ⧸ Z) ≃* R :=
    eψ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans eπ)
  have hθ : ∀ s : SU, θ (ψ s) = π s := by
    intro s
    have h1 : eψ.symm (ψ s) = (QuotientGroup.mk s : SU ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h2 : (QuotientGroup.quotientMulEquivOfEq hker.symm)
        (QuotientGroup.mk s : SU ⧸ ψ.ker) =
        (QuotientGroup.mk s : SU ⧸ π.ker) :=
      QuotientGroup.quotientMulEquivOfEq_mk hker.symm s
    have h3 : eπ (QuotientGroup.mk s : SU ⧸ π.ker) = π s := by
      have h3symm : eπ.symm (π s) = (QuotientGroup.mk s : SU ⧸ π.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [← h3symm, MulEquiv.apply_symm_apply]
    change eπ ((QuotientGroup.quotientMulEquivOfEq hker.symm) (eψ.symm (ψ s))) = π s
    rw [h1, h2, h3]
  exact ⟨θ, hθ⟩

theorem ggHasLabel_of_unitaryModel {G : Type} [Group G] {X : Subgroup G}
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    {φ : ↥(unitarySU 2 n F d) →* ↥X}
    (hM : UnitTB.Model φ) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) :
    GGHasLabel ⟨.twA, d - 1, n⟩ (↥X ⧸ Subgroup.center ↥X) := by
  by_cases hd3 : d = 3
  · subst d
    classical
    have hF : Nat.card F = (2 ^ n) ^ 2 := by
      rw [hM.field.card, show 2 * n = n * 2 by omega, pow_mul]
    obtain ⟨hqs, hcen⟩ :=
      CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (F := F) (p := 2) (f := n) hF (by norm_num) hdq
    haveI : Group.IsPerfect ↥(unitarySU 2 n F 3) := ⟨hqs.1.1⟩
    have hcenter : Subgroup.center (unitarySU 2 n F 3) = unitaryScalars hM.field 3 := by
      rw [unitaryScalars_eq hM.field (n := 3) (by norm_num)]
      exact hcen
    let eZ : (unitarySU 2 n F 3 ⧸ Subgroup.center (unitarySU 2 n F 3)) ≃*
        (↥X ⧸ Subgroup.center ↥X) :=
      CFSG.ComponentClassification.PerfectCentralQuotient.equivalence φ hM.surj (by
        intro g hg
        obtain ⟨c, hc⟩ := hM.ker g (MonoidHom.mem_ker.mp hg)
        exact CFSG.StandardType.SmallU.mem_center_of_scalar hc)
    let eC : (unitarySU 2 n F 3 ⧸ Subgroup.center (unitarySU 2 n F 3)) ≃*
        unitaryPSU hM.field 3 :=
      QuotientGroup.quotientMulEquivOfEq hcenter
    let eP : unitaryPSU hM.field 3 ≃* LargeEvenProj (unitarySU 2 n F 3) :=
      unitaryPSUEquiv hM.field (n := 3) (by norm_num)
    refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
    change Nonempty (↥X ⧸ Subgroup.center ↥X ≃*
      LargeEvenProj (unitarySU 2 n F (3 - 1 + 1)))
    rw [show 3 - 1 + 1 = 3 by norm_num]
    exact ⟨eZ.symm.trans (eC.trans eP)⟩
  · have hd4 : 4 ≤ d := by omega
    obtain ⟨θ, _⟩ := exists_theta_center_of_unitary hM hd4
    refine ⟨F, inferInstance, inferInstance, hM.field.card_eq_sq, ?_⟩
    have hdeg : d - 1 + 1 = d := by omega
    change Nonempty (↥X ⧸ Subgroup.center ↥X ≃*
      LargeEvenProj (unitarySU 2 n F (d - 1 + 1)))
    rw [hdeg]
    exact ⟨θ⟩

theorem exists_theta_center_ggOutdiagOdd_of_unitary {G : Type} [Group G]
    {B Bs L : Subgroup G} {p : ℕ}
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    {φ : ↥(unitarySU 2 n F d) →* ↥L}
    (hBBs : B ≤ Bs) (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hNL).range, ∃ t : Fin d → F, ActsDiagU φ a t)
    (hn : 1 ≤ n) (hd : 4 ≤ d) :
    ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F d),
      Subgroup.center (LargeEvenProj (unitarySU 2 n F d)) = ⊥ ∧
      GGOutdiagOdd p (LargeEvenProj (unitarySU 2 n F d))
        (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
          (LargeEvenGUSet (Fin d) F (2 ^ n))) ∧
      ∀ b ∈ B, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
          (LargeEvenGUSet (Fin d) F (2 ^ n)),
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a := by
  classical
  obtain ⟨θ, hθ⟩ := exists_theta_center_of_unitary (n := n) (d := d) hM (by omega)
  have hK : Nat.card F = (2 ^ n) ^ 2 := by
    rw [hM.field.card, ← pow_mul, Nat.mul_comm]
  have hn1 : 1 ≤ n := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : d = 3 := congrArg Prod.fst h
    omega
  have hZR : Subgroup.center (LargeEvenProj (unitarySU 2 n F d)) = ⊥ :=
    TableBUE.center_proj_eq_bot (K := F) (n := n) (d := d) hK (by omega) hdq
  have hOD : GGOutdiagOdd p (LargeEvenProj (unitarySU 2 n F d))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
        (LargeEvenGUSet (Fin d) F (2 ^ n))) :=
    InndiagSU.ggOutdiagOdd_unitary (K := F) (n := n) (d := d) hK hn1
      (by omega) (by omega) p
  refine ⟨θ, hZR, hOD, ?_⟩
  intro b hb
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hNL
  have hb' : b⁻¹ ∈ B := B.inv_mem hb
  obtain ⟨t, hactNL⟩ :=
    hdiag (ggGamma L hNL ⟨b⁻¹, hBBs hb'⟩) ⟨⟨b⁻¹, hBBs hb'⟩, rfl⟩
  have hγeq : ggGamma L hBL ⟨b⁻¹, hb'⟩ =
      ggGamma L hNL ⟨b⁻¹, hBBs hb'⟩ := by
    simp only [ggGamma, MonoidHom.comp_apply]
    congr 1
  have hact : ActsDiagU φ (ggGamma L hBL ⟨b⁻¹, hb'⟩) t := by
    rw [hγeq]
    exact hactNL
  obtain ⟨D, hD, hDt, hact_apply⟩ := hact
  have hDgu : D ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
    let i0 : Fin d := ⟨0, by omega⟩
    let μ : F := t i0 ^ (2 ^ n + 1)
    have hμeq : ∀ i : Fin d, t i ^ (2 ^ n + 1) = μ := fun i =>
      UnitTB.diag_pow_norm_eq_of_mem_normalizer hM.field hD hDt i i0
    have hμ0 : μ ≠ 0 := by
      dsimp [μ]
      exact pow_ne_zero _ (LineU.diag_ne_zero_of_eq hDt i0)
    have hμq : μ ^ (2 ^ n) = μ := by
      have hpow : t i0 ^ ((2 ^ n) * (2 ^ n)) = t i0 := by
        have hbar := hM.field.bar_bar (t i0)
        rwa [hM.field.bar_apply, hM.field.bar_apply, ← pow_mul] at hbar
      dsimp [μ]
      calc (t i0 ^ (2 ^ n + 1)) ^ (2 ^ n) = t i0 ^ ((2 ^ n + 1) * (2 ^ n)) := by
            rw [pow_mul]
        _ = t i0 ^ ((2 ^ n) * (2 ^ n) + (2 ^ n)) := by ring_nf
        _ = t i0 ^ ((2 ^ n) * (2 ^ n)) * t i0 ^ (2 ^ n) := by rw [pow_add]
        _ = t i0 * t i0 ^ (2 ^ n) := by rw [hpow]
        _ = t i0 ^ (2 ^ n + 1) := by rw [pow_succ']
    refine ⟨μ, hμ0, hμq, ?_⟩
    rw [hDt, Matrix.diagonal_map (by
      exact zero_pow (by positivity : 2 ^ n ≠ 0)), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
      simpa [smul_eq_mul, pow_succ] using hμeq i
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.one_apply_ne hij,
        smul_zero]
  let a : MulAut (LargeEvenProj (unitarySU 2 n F d)) :=
    TableB.projConj (unitarySU 2 n F d) ⟨D, hD⟩
  have haI : a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
      (LargeEvenGUSet (Fin d) F (2 ^ n)) :=
    ⟨D, hDgu, fun h h' hhh => TableBUDT.projConj_graph hD h h' hhh⟩
  refine ⟨a, haI, ?_⟩
  intro l l' hrel
  obtain ⟨s, hs⟩ := hM.surj l
  have hψs : (QuotientGroup.mk' (Subgroup.center ↥L)) (φ s) =
      QuotientGroup.mk l := by
    rw [QuotientGroup.mk'_apply, hs]
  have hθs : θ (QuotientGroup.mk l) = LargeEvenProjMk (unitarySU 2 n F d) s := by
    rw [← hψs]
    exact hθ s
  have hacts : a (θ (QuotientGroup.mk l)) =
      LargeEvenProjMk (unitarySU 2 n F d) (LineU.conjN D hD s) := by
    rw [hθs]
    exact TableBUD.projConj_mk_coe ⟨D, hD⟩ s
  have haLl : ggGamma L hBL ⟨b⁻¹, hb'⟩ l = l' := by
    apply Subtype.ext
    rw [ggGamma_coe]
    simpa using hrel.symm
  have hφs' : φ (LineU.conjN D hD s) = l' := by
    rw [← hact_apply s, hs]
    exact haLl
  have hθl' : θ (QuotientGroup.mk l') =
      LargeEvenProjMk (unitarySU 2 n F d) (LineU.conjN D hD s) := by
    have hψs' : (QuotientGroup.mk' (Subgroup.center ↥L)) (φ (LineU.conjN D hD s)) =
        QuotientGroup.mk l' := by
      rw [QuotientGroup.mk'_apply, hφs']
    rw [← hψs']
    exact hθ (LineU.conjN D hD s)
  rw [hacts, hθl']

theorem GGResHyp.centralizer_J_le_D_of_unitary
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t)
    (hn : 2 ≤ n) (hd : 5 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    (hlt : B < Bs) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  classical
  have hcfg := hH.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  let : Fact p.Prime := ⟨hp⟩
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hNL
  obtain ⟨θ, hZR, hOD, h3⟩ :=
    exists_theta_center_ggOutdiagOdd_of_unitary hBBs hNL hM hdiag (by omega) (by omega)
  let R := LargeEvenProj (unitarySU 2 n F d)
  have hL : commutator ↥L = ⊤ := hH.2.2.1.1.1
  have hnb := hH.2.2.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hBBs hyB
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInput_holds G p B x L hcfg.1
  have hne : B ≠ Bs := hlt.ne
  obtain ⟨V, hV1, hV2, hBV⟩ :=
    hcfg.beta_twoLocal_of_ne hnc hL θ hBL h3 hOD hne
  set A : Subgroup (MulAut ↥L) := (ggGamma L hBL).range with hA
  have hdiagA : ∀ a ∈ A, ∃ t : Fin d → F, ActsDiagU φ a t := by
    rintro _ ⟨b, rfl⟩
    have h := hdiag (ggGamma L hNL ⟨b.1, hBBs b.2⟩) ⟨⟨b.1, hBBs b.2⟩, rfl⟩
    rw [ggGamma_y_eq_of_le hNL hBL b.2 (hBBs b.2)] at h
    exact h
  have hAp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    have hb : (b : ↥B) ^ p = 1 := Subtype.ext (by simpa using hBs.2 b.1 (hBBs b.2))
    rw [← map_pow, hb, map_one]
  have hK : Nat.card F = (2 ^ n) ^ 2 := by
    rw [hM.field.card, ← pow_mul, Nat.mul_comm]
  have hAU : ∀ a ∈ A, ∀ l : ↥L, ggQuotHom θ l ∈ V → ggQuotHom θ (a l) ∈ V := by
    rintro _ ⟨b, rfl⟩ l hl
    have h := hBV (ggBeta L θ hBL b) ⟨b, rfl⟩ (ggQuotHom θ l) hl
    rw [← ggBeta_ggQuotHom]
    exact h
  obtain ⟨s, t, hst, hpair⟩ :=
    SmallU.exists_pair hM hK (by omega) hp hpq (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hZR hAp hdiagA hV1 hV2 hAU
  have haA : ggGamma L hBL ⟨y, hyB⟩ ∈ A := ⟨⟨y, hyB⟩, rfl⟩
  obtain ⟨t₀, ht₀⟩ := hdiagA (ggGamma L hBL ⟨y, hyB⟩) haA
  obtain ⟨σ, -, hσ⟩ := SmallU.ActsU.of_actsDiagU ht₀
  have hEcomp : IsComponentOf
      (LargeEvenLayer (ggFix (ggGamma L hBL ⟨y, hyB⟩)))
      (ggFix (ggGamma L hBL ⟨y, hyB⟩)) :=
    GGResHyp.isComponentOf_layer_ggFix_ggGamma_y hH hBL hyB
  obtain ⟨U, hU1, hU2, hUA, hUle⟩ :=
    SmallU.exists_swap_group_le_layer hM hn (by omega : 3 ≤ d) hdiagA haA hσ hEcomp hst hpair
  have hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.1
  have hJL : J ≤ L :=
    hJ ▸ sSup_le fun K hK => hK.1.trans inf_le_left
  have hJmap : (J.subgroupOf L).map L.subtype = J :=
    Subgroup.map_subgroupOf_eq_of_le hJL
  have hJle : U ≤ J.subgroupOf L := by
    rw [← GGResHyp.layer_ggFix_ggGamma_y hH hBL hyB]
    exact hUle
  set T : Subgroup G := U.map L.subtype with hT
  have hT1 : T ≠ ⊥ := by
    rw [hT]
    intro h
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h)
  have hT2 : IsPGroup 2 T := hU2.map L.subtype
  have hTJ : T ≤ J := by
    rw [hT]
    exact (Subgroup.map_mono hJle).trans (le_of_eq hJmap)
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨l, hlU, rfl⟩ := Subgroup.mem_map.mp hg
      have hbl : b * (l : G) * b⁻¹ =
          L.subtype ((ggGamma L hBL ⟨b, hb⟩) l) :=
        (by simpa using (ggGamma_coe L hBL ⟨b, hb⟩ l).symm)
      change b * (l : G) * b⁻¹ ∈ T
      rw [hbl]
      exact Subgroup.mem_map_of_mem L.subtype
        (hUA (ggGamma L hBL ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ l hlU)
    · intro hg
      obtain ⟨l, hlU, hgl⟩ := Subgroup.mem_map.mp hg
      have hb' : b⁻¹ * (l : G) * b =
          L.subtype ((ggGamma L hBL ⟨b⁻¹, B.inv_mem hb⟩) l) :=
        (by simpa using (ggGamma_coe L hBL ⟨b⁻¹, B.inv_mem hb⟩ l).symm)
      have hTmem : b⁻¹ * (l : G) * b ∈ T := by
        rw [hb']
        exact Subgroup.mem_map_of_mem L.subtype
          (hUA (ggGamma L hBL ⟨b⁻¹, B.inv_mem hb⟩) ⟨⟨b⁻¹, B.inv_mem hb⟩, rfl⟩ l hlU)
      have hg_eq : g = b⁻¹ * (l : G) * b := by
        calc g = b⁻¹ * (b * g * b⁻¹) * b := by group
          _ = b⁻¹ * L.subtype l * b := by rw [← hgl]
          _ = b⁻¹ * (l : G) * b := rfl
      rwa [hg_eq]
  by_contra hnot
  obtain ⟨c, hc, hcD⟩ := Set.not_subset.mp hnot
  obtain ⟨hcBs, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcB : c ∉ B := by
    intro hcB
    apply hcD
    have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
    rw [hD]
    exact ⟨hcB, hcC⟩
  have hcp : c ^ p = 1 := hBs.2 c hcBs
  have hcomm : ∀ e ∈ B, e * c = c * e := fun e he =>
    CFSG.Open.IsElemAbelian.comm hBs (hBBs he) hcBs
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup
    (CFSG.Open.IsElemAbelian.mono hBs hBBs : IsElemAbelian p B))
  have hsupcard := isElemAbelian_sup_zpowers_of_card hp
    (CFSG.Open.IsElemAbelian.mono hBs hBBs) hk hcp hcB hcomm
  have hsup_eq : B ⊔ Subgroup.zpowers c = Bs := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hBBs (Subgroup.zpowers_le.mpr hcBs)) ?_
    calc Nat.card Bs ≤ p * Nat.card B := hcfg.2.1.2.2.1
      _ = p ^ (k + 1) := by rw [pow_succ, hk, Nat.mul_comm]
      _ = Nat.card ↥(B ⊔ Subgroup.zpowers c) := hsupcard.2.symm
  have hcT : c ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hcomm' : g * c = c * g :=
        Subgroup.mem_centralizer_iff.mp hcC g (hTJ hg)
      have hcg : c * g * c⁻¹ = g := by
        rw [hcomm'.symm]
        group
      rw [hcg]
      exact hg
    · intro hg
      have hgJ : c * g * c⁻¹ ∈ J := hTJ hg
      have hcomm' : (c * g * c⁻¹) * c = c * (c * g * c⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hcC (c * g * c⁻¹) hgJ
      have hcg : g = c * g * c⁻¹ := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = c⁻¹ * ((c * g * c⁻¹) * c) := by group
          _ = c⁻¹ * (c * (c * g * c⁻¹)) := by rw [hcomm']
          _ = c * g * c⁻¹ := by group
      rw [← hcg] at hg
      exact hg
  have hBsN_T : Bs ≤ Subgroup.normalizer (T : Set G) := by
    rw [← hsup_eq]
    exact sup_le hBT (Subgroup.zpowers_le.mpr hcT)
  exact hlt.ne (Subgroup.eq_of_le_of_card_ge hBBs (by
    have hle : Nat.card Bs ≤ p ^ LargeEvenTwoLocalRank p G :=
      TableB.card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hBsN_T hcfg.2.1.2.1
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
      hcfg.1.2.2.2.2.2.2.1.1.2.1
    exact hBcard ▸ hle))

theorem GGResHyp.centralizer_J_card_ne_p3_of_unitary
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t)
    (hn : 2 ≤ n) (hd : 5 ≤ d) (hpq : p ∣ 2 ^ n + 1) (hlt : B < Bs)
    (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3) : False := by
  classical
  have hle := GGResHyp.centralizer_J_le_D_of_unitary hH hM hdiag hn hd hpq hlt
  have hcardle : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ Nat.card ↥D :=
    Subgroup.card_le_of_le hle
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hp : p.Prime := hH.1.tableB_facts.1
  rw [hcard, hDcard] at hcardle
  exact (Nat.not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3))) hcardle

end UnitaryRootTwoSubgroup

end CFSG.StandardType

end
