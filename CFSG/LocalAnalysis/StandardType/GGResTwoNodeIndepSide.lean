module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepChain
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import TauCeti.GroupTheory.Coxeter.Matrix
public import TauCeti.Combinatorics.SimpleGraph.BranchComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6sc_cartan_eq_zero_iff {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {i j : Λ} (hij : i ≠ j) : C i j = 0 ↔ M.M i j = 2 := by
  constructor
  · intro h
    rcases hC.2 i j hij with ⟨hm, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · exact hm
    · rw [h] at h1; exact absurd h1 (by norm_num)
    · rw [h, zero_mul] at h1; exact absurd h1 (by norm_num)
    · rw [h, zero_mul] at h1; exact absurd h1 (by norm_num)
  · intro h
    rcases hC.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · exact h1
    · exact absurd (hm.symm.trans h) (by norm_num)
    · exact absurd (hm.symm.trans h) (by norm_num)
    · exact absurd (hm.symm.trans h) (by norm_num)

private theorem l6sc_weylFixed {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    GGIsWeylMatrixFixed M := h

private theorem l6sc_nonempty {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private theorem l6sc_graph_adj {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (i j : Λ) :
    (TauCeti.diagramGraph C).Adj i j ↔ i ≠ j ∧ M.M i j ≠ 2 := by
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l6sc_weylFixed hWM) hC
  rw [TauCeti.IsFiniteType.diagramGraph_adj_iff hFT]
  constructor
  · rintro ⟨hij, hCij⟩
    exact ⟨hij, fun hM => hCij ((l6sc_cartan_eq_zero_iff hC hij).2 hM)⟩
  · rintro ⟨hij, hMij⟩
    exact ⟨hij, fun h0 => hMij ((l6sc_cartan_eq_zero_iff hC hij).1 h0)⟩

private theorem l6sc_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem l6sc_reindex_trans {ι κ ν : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ ν) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

private theorem l6sc_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l6sc_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l6sc_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l6sc_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l6sc_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l6sc_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l6sc_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l6sc_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l6sc_reindex_trans]⟩))))

private theorem l6sc_intCartan_reindex {Γ Δ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (h : GGIntCartan M C) (e : Δ ≃ Γ) :
    GGIntCartan (M.reindex e.symm) (fun o o' => C (e o) (e o')) := by
  constructor
  · intro o
    simpa using h.1 (e o)
  · intro o o' hne
    have hene : e o ≠ e o' := fun hh => hne (e.injective hh)
    have hh := h.2 (e o) (e o') hene
    simpa only [CoxeterMatrix.reindex_apply, Equiv.symm_symm] using hh

private theorem l6sc_rtg_map {α β : Type} {r : α → α → Prop} {p : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → p (f a) (f b)) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem l6sc_isTree {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) :
    (TauCeti.diagramGraph C).IsTree := by
  classical
  have hadj := l6sc_graph_adj (M := M) (C := C) hW hC
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l6sc_weylFixed hW) hC
  have hpre : (TauCeti.diagramGraph C).Preconnected := by
    intro i j
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact l6sc_rtg_mono (fun u v huv => (hadj u v).2 huv) (ggRC_weyl_connected hW i j)
  have hconn : (TauCeti.diagramGraph C).Connected :=
    (SimpleGraph.connected_iff _).2 ⟨hpre, l6sc_nonempty hW⟩
  exact TauCeti.IsFiniteType.isTree_diagramGraph hFT hconn

private theorem l6sc_reach_J {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) (a : Λa) {i j : Jn}
    (h : Relation.ReflTransGen (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j) :
    ((TauCeti.diagramGraph C).induce ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))).Reachable
      ⟨Sum.inl i, by simp⟩ ⟨Sum.inl j, by simp⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  refine l6sc_rtg_map
    (fun u : Jn => (⟨Sum.inl u, by simp⟩ :
      {x : Jn ⊕ Λa // x ∈ ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))})) ?_ h
  intro u v huv
  rw [SimpleGraph.induce_adj]
  exact (l6sc_graph_adj (M := M) (C := C) hW hC (Sum.inl u) (Sum.inl v)).2
    ⟨fun h => huv.1 (Sum.inl.inj h), huv.2⟩

private theorem l6sc_J_unique {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (a : Λa) (j j' : Jn) (hj : M.M (Sum.inr a) (Sum.inl j) ≠ 2)
    (hj' : M.M (Sum.inr a) (Sum.inl j') ≠ 2) : j = j' := by
  classical
  have htree := l6sc_isTree (M := M) (C := C) hW hC
  have hadj := l6sc_graph_adj (M := M) (C := C) hW hC
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
      (l6sc_reach_J (M := M) (C := C) hW hC a (hJ j j'))
  have hval : (x : Jn ⊕ Λa) = (y : Jn ⊕ Λa) :=
    congrArg Subtype.val ((TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree
      (Sum.inr a)).injective heq)
  exact Sum.inl.inj hval

private theorem l6sc_first_step {Jn Λa : Type} {M : CoxeterMatrix (Jn ⊕ Λa)}
    (a₀ : Λa) (huniq : ∀ a : Λa, a = a₀) {j₀ : Jn}
    (h : Relation.ReflTransGen (fun u v : Jn ⊕ Λa => u ≠ v ∧ M.M u v ≠ 2)
      (Sum.inr a₀) (Sum.inl j₀)) :
    ∃ j : Jn, M.M (Sum.inr a₀) (Sum.inl j) ≠ 2 := by
  rcases Relation.ReflTransGen.cases_head h with h0 | ⟨c, hc, -⟩
  · exact absurd h0 (by simp)
  · rcases hc with ⟨hne, hM⟩
    cases c with
    | inr b =>
        exact absurd (by rw [huniq b] : Sum.inr a₀ = Sum.inr b) hne
    | inl j => exact ⟨j, hM⟩

theorem ggJoint_exists_attached_added_node {Jn Λa : Type}
    [Fintype Jn] [DecidableEq Jn] [Fintype Λa] [DecidableEq Λa]
    [Nonempty Jn] [Nonempty Λa] {M : CoxeterMatrix (Jn ⊕ Λa)}
    (hW : GGIsWeylMatrix M) :
    ∃ a : Λa, ∃ j : Jn, M.M (Sum.inr a) (Sum.inl j) ≠ 2 := by
  classical
  let a₀ : Λa := Classical.choice (inferInstance : Nonempty Λa)
  let j₀ : Jn := Classical.choice (inferInstance : Nonempty Jn)
  have hpath := ggRC_weyl_connected hW (Sum.inr a₀) (Sum.inl j₀)
  have aux : ∀ v : Jn ⊕ Λa, Relation.ReflTransGen
      (fun u w => u ≠ w ∧ M.M u w ≠ 2) (Sum.inr a₀) v →
      (∃ a : Λa, v = Sum.inr a) ∨
        ∃ a : Λa, ∃ j : Jn, M.M (Sum.inr a) (Sum.inl j) ≠ 2 := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨a₀, rfl⟩
    | tail hu huv ih =>
        rename_i v
        rcases ih with ⟨a, ha⟩ | hc
        · rw [ha] at huv
          cases v with
          | inl j => exact Or.inr ⟨a, j, huv.2⟩
          | inr b => exact Or.inl ⟨b, rfl⟩
        · exact Or.inr hc
  rcases aux _ hpath with ⟨a, ha⟩ | hc
  · exact (Sum.inl_ne_inr ha).elim
  · exact hc

theorem ggJoint_oneNode_sideClause_selected {G : Type} [Group G] [Finite G]
    {p N : ℕ} [Fact p.Prime] {Bs K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} (hb : b₁ ≠ b₂)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa] (a₀ : Λa) (hN : 5 ≤ N)
    {ML : CoxeterMatrix Λ} (e : Fin (N - 1) ≃ Λ)
    (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hconn : GGDeletedConnected2 ML b₁ b₂)
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1)
    (hattach : ∃ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inr a₀) (Sum.inl j) ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ∃ (S : Finset (Fin (N - 1))) (MK' : CoxeterMatrix (Option ↥S))
        (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∀ i : Fin (N - 1), i ∈ S ↔ (e i ≠ b₁ ∧ e i ≠ b₂)) ∧
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧
      GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
      (∀ i j : Option ↥S, (CK' i j : ZMod p) =
        (i.elim (α (Sum.inr a₀)) fun a => α (Sum.inl (e a)))
          (j.elim (h (Sum.inr a₀)) fun b => h (Sum.inl (e b)))) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
      ∃ f : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => ggLin (p := p) ι (φ (Sum.inl (e j))))
          (ggLin (p := p) ι (φ (Sum.inr a₀)))),
        ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod p] V)) =
          o.elim (ggLin (p := p) ι (φ (Sum.inr a₀))) fun j => ggLin (p := p) ι (φ (Sum.inl (e j))) := by
  classical
  let Jn : Type := {i : Λ // i ≠ b₁ ∧ i ≠ b₂}
  let Jset : Set (Jn ⊕ Λa) :=
    Set.range (Sum.inl : Jn → Jn ⊕ Λa) ∪ {Sum.inr a₀}
  have hconnA : GGDeletedConnected2 ((CoxeterMatrix.A (N - 1)).reindex e) b₁ b₂ := by
    rwa [← hML]
  obtain ⟨s, hs2, hsint⟩ := ggChainA_deleted_interval (n := N - 1) (by omega) e b₁ b₂ hb hconnA
  have hsint' : ∀ i : Fin (N - 1),
      (e i ≠ b₁ ∧ e i ≠ b₂) ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3) := by
    intro i
    have h := hsint i
    rwa [show (N - 1) - 2 = N - 3 by omega] at h
  let S : Finset (Fin (N - 1)) := Finset.univ.filter (fun i => e i ≠ b₁ ∧ e i ≠ b₂)
  let eJ : ↥S ≃ Jn :=
  { toFun := fun i => ⟨e i.1, (Finset.mem_filter.mp i.2).2⟩
    invFun := fun j => ⟨e.symm j.1, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using j.2⟩⟩
    left_inv := by intro i; apply Subtype.ext; simp
    right_inv := by intro j; apply Subtype.ext; simp }
  let eJsub : Option ↥S ≃ Jset :=
  { toFun := fun o => o.elim ⟨Sum.inr a₀, by simp [Jset]⟩
      (fun j => ⟨Sum.inl (eJ j), by simp [Jset]⟩)
    invFun := fun x => match x.1 with
      | Sum.inl j => some (eJ.symm j)
      | Sum.inr _ => none
    left_inv := by
      intro o
      cases o with
      | none => rfl
      | some j => simp
    right_inv := by
      intro x
      rcases x with ⟨sx, hsx⟩
      rcases sx with j | a
      · simp
      · have ha : a = a₀ := by
          simpa [Jset] using hsx
        subst ha
        simp }
  obtain ⟨j₁, hj₁⟩ := hattach
  let S0 : Finset (Jn ⊕ Λa) := Finset.univ.filter (fun x => x ∉ Jset)
  have hS0 : ∀ x : Jn ⊕ Λa, x ∉ S0 ↔ x ∈ Jset := by
    intro x
    simp [S0]
  have hnon : Nonempty {x : Jn ⊕ Λa // x ∉ S0} :=
    ⟨⟨Sum.inl j₁, (hS0 _).2 (by simp [Jset])⟩⟩
  let incs : Jn → {x : Jn ⊕ Λa // x ∉ S0} := fun j =>
    ⟨Sum.inl j, (hS0 _).2 (by simp [Jset])⟩
  let a0s : {x : Jn ⊕ Λa // x ∉ S0} :=
    ⟨Sum.inr a₀, (hS0 _).2 (by simp [Jset])⟩
  have hJ_MK : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ MK.M (Sum.inl u) (Sum.inl v) ≠ 2) i j := by
    intro i j
    exact l6sc_rtg_mono (fun u v huv => ⟨huv.1, by rw [hJM u v]; exact huv.2⟩) (hconn i j)
  have hJpath : ∀ j j' : Jn, Relation.ReflTransGen
      (fun u v : {x : Jn ⊕ Λa // x ∉ S0} => u ≠ v ∧ MK.M u v ≠ 2)
      (incs j) (incs j') := by
    intro j j'
    refine l6sc_rtg_map incs ?_ (hJ_MK j j')
    intro u v huv
    refine ⟨?_, ?_⟩
    · intro h
      exact huv.1 (Sum.inl.inj (congrArg Subtype.val h))
    · simpa using huv.2
  have hstep : (fun u v : {x : Jn ⊕ Λa // x ∉ S0} => u ≠ v ∧ MK.M u v ≠ 2)
      a0s (incs j₁) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact Sum.inr_ne_inl (congrArg Subtype.val h)
    · simpa [incs, a0s] using hj₁
  have hstep_symm : (fun u v : {x : Jn ⊕ Λa // x ∉ S0} => u ≠ v ∧ MK.M u v ≠ 2)
      (incs j₁) a0s := by
    refine ⟨?_, ?_⟩
    · intro h
      exact Sum.inl_ne_inr (congrArg Subtype.val h)
    · show MK.M (Sum.inl j₁) (Sum.inr a₀) ≠ 2
      intro h
      exact hj₁ ((MK.isSymm.apply (Sum.inl j₁) (Sum.inr a₀)).trans h)
  have hdel : GGDeletedConnectedS MK S0 := by
    intro i j
    have hi : i.1 ∈ Jset := (hS0 i.1).1 i.2
    have hj : j.1 ∈ Jset := (hS0 j.1).1 j.2
    simp only [Jset, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hi hj
    rcases hi with ⟨ji, hji⟩ | hji
    · rcases hj with ⟨jj, hjj⟩ | hjj
      · have hii : i = incs ji := Subtype.ext hji.symm
        have hjj' : j = incs jj := Subtype.ext hjj.symm
        rw [hii, hjj']
        exact hJpath ji jj
      · have hii : i = incs ji := Subtype.ext hji.symm
        have hjj' : j = a0s := Subtype.ext hjj
        rw [hii, hjj']
        exact (hJpath ji j₁).tail hstep_symm
    · rcases hj with ⟨jj, hjj⟩ | hjj
      · have hii : i = a0s := Subtype.ext hji
        have hjj' : j = incs jj := Subtype.ext hjj.symm
        rw [hii, hjj']
        exact Relation.ReflTransGen.head hstep (hJpath j₁ jj)
      · have hii : i = a0s := Subtype.ext hji
        have hjj' : j = a0s := Subtype.ext hjj
        rw [hii, hjj']
  have hcomp : {x : Jn ⊕ Λa | x ∉ S0} = Jset := by
    ext x
    simp [S0]
  have hWpar' : GGIsWeylMatrix (parMatrix MK Jset) := by
    have hraw := l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected
      S0 MK CK hWMK hCK hdel hnon
    rw [hcomp] at hraw
    exact hraw
  let MK' : CoxeterMatrix (Option ↥S) := (parMatrix MK Jset).reindex eJsub.symm
  let CK' : Matrix (Option ↥S) (Option ↥S) ℤ :=
    fun o o' => CK (eJsub o).1 (eJsub o').1
  have hW' : GGIsWeylMatrix MK' := l6sc_weyl_reindex hWpar' eJsub.symm
  have hCpar : GGIntCartan (parMatrix MK Jset) (fun i j => CK i.1 j.1) := by
    constructor
    · intro i
      simpa [parMatrix] using hCK.1 i.1
    · intro i j hij
      simpa [parMatrix] using hCK.2 i.1 j.1 (fun h => hij (Subtype.ext h))
  have hC' : GGIntCartan MK' CK' := l6sc_intCartan_reindex hCpar eJsub
  refine ⟨S, MK', CK', ?_, ?_, hW', hC', ?_, ?_, ?_⟩
  · intro i
    simp [S]
  · refine ⟨s, hs2, ?_⟩
    intro i
    rw [show i ∈ S ↔ (e i ≠ b₁ ∧ e i ≠ b₂) from by simp [S]]
    exact hsint' i
  · intro i j
    have hp := hpairK (eJsub i).1 (eJsub j).1
    change (CK (eJsub i).1 (eJsub j).1 : ZMod p) = _
    rw [← hp]
    cases i <;> cases j <;> simp [eJsub, eJ, Jset]
  · refine ⟨eJ.symm j₁, ?_⟩
    intro j
    have hne : CK' none (some j) ≠ 0 ↔ MK'.M none (some j) ≠ 2 :=
      not_congr (l6sc_cartan_eq_zero_iff hC' (show none ≠ some j by simp))
    rw [hne]
    constructor
    · intro hj
      have hj' : MK.M (Sum.inr a₀) (Sum.inl (eJ j)) ≠ 2 := by
        simpa [MK', parMatrix, CoxeterMatrix.reindex_apply, eJsub, eJ, Jset] using hj
      have hj₁' : MK.M (Sum.inr a₀) (Sum.inl j₁) ≠ 2 := hj₁
      have heq : eJ j = j₁ := l6sc_J_unique hWMK hCK hJ_MK a₀ (eJ j) j₁ hj' hj₁'
      apply eJ.injective
      rw [Equiv.apply_symm_apply]
      exact heq
    · intro hjc
      rw [hjc]
      simpa [MK', parMatrix, CoxeterMatrix.reindex_apply, eJsub, eJ, Jset] using hj₁
  ·
    obtain ⟨fK, hfK'⟩ := hfK
    let csK : CoxeterSystem MK MK.Group := MK.toCoxeterSystem
    have hparGen : csK.parabolic Jset =
        Subgroup.closure (csK.simple '' Jset) := by
      apply le_antisymm
      · rw [csK.parabolic_le_iff]
        intro i hi
        exact Subgroup.subset_closure ⟨i, hi, rfl⟩
      · refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        exact csK.simple_mem_parabolic hi
    let fK' : MK.Group →* MulAut ↥Bs := (ggAutomizer K Bs).subtype.comp fK.toMonoidHom
    have hfK'inj : Function.Injective fK' := by
      intro x y hxy
      apply fK.injective
      apply Subtype.ext
      exact hxy
    let P : Subgroup (MulAut ↥Bs) := (csK.parabolic Jset).map fK'
    have hPgen : P = Subgroup.closure
        (Set.range (fun j : ↥S => fK' (csK.simple (eJsub (some j)).1)) ∪
          {fK' (csK.simple (eJsub none).1)}) := by
      dsimp only [P]
      rw [hparGen, MonoidHom.map_closure]
      congr 1
      rw [Set.image_image]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨i, hi, rfl⟩
        · left
          refine ⟨eJ.symm i, ?_⟩
          simp [eJsub, eJ]
        · right
          simp_all [Jset, eJsub]
      · rintro (⟨j, rfl⟩ | rfl)
        · refine ⟨eJsub (some j), ?_, rfl⟩
          simp
        · refine ⟨eJsub none, ?_, rfl⟩
          simp
    have hmapP : P.map (ggLin (p := p) ι) =
        lr6Group (fun j : ↥S => ggLin (p := p) ι (φ (Sum.inl (e j))))
          (ggLin (p := p) ι (φ (Sum.inr a₀))) := by
      rw [hPgen, MonoidHom.map_closure]
      congr 1
      rw [Set.image_union]
      congr 1
      · rw [← Set.range_comp]
        congr 1
        funext j
        simp [fK', hfK', eJsub, eJ, csK]
      · ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          rw [Set.mem_singleton_iff] at ha
          rw [ha]
          simp [fK', hfK', eJsub, csK]
        · intro hx
          rw [Set.mem_singleton_iff] at hx
          refine ⟨fK' (csK.simple (eJsub none).1), by simp, ?_⟩
          rw [hx]
          simp [fK', hfK', eJsub, csK]
    let ePar : (parMatrix MK Jset).Group ≃* csK.parabolic Jset :=
    { toFun := parToPar csK Jset
      invFun := parOfGroup csK Jset
      left_inv := by intro x; exact parOfGroup_parToPar csK Jset x
      right_inv := by
        intro w
        apply Subtype.ext
        change (parToGroup csK Jset (parOfGroup csK Jset w)) = (w : MK.Group)
        exact parToGroup_parOfGroup csK Jset w
      map_mul' := fun x y => (parToPar csK Jset).map_mul x y }
    let eAuto : csK.parabolic Jset ≃* P :=
      Subgroup.equivMapOfInjective (csK.parabolic Jset) fK' hfK'inj
    let eLin : P ≃* ↥(lr6Group (fun j : ↥S => ggLin (p := p) ι (φ (Sum.inl (e j))))
        (ggLin (p := p) ι (φ (Sum.inr a₀)))) :=
      (Subgroup.equivMapOfInjective P (ggLin (p := p) ι) (ggLin_injective ι)).trans
        (MulEquiv.subgroupCongr hmapP)
    let F : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => ggLin (p := p) ι (φ (Sum.inl (e j))))
        (ggLin (p := p) ι (φ (Sum.inr a₀)))) :=
      (CoxeterMatrix.reindexGroupEquiv (M := parMatrix MK Jset) eJsub.symm).trans
        (ePar.trans (eAuto.trans eLin))
    refine ⟨F, ?_⟩
    intro o
    dsimp only [F, MulEquiv.trans_apply]
    rw [show (CoxeterMatrix.reindexGroupEquiv (M := parMatrix MK Jset) eJsub.symm)
        (MK'.simple o) = (parMatrix MK Jset).simple (eJsub o) from by
      simpa [MK'] using
        (CoxeterMatrix.reindexGroupEquiv_apply_simple (M := parMatrix MK Jset)
          eJsub.symm o)]
    have hpar : ePar ((parMatrix MK Jset).simple (eJsub o)) =
        ⟨csK.simple (eJsub o).1, csK.simple_mem_parabolic (eJsub o).2⟩ := by
      apply Subtype.ext
      change (parToPar csK Jset ((parMatrix MK Jset).simple (eJsub o)) : MK.Group) =
        csK.simple (eJsub o).1
      rw [coe_parToPar, parToGroup_simple]
    rw [hpar]
    change (ggLin (p := p) ι
      (↑(fK (MK.simple (eJsub o).1)) : MulAut ↥Bs) : V ≃ₗ[ZMod p] V) = _
    rw [hfK' (eJsub o).1]
    cases o with
    | none => simp [eJsub]
    | some j => simp [eJsub, eJ]

theorem ggJoint_oneNode_sideClause {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} (hb : b₁ ≠ b₂)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 1) (a₀ : Λa) (hN : 5 ≤ N)
    {ML : CoxeterMatrix Λ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hconn : GGDeletedConnected2 ML b₁ b₂)
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1)
    {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ∃ (S : Finset (Fin (N - 1))) (MK' : CoxeterMatrix (Option ↥S))
        (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∀ i : Fin (N - 1), i ∈ S ↔ (e i ≠ b₁ ∧ e i ≠ b₂)) ∧
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧
      GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
      (∀ i j : Option ↥S, (CK' i j : ZMod p) =
        (i.elim (α (Sum.inr a₀)) fun a => α (Sum.inl (e a)))
          (j.elim (h (Sum.inr a₀)) fun b => h (Sum.inl (e b)))) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
      ∃ f : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => ggLin (p := p) ι (φ (Sum.inl (e j))))
          (ggLin (p := p) ι (φ (Sum.inr a₀)))),
        ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod p] V)) =
          o.elim (ggLin (p := p) ι (φ (Sum.inr a₀))) fun j => ggLin (p := p) ι (φ (Sum.inl (e j))) := by
  classical
  have huniq : ∀ a : Λa, a = a₀ := by
    obtain ⟨a₁, ha₁⟩ := Nat.card_eq_one_iff_exists.mp hΛa
    intro a
    exact (ha₁ a).trans (ha₁ a₀).symm
  let Jn : Type := {i : Λ // i ≠ b₁ ∧ i ≠ b₂}
  let Jset : Set (Jn ⊕ Λa) :=
    Set.range (Sum.inl : Jn → Jn ⊕ Λa) ∪ {Sum.inr a₀}
  have hconnA : GGDeletedConnected2 ((CoxeterMatrix.A (N - 1)).reindex e) b₁ b₂ := by
    rwa [← hML]
  obtain ⟨s, hs2, hsint⟩ := ggChainA_deleted_interval (n := N - 1) (by omega) e b₁ b₂ hb hconnA
  have hsint' : ∀ i : Fin (N - 1),
      (e i ≠ b₁ ∧ e i ≠ b₂) ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3) := by
    intro i
    have h := hsint i
    rwa [show (N - 1) - 2 = N - 3 by omega] at h
  have hs_lt : s < N - 1 := by omega
  let i₀ : Fin (N - 1) := ⟨s, hs_lt⟩
  have hi₀prop : e i₀ ≠ b₁ ∧ e i₀ ≠ b₂ := by
    rw [hsint' i₀]
    change s ≤ s ∧ s < s + (N - 3)
    exact ⟨le_rfl, by omega⟩
  let j₀ : Jn := ⟨e i₀, hi₀prop⟩
  have hpath : Relation.ReflTransGen
      (fun u v : Jn ⊕ Λa => u ≠ v ∧ MK.M u v ≠ 2)
      (Sum.inr a₀) (Sum.inl j₀) := ggRC_weyl_connected hWMK _ _
  obtain ⟨j₁, hj₁⟩ := l6sc_first_step a₀ huniq hpath
  exact ggJoint_oneNode_sideClause_selected (p := p) (N := N) (Bs := Bs) (K := K)
    hb a₀ hN e hML hconn hWMK hCK hJM ⟨j₁, hj₁⟩ hφ hpairK hfK hAK

end CFSG.StandardType

end
