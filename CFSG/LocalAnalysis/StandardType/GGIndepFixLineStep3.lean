module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2Defs
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6f3_walk_map {V W : Type*} {G : SimpleGraph V} {R : W → W → Prop} (f : V → W)
    (h : ∀ a b, G.Adj a b → R (f a) (f b)) {u v : V} (w : G.Walk u v) :
    Relation.ReflTransGen R (f u) (f v) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons hadj _ ih => exact Relation.ReflTransGen.head (h _ _ hadj) ih

private lemma l6f3_isRefl_iff {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (t : U ≃ₗ[ZMod p] U) : ZS.IsRefl p t ↔ GGLinRefl t := Iff.rfl

private lemma l6f3_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (w : ↥T) :
    ((ggLinRestrictHom T g w : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) w := by
  simp [ggLinRestrictHom]

private lemma l6f3_move_eq_span {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (a : V ≃ₗ[ZMod p] V) {c : V}
    {β : Module.Dual (ZMod p) V} (hβc : β c = 2) (hform : ∀ v, a v = v - β v • c) :
    ggLinMove a = Submodule.span (ZMod p) {c} := by
  have hβ0 : β ≠ 0 := by
    intro hzero
    rw [hzero] at hβc
    exact (zmod_two_ne_zero hp2) hβc.symm
  have hL : a.toLinearMap - LinearMap.id = (-β).smulRight c := by
    ext v
    change a v - v = (-β) v • c
    rw [hform v]
    simp only [LinearMap.neg_apply, neg_smul]
    abel
  rw [ggLinMove, hL, LinearMap.range_smulRight_apply (neg_ne_zero.mpr hβ0)]

private lemma l6f3_restrict_refl {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T))
    {c : V} (hcT : c ∈ T) {β : Module.Dual (ZMod p) V} (hβc : β c = 2)
    (hform : ∀ v, (g : V ≃ₗ[ZMod p] V) v = v - β v • c) :
    GGLinRefl (ggLinRestrictHom T g) := by
  have hform_t : ∀ w : ↥T, ggLinRestrictHom T g w =
      w - (β.comp T.subtype) w • (⟨c, hcT⟩ : ↥T) := by
    intro w
    apply Subtype.ext
    show ((ggLinRestrictHom T g w : ↥T) : V) =
      (w : V) - (β.comp T.subtype w) • c
    rw [l6f3_restrict_apply, hform]
    simp [LinearMap.comp_apply, Submodule.subtype_apply]
  have hβ'c' : (β.comp T.subtype) (⟨c, hcT⟩ : ↥T) = 2 := by
    simp [LinearMap.comp_apply, Submodule.subtype_apply, hβc]
  exact (ggDepA_linRefl_iff hp2 (ggLinRestrictHom T g)).mpr
    ⟨⟨c, hcT⟩, β.comp T.subtype, hβ'c', hform_t⟩

private structure L6f3Setup {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) where
  O : Type
  g : O → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))
  c : O → ↥(ggFixLineT r s)
  β : O → Module.Dual (ZMod p) ↥(ggFixLineT r s)
  hQ : ggFixLineQ S = Subgroup.closure (Set.range g)
  hrefl : ∀ o, ZS.IsRefl p (g o)
  hg : ∀ o w, g o w = w - β o w • c o
  hβ : ∀ o, β o (c o) = 2
  hspan : Submodule.span (ZMod p) (Set.range c) = ⊤
  hker : ∀ w, (∀ o, β o w = 0) → w = 0
  hconn : ∀ a b, Relation.ReflTransGen (fun a b => β a (c b) ≠ 0 ∧ β b (c a) ≠ 0) a b

private noncomputable def l6f3_setup {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : L6f3Setup S := by
  classical
  haveI : NeZero (N - 1) := ⟨by have h5 := S.five_le; omega⟩
  let O := Fin (N - 1) ⊕ ι
  let gV : O → (V ≃ₗ[ZMod p] V) := Sum.elim r s
  have hs_form : ∀ k : ι, ∃ (c : V) (β : Module.Dual (ZMod p) V),
      β c = 2 ∧ ∀ v, s k v = v - β v • c :=
    fun k => (ggDepA_linRefl_iff S.odd (s k)).mp (S.s_refl k)
  choose crootS βrootS hβcS hformS using hs_form
  let crootV : O → V := Sum.elim h crootS
  let βrootV : O → Module.Dual (ZMod p) V := Sum.elim α βrootS
  have hβcV : ∀ o, βrootV o (crootV o) = 2 := by
    intro o
    cases o with
    | inl i =>
      show α i (h i) = 2
      rw [S.pair i i]
      have hdiag : CartanMatrix.A (N - 1) i i = 2 := by
        simp [CartanMatrix.A, Matrix.of_apply]
      rw [hdiag]
      norm_num
    | inr k => exact hβcS k
  have hformV : ∀ o v, gV o v = v - βrootV o v • crootV o := by
    intro o v
    cases o with
    | inl i => exact S.r_form i v
    | inr k => exact hformS k v
  have hT : ggFixLineT r s = (⨆ i, ggLinMove (r i)) ⊔ ⨆ k, ggLinMove (s k) := by
    simp only [ggFixLineT]
  have hle_r : ∀ i, ggLinMove (r i) ≤ ggFixLineT r s := by
    intro i
    rw [hT]
    exact (le_iSup (fun i => ggLinMove (r i)) i).trans le_sup_left
  have hle_s : ∀ k, ggLinMove (s k) ≤ ggFixLineT r s := by
    intro k
    rw [hT]
    exact (le_iSup (fun k => ggLinMove (s k)) k).trans le_sup_right
  have hmove_r : ∀ i, ggLinMove (r i) =
      Submodule.span (ZMod p) {crootV (Sum.inl i)} := by
    intro i
    exact l6f3_move_eq_span S.odd (r i) (hβcV (Sum.inl i)) (hformV (Sum.inl i))
  have hmove_s : ∀ k, ggLinMove (s k) =
      Submodule.span (ZMod p) {crootV (Sum.inr k)} := by
    intro k
    exact l6f3_move_eq_span S.odd (s k) (hβcV (Sum.inr k)) (hformV (Sum.inr k))
  have hcrootV_mem : ∀ o, crootV o ∈ ggFixLineT r s := by
    intro o
    cases o with
    | inl i =>
      have h1 : crootV (Sum.inl i) ∈ ggLinMove (r i) := by
        rw [hmove_r i]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact hle_r i h1
    | inr k =>
      have h1 : crootV (Sum.inr k) ∈ ggLinMove (s k) := by
        rw [hmove_s k]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact hle_s k h1
  have hspan_range : Submodule.span (ZMod p) (Set.range crootV) = ggFixLineT r s := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨o, rfl⟩
      exact hcrootV_mem o
    · rw [hT]
      apply sup_le
      · apply iSup_le
        intro i
        rw [hmove_r i]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨Sum.inl i, rfl⟩)
      · apply iSup_le
        intro k
        rw [hmove_s k]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨Sum.inr k, rfl⟩)
  let cU : O → ↥(ggFixLineT r s) := fun o => ⟨crootV o, hcrootV_mem o⟩
  have hspanU : Submodule.span (ZMod p) (Set.range cU) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (ggFixLineT r s) hcrootV_mem).mpr hspan_range
  let βU : O → Module.Dual (ZMod p) ↥(ggFixLineT r s) :=
    fun o => (βrootV o).comp (ggFixLineT r s).subtype
  have hβU : ∀ o, βU o (cU o) = 2 := by
    intro o
    exact hβcV o
  let A := Subgroup.closure (Set.range r ∪ Set.range s)
  let F : ↥A →* (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    (ggLinRestrictHom (ggFixLineT r s)).comp
      (Subgroup.inclusion (ggFixLine_A_le_stab S))
  have hgenmem : ∀ o : O, gV o ∈ A := by
    intro o
    cases o with
    | inl i => exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
    | inr k => exact Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)
  let gen : O → ↥A := fun o => ⟨gV o, hgenmem o⟩
  let gU : O → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) := fun o => F (gen o)
  have hS0 : Subgroup.closure (((↑) : ↥A → V ≃ₗ[ZMod p] V) ⁻¹'
      (Set.range r ∪ Set.range s)) = ⊤ := Subgroup.closure_closure_coe_preimage
  have hgU_range : Set.range gU =
      F '' (((↑) : ↥A → V ≃ₗ[ZMod p] V) ⁻¹' (Set.range r ∪ Set.range s)) := by
    ext t
    constructor
    · rintro ⟨o, rfl⟩
      refine ⟨gen o, ?_, rfl⟩
      cases o with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr k => exact Or.inr ⟨k, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases ha with ⟨i, hi⟩ | ⟨k, hk⟩
      · refine ⟨Sum.inl i, ?_⟩
        apply congrArg F
        apply Subtype.ext
        show gV (Sum.inl i) = (a : V ≃ₗ[ZMod p] V)
        simpa [gV] using hi
      · refine ⟨Sum.inr k, ?_⟩
        apply congrArg F
        apply Subtype.ext
        show gV (Sum.inr k) = (a : V ≃ₗ[ZMod p] V)
        simpa [gV] using hk
  have hQ_closure : ggFixLineQ S = Subgroup.closure (Set.range gU) := by
    have hQeq : ggFixLineQ S = F.range := rfl
    rw [hQeq, MonoidHom.range_eq_map, ← hS0, MonoidHom.map_closure, hgU_range]
  have hreflU : ∀ o, ZS.IsRefl p (gU o) := by
    intro o
    refine (l6f3_isRefl_iff (gU o)).mpr ?_
    have hg : GGLinRefl (ggLinRestrictHom (ggFixLineT r s)
        ((Subgroup.inclusion (ggFixLine_A_le_stab S)) (gen o))) :=
      l6f3_restrict_refl S.odd (ggFixLineT r s)
        ((Subgroup.inclusion (ggFixLine_A_le_stab S)) (gen o))
        (hcrootV_mem o) (hβcV o) (hformV o)
    exact hg
  have hgU : ∀ o w, gU o w = w - βU o w • cU o := by
    intro o w
    have h1 : ((gU o) w : V) = (gV o) (w : V) := by
      have := l6f3_restrict_apply (ggFixLineT r s)
        ((Subgroup.inclusion (ggFixLine_A_le_stab S)) (gen o)) w
      simpa [gU, F, gen] using this
    apply Subtype.ext
    rw [h1, hformV o (w : V)]
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rfl
  have hkerU : ∀ w : ↥(ggFixLineT r s), (∀ o, βU o w = 0) → w = 0 := by
    intro w hw0
    have hfix : (w : V) ∈ ggLinFix (Set.range r ∪ Set.range s) := by
      intro a ha
      rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [S.r_form i (w : V)]
        have hzero : α i (w : V) = 0 := by
          have h := hw0 (Sum.inl i)
          simpa [βU, βrootV, LinearMap.comp_apply] using h
        rw [hzero, zero_smul, sub_zero]
      · rw [hformS k (w : V)]
        have hzero : βrootS k (w : V) = 0 := by
          have h := hw0 (Sum.inr k)
          simpa [βU, βrootV, LinearMap.comp_apply] using h
        rw [hzero, zero_smul, sub_zero]
    have hbot : (w : V) ∈ (⊥ : Submodule (ZMod p) V) := by
      rw [← ggFixLine_fix_A S]
      exact hfix
    exact Subtype.ext (by simpa using hbot)
  let R : O → O → Prop := fun a b => βU a (cU b) ≠ 0 ∧ βU b (cU a) ≠ 0
  have hneg1 : (-1 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]
    exact one_ne_zero
  have hA_succ : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) i j : ZMod p) = -1 := by
    intro i j hij
    have hne : i ≠ j := by
      intro hh
      have := congrArg Fin.val hh
      omega
    have hAi : CartanMatrix.A (N - 1) i j = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inl hij)]
    rw [hAi]
    norm_num
  have hA_succ' : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) j i : ZMod p) = -1 := by
    intro i j hij
    have hne : j ≠ i := by
      intro hh
      have := congrArg Fin.val hh
      omega
    have hAi : CartanMatrix.A (N - 1) j i = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inr hij)]
    rw [hAi]
    norm_num
  have hedge : ∀ i j : Fin (N - 1), i.val + 1 = j.val → R (Sum.inl i) (Sum.inl j) := by
    intro i j hij
    refine ⟨?_, ?_⟩
    · change α i (h j) ≠ 0
      rw [S.pair i j, hA_succ i j hij]
      exact hneg1
    · change α j (h i) ≠ 0
      rw [S.pair j i, hA_succ' i j hij]
      exact hneg1
  have hchain : ∀ j : Fin (N - 1),
      Relation.ReflTransGen R (Sum.inl (0 : Fin (N - 1))) (Sum.inl j) := by
    intro j
    refine Fin.strong_induction_on
      (motive := fun j => Relation.ReflTransGen R (Sum.inl (0 : Fin (N - 1))) (Sum.inl j)) ?_ j
    intro j ih
    by_cases hj : j = 0
    · subst hj
      exact Relation.ReflTransGen.refl
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hh => hj (Fin.ext hh))
      let j' : Fin (N - 1) := ⟨j.val - 1, by omega⟩
      have hlt : j' < j := by
        show j.val - 1 < j.val
        omega
      have hval : j'.val + 1 = j.val := by
        show j.val - 1 + 1 = j.val
        omega
      exact (ih j' hlt).tail (hedge j' j hval)
  have hpair_ss : ∀ a b : ι, s a * s b ≠ s b * s a →
      βrootS a (crootS b) ≠ 0 ∧ βrootS b (crootS a) ≠ 0 := by
    intro a b hne
    exact ggFixLine_noncomm_pairs S.odd (Subgroup.closure (Set.range r ∪ Set.range s))
      S.no_transvection
      (Subgroup.subset_closure (Or.inr ⟨a, rfl⟩))
      (Subgroup.subset_closure (Or.inr ⟨b, rfl⟩))
      (hformS a) (hformS b) (hβcS a) (hβcS b) hne
  have hH : ∀ k l : ι, Relation.ReflTransGen R (Sum.inr k) (Sum.inr l) := by
    intro k l
    have hstep : ∀ a b : ι,
        (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Adj a b →
        R (Sum.inr a) (Sum.inr b) := by
      intro a b hab
      rw [SimpleGraph.fromRel_adj] at hab
      rcases hab with ⟨_, hne | hne⟩
      · exact hpair_ss a b hne
      · exact ⟨(hpair_ss b a hne).2, (hpair_ss b a hne).1⟩
    rcases S.conn.preconnected k l with ⟨w⟩
    exact l6f3_walk_map (f := Sum.inr) hstep w
  choose k0 i0 hne0 using ggFixLine_cross_pair S
  have hcross : R (Sum.inr k0) (Sum.inl i0) := by
    have hpair := ggFixLine_noncomm_pairs S.odd
      (Subgroup.closure (Set.range r ∪ Set.range s)) S.no_transvection
      (Subgroup.subset_closure (Or.inr ⟨k0, rfl⟩))
      (Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩))
      (hformS k0) (S.r_form i0) (hβcS k0) (hβcV (Sum.inl i0)) hne0
    exact hpair
  haveI : Std.Symm R := ⟨fun a b hh => ⟨hh.2, hh.1⟩⟩
  have hsymm : ∀ {a b : O}, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a :=
    fun h => Std.Symm.symm _ _ h
  have hconnU : ∀ a b : O, Relation.ReflTransGen R a b := by
    intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (hsymm (hchain i)).trans (hchain j)
      | inr l =>
        exact (((hsymm (hchain i)).trans (hchain i0)).trans
          (Relation.ReflTransGen.single (⟨hcross.2, hcross.1⟩ : R (Sum.inl i0) (Sum.inr k0)))).trans
            (hH k0 l)
    | inr k =>
      cases b with
      | inl j =>
        exact hsymm ((((hsymm (hchain j)).trans (hchain i0)).trans
          (Relation.ReflTransGen.single (⟨hcross.2, hcross.1⟩ : R (Sum.inl i0) (Sum.inr k0)))).trans
            (hH k0 k))
      | inr l => exact hH k l
  exact ⟨O, gU, cU, βU, hQ_closure, hreflU, hgU, hβU, hspanU, hkerU, hconnU⟩

theorem ggFixLine_Q_reflGen {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : ZS.ReflGen p (ggFixLineQ S) := by
  have D := l6f3_setup S
  unfold ZS.ReflGen
  rw [D.hQ]
  apply le_antisymm
  · apply Subgroup.closure_mono
    intro t ht
    obtain ⟨o, rfl⟩ := ht
    exact ⟨Subgroup.subset_closure (Set.mem_range_self o), D.hrefl o⟩
  · rw [Subgroup.closure_le]
    intro t ht
    exact ht.1

theorem ggFixLine_Q_absIrred {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : ZS.AbsIrred p (ggFixLineQ S) := by
  have D := l6f3_setup S
  exact ggRC_absIrred_of_connected S.odd D.g D.c D.β D.hg D.hβ D.hspan D.hker D.hconn
    (ggFixLineQ S) D.hQ

end CFSG.StandardType

end
