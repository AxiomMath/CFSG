module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggK1Dp_map_filter_eq {α β : Type*} (l : List α) (g : α → β)
    (q : β → Bool) :
    (l.map g).filter q = (l.filter (fun a => q (g a))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.filter_cons, ih]
      split <;> rfl

private theorem ggK1Dp_finRange_map_ofFn {γ : Type} {n : ℕ} (f : Fin n → γ) :
    (List.finRange n).map f = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map, ih, List.ofFn_succ]
      rfl

private theorem ggK1Dp_ofFn_filter_map {γ : Type} {n : ℕ} (f : Fin n → γ) (p : γ → Bool) :
    ((List.finRange n).filter (fun k => p (f k))).map f = (List.ofFn f).filter p := by
  rw [← ggK1Dp_map_filter_eq (List.finRange n) f p, ggK1Dp_finRange_map_ofFn]

private theorem ggK1Dp_univ_subtype_map {α β : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (g : α → β) :
    (Finset.univ : Finset {x : α // p x}).val.map (fun x => g x.1) =
      (Finset.univ.filter p).val.map g := by
  rw [← Finset.subtype_univ p]
  rw [show (fun x : {x // p x} => g x.1) = g ∘ (Function.Embedding.subtype p) from rfl]
  rw [← Multiset.map_map]
  congr 1
  rw [← Finset.map_val, Finset.subtype_map]

private theorem ggK1Dp_subtype_fin_map_list {γ : Type} (l : List γ) (p : γ → Bool) :
    (Finset.univ : Finset {k : Fin l.length // p (l.get k) = true}).val.map
        (fun b => l.get b.1) = l.filter p := by
  rw [ggK1Dp_univ_subtype_map]
  rw [Finset.filter_val, Finset.val_univ_fin, Multiset.filter_coe]
  rw [show (fun k : Fin l.length => decide (p (l.get k) = true)) = (fun k => p (l.get k)) from by
    funext k; simp]
  rw [Multiset.map_coe, ggK1Dp_ofFn_filter_map (f := l.get) (p := p), List.ofFn_get]

private theorem ggK1Dp_subtype_fin_map {γ : Type} (l : List γ) (p : γ → Bool) :
    (Finset.univ : Finset {k : Fin l.length // p (l.get k) = true}).val.map
        (fun b => l.get b.1) = (l.filter p : Multiset γ) := by
  rw [ggK1Dp_subtype_fin_map_list]

private theorem ggK1Dp_card_fiber_eq_count {α γ : Type} [Fintype α] [DecidableEq γ]
    (f : α → γ) (c : γ) :
    Fintype.card {a : α // f a = c} = Multiset.count c ((Finset.univ : Finset α).val.map f) := by
  rw [Fintype.card_subtype, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro x _
  exact eq_comm

private theorem ggK1Dp_card_fin_filter (l : List GGKacOrbit) (c : GGKacOrbit) :
    Fintype.card {j : Fin l.length // (l.get j).qs = true ∧ l.get j = c}
      = Multiset.count c (l.filter (fun o => o.qs) : Multiset GGKacOrbit) := by
  classical
  have he : {j : Fin l.length // (l.get j).qs = true ∧ l.get j = c} ≃
      {j : {j : Fin l.length // (l.get j).qs = true} // l.get j.1 = c} :=
    ⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
     fun y => ⟨y.1.1, y.1.2, y.2⟩,
     fun x => rfl, fun y => rfl⟩
  rw [Fintype.card_congr he]
  rw [ggK1Dp_card_fiber_eq_count
        (f := fun j : {j : Fin l.length // (l.get j).qs = true} => l.get j.1) c]
  rw [ggK1Dp_subtype_fin_map l (fun o => o.qs)]

private theorem ggK1Dp_count_block {α : Type} [Fintype α]
    (g : α → List GGKacOrbit) (c : GGKacOrbit) :
    Multiset.count c ((Finset.univ : Finset {q : Σ i : α, Fin (g i).length //
        ((g q.1).get q.2).qs = true}).val.map (fun q => (g q.1.1).get q.1.2))
      = ∑ i : α, Multiset.count c ((g i).filter (fun b => b.qs) : Multiset GGKacOrbit) := by
  classical
  rw [← ggK1Dp_card_fiber_eq_count
        (f := fun q : {q : Σ i : α, Fin (g i).length //
          ((g q.1).get q.2).qs = true} => (g q.1.1).get q.1.2) c]
  have he : {q : {q : Σ i : α, Fin (g i).length //
        ((g q.1).get q.2).qs = true} // (g q.1.1).get q.1.2 = c} ≃
      (Σ i : α, {j : Fin (g i).length // ((g i).get j).qs = true ∧ (g i).get j = c}) :=
    ⟨fun x => ⟨x.1.1.1, ⟨x.1.1.2, x.1.2, x.2⟩⟩,
     fun y => ⟨⟨⟨y.1, y.2.1⟩, y.2.2.1⟩, y.2.2.2⟩,
     fun x => rfl, fun y => rfl⟩
  rw [Fintype.card_congr he, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact ggK1Dp_card_fin_filter (g i) c

private theorem ggK1Dp_bind_map {α β γ : Type} [DecidableEq γ]
    (m : Multiset α) (f : α → β) (F : β → Multiset γ) :
    m.bind (fun a => F (f a)) = (m.map f).bind F := by
  apply Multiset.ext'
  intro c
  rw [Multiset.count_bind, Multiset.count_bind, Multiset.map_map]
  rfl

private theorem ggK1Dp_flatten_filter_eq {α β : Type} (l : List α) (f : α → Bool)
    (g : α → List β) (hg : ∀ a, f a = false → g a = []) :
    ((l.filter f).map g).flatten = (l.map g).flatten := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filter_cons]
      by_cases ha : f a = true
      · rw [if_pos ha, List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons, ih]
      · have haf : f a = false := by
          cases hfa : f a with
          | false => rfl
          | true => exact absurd hfa ha
        rw [if_neg (by simp [ha]), ih, List.map_cons, List.flatten_cons, hg a haf]
        rfl

private theorem ggK1Dp_hasOrbit_false (nf : ℕ) (k : ggK1DCo_Kind) :
    ggK1DCo_Kind.hasOrbit k = false →
      (ggK1DCo_kindOrbits nf k).filter (fun o => o.qs) = [] := by
  intro h
  cases k with
  | om eps m =>
      simp only [ggK1DCo_Kind.hasOrbit] at h
      rw [decide_eq_false_iff_not] at h
      have hm : m ≤ 1 := by omega
      simp [ggK1DCo_kindOrbits, hm, ggK1DCo_dummyOrbit]
  | sl m =>
      simp only [ggK1DCo_Kind.hasOrbit] at h
      rw [decide_eq_false_iff_not] at h
      have hm : m ≤ 1 := by omega
      simp [ggK1DCo_kindOrbits, hm, ggK1DCo_dummyOrbit]
  | su m =>
      simp only [ggK1DCo_Kind.hasOrbit] at h
      rw [decide_eq_false_iff_not] at h
      have hm : m ≤ 1 := by omega
      simp [ggK1DCo_kindOrbits, hm, ggK1DCo_dummyOrbit]

theorem ggK1DCo_pos_equiv {nf : ℕ} {ι : Type} [Fintype ι] (kind : ι → ggK1DCo_Kind)
    (L : List ggK1DCo_Kind) (O : List GGKacOrbit)
    (hmult : (Finset.univ : Finset ι).val.map kind = (L : Multiset ggK1DCo_Kind))
    (hO : ((L.filter (fun k => ggK1DCo_Kind.hasOrbit k)).map
      (ggK1DCo_kindOrbits nf)).flatten = O) :
    ∃ g : {q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length //
          ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true} ≃
        {k : Fin O.length // (O.get k).qs = true},
      ∀ q, O.get (g q).1 = (ggK1DCo_kindOrbits nf (kind q.1.1)).get q.1.2 := by
  classical
  let BlockSub : Type := {q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length //
      ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true}
  let OSub : Type := {k : Fin O.length // (O.get k).qs = true}
  let f : BlockSub → GGKacOrbit :=
    fun q => (ggK1DCo_kindOrbits nf (kind q.1.1)).get q.1.2
  let ob : OSub → GGKacOrbit := fun b => O.get b.1
  let gL : ggK1DCo_Kind → List GGKacOrbit :=
    fun k => (ggK1DCo_kindOrbits nf k).filter (fun o => o.qs)
  let A : List GGKacOrbit := (L.map gL).flatten
  have hcount : ∀ c : GGKacOrbit,
      Multiset.count c ((Finset.univ : Finset BlockSub).val.map f)
        = Multiset.count c ((Finset.univ : Finset OSub).val.map ob) := by
    intro c
    have hblock : Multiset.count c ((Finset.univ : Finset BlockSub).val.map f)
        = ∑ i : ι, Multiset.count c ((gL (kind i)) : Multiset GGKacOrbit) := by
      change Multiset.count c ((Finset.univ : Finset {q : Σ i : ι,
          Fin (ggK1DCo_kindOrbits nf (kind i)).length //
          ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true}).val.map
            (fun q => (ggK1DCo_kindOrbits nf (kind q.1.1)).get q.1.2))
        = ∑ i : ι, Multiset.count c ((gL (kind i)) : Multiset GGKacOrbit)
      rw [ggK1Dp_count_block (g := fun i => ggK1DCo_kindOrbits nf (kind i)) c]
    have hsum : (∑ i : ι, Multiset.count c ((gL (kind i)) : Multiset GGKacOrbit))
        = Multiset.count c ((A : List GGKacOrbit) : Multiset GGKacOrbit) := by
      change (Multiset.map (fun i : ι => Multiset.count c ((gL (kind i)) : Multiset GGKacOrbit))
          (Finset.univ : Finset ι).val).sum
        = Multiset.count c ((A : List GGKacOrbit) : Multiset GGKacOrbit)
      rw [← Multiset.count_bind]
      rw [ggK1Dp_bind_map (m := (Finset.univ : Finset ι).val) (f := kind)
            (F := fun k => (gL k : Multiset GGKacOrbit))]
      rw [hmult, Multiset.coe_bind]
      rfl
    have hO' : List.filter (fun o => o.qs) O = A := by
      rw [← hO, List.filter_flatten]
      rw [List.map_map]
      exact ggK1Dp_flatten_filter_eq L (fun k => ggK1DCo_Kind.hasOrbit k) gL
        (fun k => ggK1Dp_hasOrbit_false nf k)
    have hob : Multiset.count c ((Finset.univ : Finset OSub).val.map ob)
        = Multiset.count c ((A : List GGKacOrbit) : Multiset GGKacOrbit) := by
      change Multiset.count c ((Finset.univ :
          Finset {k : Fin O.length // (fun o : GGKacOrbit => o.qs) (O.get k) = true}).val.map
            (fun b => O.get b.1))
        = Multiset.count c ((A : List GGKacOrbit) : Multiset GGKacOrbit)
      rw [ggK1Dp_subtype_fin_map O (fun o => o.qs), hO']
    rw [hblock, hsum, hob]
  let E : ∀ c, {a // f a = c} ≃ {b // ob b = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [ggK1Dp_card_fiber_eq_count (f := f), ggK1Dp_card_fiber_eq_count (f := ob),
        hcount c])
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := ob) E, ?_⟩
  intro a
  exact Equiv.ofFiberEquiv_map (f := f) (g := ob) (e := E) a

end CFSG.StandardType

end
