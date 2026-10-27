module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggK1CPo_map_filter_eq {α β : Type*} (l : List α) (g : α → β)
    (q : β → Bool) :
    (l.map g).filter q = (l.filter (fun a => q (g a))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.filter_cons, ih]
      split <;> rfl

private theorem ggK1CPo_finRange_map_ofFn {γ : Type} {n : ℕ} (f : Fin n → γ) :
    (List.finRange n).map f = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map, ih, List.ofFn_succ]
      rfl

private theorem ggK1CPo_ofFn_filter_map {γ : Type} {n : ℕ} (f : Fin n → γ) (p : γ → Bool) :
    ((List.finRange n).filter (fun k => p (f k))).map f = (List.ofFn f).filter p := by
  rw [← ggK1CPo_map_filter_eq (List.finRange n) f p, ggK1CPo_finRange_map_ofFn]

private theorem ggK1CPo_univ_subtype_map {α β : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (g : α → β) :
    (Finset.univ : Finset {x : α // p x}).val.map (fun x => g x.1) =
      (Finset.univ.filter p).val.map g := by
  rw [← Finset.subtype_univ p]
  rw [show (fun x : {x // p x} => g x.1) = g ∘ (Function.Embedding.subtype p) from rfl]
  rw [← Multiset.map_map]
  congr 1
  rw [← Finset.map_val, Finset.subtype_map]

private theorem ggK1CPo_subtype_fin_map_list {γ : Type} (l : List γ) (p : γ → Bool) :
    (Finset.univ : Finset {k : Fin l.length // p (l.get k) = true}).val.map
        (fun b => l.get b.1) = l.filter p := by
  rw [ggK1CPo_univ_subtype_map]
  rw [Finset.filter_val, Finset.val_univ_fin, Multiset.filter_coe]
  rw [show (fun k : Fin l.length => decide (p (l.get k) = true)) = (fun k => p (l.get k)) from by
    funext k; simp]
  rw [Multiset.map_coe, ggK1CPo_ofFn_filter_map (f := l.get) (p := p), List.ofFn_get]

private theorem ggK1CPo_subtype_fin_map {γ : Type} (l : List γ) (p : γ → Bool) :
    (Finset.univ : Finset {k : Fin l.length // p (l.get k) = true}).val.map
        (fun b => l.get b.1) = (l.filter p : Multiset γ) := by
  rw [ggK1CPo_subtype_fin_map_list]

private theorem ggK1CPo_qs_hasOrbit (nf : ℕ) (k : ggK1CCo_Kind) :
    (ggK1CCo_kindOrbit nf k).qs = true → ggK1CCo_Kind.hasOrbit k = true := by
  intro h
  cases k with
  | sp s => rfl
  | sl m =>
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => simp [ggK1CCo_kindOrbit, ggK1CCo_Kind.hasOrbit] at h
          | succ m => rfl
  | su m =>
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => simp [ggK1CCo_kindOrbit, ggK1CCo_Kind.hasOrbit] at h
          | succ m => rfl

private theorem ggK1CPo_card_fiber_eq_count {α γ : Type} [Fintype α] [DecidableEq γ]
    (f : α → γ) (c : γ) :
    Fintype.card {a : α // f a = c} = Multiset.count c ((Finset.univ : Finset α).val.map f) := by
  rw [Fintype.card_subtype, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro x _
  exact eq_comm

private theorem ggK1CPo_Malpha {nf : ℕ} {ι : Type} [Fintype ι] (kind : ι → ggK1CCo_Kind)
    (L : List ggK1CCo_Kind)
    (hmult : (Finset.univ : Finset ι).val.map kind = (L : Multiset ggK1CCo_Kind)) :
    (Finset.univ : Finset {i : ι // (ggK1CCo_kindOrbit nf (kind i)).qs = true}).val.map
        (fun a => ggK1CCo_kindOrbit nf (kind a.1))
      = ((L.filter (fun k => (ggK1CCo_kindOrbit nf k).qs)).map
          (ggK1CCo_kindOrbit nf) : Multiset GGKacOrbit) := by
  rw [ggK1CPo_univ_subtype_map (p := fun i : ι => (ggK1CCo_kindOrbit nf (kind i)).qs = true)
        (g := fun i => ggK1CCo_kindOrbit nf (kind i))]
  rw [Finset.filter_val]
  have hP : Multiset.filter (fun i : ι => (ggK1CCo_kindOrbit nf (kind i)).qs = true)
        (Finset.univ : Finset ι).val
      = Multiset.filter ((fun o : GGKacOrbit => o.qs = true) ∘
          (fun i => ggK1CCo_kindOrbit nf (kind i)))
        (Finset.univ : Finset ι).val := by
    apply Multiset.filter_congr; intro x _; rfl
  rw [hP, ← Multiset.filter_map]
  congr 1
  rw [show (fun i => ggK1CCo_kindOrbit nf (kind i))
        = (ggK1CCo_kindOrbit nf) ∘ kind from rfl]
  rw [← Multiset.map_map, hmult]
  rw [Multiset.filter_map]
  congr 1

private theorem ggK1CPo_Mbeta {nf : ℕ} (L : List ggK1CCo_Kind) (O : List GGKacOrbit)
    (hO : (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) = O) :
    (Finset.univ : Finset {k : Fin O.length // O[k].qs = true}).val.map (fun b => O[b.1])
      = ((L.filter (fun k => (ggK1CCo_kindOrbit nf k).qs)).map
          (ggK1CCo_kindOrbit nf) : Multiset GGKacOrbit) := by
  change (Finset.univ :
      Finset {k : Fin O.length // (fun o : GGKacOrbit => o.qs) (O.get k) = true}).val.map
      (fun b => O.get b.1) = ((L.filter (fun k => (ggK1CCo_kindOrbit nf k).qs)).map
          (ggK1CCo_kindOrbit nf) : Multiset GGKacOrbit)
  rw [ggK1CPo_subtype_fin_map O (fun o => o.qs)]
  rw [← hO]
  rw [ggK1CPo_map_filter_eq (L.filter (fun k => ggK1CCo_Kind.hasOrbit k))
        (ggK1CCo_kindOrbit nf) (fun o => o.qs)]
  have hfil : (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).filter
        (fun k => (ggK1CCo_kindOrbit nf k).qs)
      = L.filter (fun k => (ggK1CCo_kindOrbit nf k).qs) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    cases hx : (ggK1CCo_kindOrbit nf x).qs with
    | false => simp [hx]
    | true => simp [hx, ggK1CPo_qs_hasOrbit nf x hx]
  rw [hfil]

theorem ggK1CCo_pos_equiv {nf : ℕ} {ι : Type} [Fintype ι] (kind : ι → ggK1CCo_Kind)
    (L : List ggK1CCo_Kind) (O : List GGKacOrbit)
    (hmult : (Finset.univ : Finset ι).val.map kind = (L : Multiset ggK1CCo_Kind))
    (hO : (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) = O) :
    ∃ g : {i : ι // (ggK1CCo_kindOrbit nf (kind i)).qs = true} ≃
        {k : Fin O.length // O[k].qs = true},
      ∀ i, O[(g i).1] = ggK1CCo_kindOrbit nf (kind i.1) := by
  have hα := ggK1CPo_Malpha (nf := nf) kind L hmult
  have hβ := ggK1CPo_Mbeta (nf := nf) L O hO
  let f : {i : ι // (ggK1CCo_kindOrbit nf (kind i)).qs = true} → GGKacOrbit :=
    fun a => ggK1CCo_kindOrbit nf (kind a.1)
  let g : {k : Fin O.length // O[k].qs = true} → GGKacOrbit := fun b => O[b.1]
  let E : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [ggK1CPo_card_fiber_eq_count (f := f), ggK1CPo_card_fiber_eq_count (f := g), hα, hβ])
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := g) E, ?_⟩
  intro a
  exact Equiv.ofFiberEquiv_map (f := f) (g := g) (e := E) a


end CFSG.StandardType

end
