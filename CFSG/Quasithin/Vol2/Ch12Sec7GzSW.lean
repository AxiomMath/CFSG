module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBrS
public import Certificates.Data.S1277Surv

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Sig Certificates.Data.S1277Surv
  Certificates.Data.S1277Bfs Std

theorem unpackC_packC (cols : List Nat) (hlen : cols.length = 6) (hlt : ∀ c ∈ cols, c < 64) :
    unpackC 6 (packC cols) = cols := by
  match cols, hlen with
  | [a, b, c, d, e, f], _ =>
    have ha : a < 64 := hlt a (by simp)
    have hb : b < 64 := hlt b (by simp)
    have hc : c < 64 := hlt c (by simp)
    have hd : d < 64 := hlt d (by simp)
    have he : e < 64 := hlt e (by simp)
    have hf : f < 64 := hlt f (by simp)
    simp [unpackC, packC, List.range_succ]
    omega

theorem packC_injective (c₁ c₂ : List Nat) (h1 : c₁.length = 6) (h2 : c₂.length = 6)
    (hl1 : ∀ c ∈ c₁, c < 64) (hl2 : ∀ c ∈ c₂, c < 64) (h : packC c₁ = packC c₂) : c₁ = c₂ := by
  rw [← unpackC_packC c₁ h1 hl1, ← unpackC_packC c₂ h2 hl2, h]

theorem app6_eq (x v : Nat) : app6 x v = applyCols (unpackC 6 x) v := by
  simp [app6, unpackC, List.range_succ, applyCols, Nat.div_div_eq_div_mul]

theorem mulS_eq (x y : Nat) : mulS x y = mulSSpec x y := by
  unfold mulS mulSSpec packC compCols
  simp only [app6_eq]
  simp [unpackC, List.range_succ, Nat.div_div_eq_div_mul]

@[expose] noncomputable def pk (σ : Equiv.Perm (Fin (2 ^ 6))) : Nat := packC (colsOf σ)

theorem pk_def (σ : Equiv.Perm (Fin (2 ^ 6))) : pk σ = packC (colsOf σ) := rfl

theorem colsOf_lt (σ : Equiv.Perm (Fin (2 ^ 6))) : ∀ c ∈ colsOf σ, c < 64 := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < 6 := by simpa [length_colsOf] using hi
  rw [getElem_colsOf σ i hi']
  exact (σ _).2

theorem unpackC_pk (σ : Equiv.Perm (Fin (2 ^ 6))) : unpackC 6 (pk σ) = colsOf σ :=
  unpackC_packC _ (length_colsOf σ) (colsOf_lt σ)

theorem pk_mul {σ : Equiv.Perm (Fin (2 ^ 6))}
    (hσ : ∀ a b c : Fin (2 ^ 6), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1)
    (τ : Equiv.Perm (Fin (2 ^ 6))) : pk (σ * τ) = mulS (pk σ) (pk τ) := by
  rw [mulS_eq]
  unfold mulSSpec
  rw [unpackC_pk, unpackC_pk]
  show packC (colsOf (σ * τ)) = packC (compCols (colsOf σ) (colsOf τ))
  rw [colsOf_mul hσ]

theorem pk_one : pk (1 : Equiv.Perm (Fin (2 ^ 6))) = oneS := by
  unfold pk
  rw [colsOf_one]
  rfl

theorem pk_injective {φ : Nat → Nat} {σ τ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (hτ : τ ∈ Sig 6 φ) (h : pk σ = pk τ) : σ = τ :=
  colsOf_injective hσ hτ (packC_injective _ _ (length_colsOf σ) (length_colsOf τ)
    (colsOf_lt σ) (colsOf_lt τ) h)


section Lattice

variable {φ : Nat → Nat}

abbrev pkSet (R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))) (y : Nat) : Prop := ∃ r ∈ R, pk r = y

theorem pkSet_mul {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {x y : Nat}
    (hx : pkSet R x) (hy : pkSet R y) : pkSet R (mulS x y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  exact ⟨r * r', R.mul_mem hr hr', pk_mul (hR hr).1 r'⟩

theorem pkSet_one {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} : pkSet R oneS :=
  ⟨1, R.one_mem, pk_one⟩

theorem card_le_of_pkSet {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ)
    (l : List Nat) (hnd : l.Nodup) (hl : ∀ y ∈ l, pkSet R y) : l.length ≤ Nat.card R := by
  classical
  let f : {y // y ∈ l} → R := fun y => ⟨(hl y.1 y.2).choose, (hl y.1 y.2).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun r : R => pk r.1) hab
    simp only [f] at this
    rw [(hl a.1 a.2).choose_spec.2, (hl b.1 b.2).choose_spec.2] at this
    exact this
  have h1 := Nat.card_le_card_of_injective f hf
  have e2 : {y // y ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rwa [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd] at h1

theorem nodeValidW_spec {cap : Nat} {N : Node} (h : nodeValidW cap N = true) :
    (∀ g ∈ N.gens, g ∈ N.elems) ∧ ∀ P : Nat → Prop, P oneS → (∀ g ∈ N.gens, P g) →
      (∀ g ∈ N.gens, ∀ y, P y → P (mulS y g)) → ∀ e ∈ N.elems, P e := by
  unfold nodeValidW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, hel⟩, hsub⟩ := h
  refine ⟨(subsetL_iff _ _).1 hsub, fun P hone hgen hmul e he => ?_⟩
  rw [hel, mem_sortSet] at he
  unfold closW at he
  refine bfs_inv P _ ?_ (oneS :: N.gens) ?_ _ e he
  · intro f hf x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact hmul g hg x hx
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hone
    · exact hgen x hx

theorem oneS_mem_of_valid {cap : Nat} {N : Node} (h : nodeValidW cap N = true) : oneS ∈ N.elems := by
  unfold nodeValidW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, hel⟩, -⟩ := h
  rw [hel, mem_sortSet]
  exact mem_bfs_of_mem _ List.mem_cons_self _

theorem nodeValidW_nodup {cap : Nat} {N : Node} (h : nodeValidW cap N = true) : N.elems.Nodup := by
  unfold nodeValidW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, hel⟩, -⟩ := h
  rw [hel]
  exact sortSet_nodup _

abbrev InSigma (φ : Nat → Nat) (y : Nat) : Prop := ∃ σ ∈ Sig 6 φ, pk σ = y

theorem inSigma_one : InSigma φ oneS := ⟨1, (Sig 6 φ).one_mem, pk_one⟩

theorem pkSet_of_mul {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {s c : Nat}
    (hs : pkSet R s) (hc : InSigma φ c) (hsc : pkSet R (mulS s c)) : pkSet R c := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨τ, hτ, rfl⟩ := hc
  obtain ⟨ρ, hρ, hρe⟩ := hsc
  have h1 : pk ρ = pk (σ * τ) := by rw [hρe, pk_mul (hR hσ).1 τ]
  have h2 : ρ = σ * τ := pk_injective (hR hρ) ((Sig 6 φ).mul_mem (hR hσ) hτ) h1
  have h3 : τ = σ⁻¹ * ρ := by rw [h2]; group
  exact ⟨τ, by rw [h3]; exact R.mul_mem (R.inv_mem hσ) hρ, rfl⟩

theorem mulS_cancel {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {s s' c : Nat}
    (hs : pkSet R s) (hs' : pkSet R s') (hc : InSigma φ c) (h : mulS s c = mulS s' c) : s = s' := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨σ', hσ', rfl⟩ := hs'
  obtain ⟨τ, hτ, rfl⟩ := hc
  rw [← pk_mul (hR hσ).1, ← pk_mul (hR hσ').1] at h
  have h2 := pk_injective ((Sig 6 φ).mul_mem (hR hσ) hτ) ((Sig 6 φ).mul_mem (hR hσ') hτ) h
  rw [mul_right_cancel h2]

theorem mulS_one_right {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {s : Nat}
    (hs : pkSet R s) : mulS s oneS = s := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  rw [← pk_one, ← pk_mul (hR hσ).1, mul_one]

theorem mulS_one_left {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {s : Nat}
    (hs : pkSet R s) : mulS oneS s = s := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  rw [← pk_one, ← pk_mul (Sig 6 φ).one_mem.1, one_mul]

abbrev CtInv (S : Node) (sigP : List Nat) (st : HashMap Nat Nat × List Nat) : Prop :=
  (∀ y, st.1.contains y = true →
    (∃ s ∈ S.elems, y = mulS s (st.1.getD y 0)) ∧ st.1.getD y 0 ∈ st.2) ∧
  ∀ r ∈ st.2, r = oneS ∨ r ∈ sigP

theorem ctInner (S : Node) (x : Nat) (reps : List Nat) (hx : x ∈ reps) :
    ∀ (l : List Nat), (∀ s ∈ l, s ∈ S.elems) → ∀ (t : HashMap Nat Nat),
      (∀ y, t.contains y = true →
        (∃ s ∈ S.elems, y = mulS s (t.getD y 0)) ∧ t.getD y 0 ∈ reps) →
      ∀ y, (l.foldl (fun t s => t.insert (mulS s x) x) t).contains y = true →
        (∃ s ∈ S.elems, y = mulS s ((l.foldl (fun t s => t.insert (mulS s x) x) t).getD y 0)) ∧
          (l.foldl (fun t s => t.insert (mulS s x) x) t).getD y 0 ∈ reps := by
  intro l
  induction l with
  | nil => intro _ t ht y hy; exact ht y hy
  | cons a l ih =>
    intro hl t ht
    simp only [List.foldl_cons]
    apply ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))
    intro y hy
    rw [HashMap.contains_insert, Bool.or_eq_true] at hy
    by_cases hky : (mulS a x == y) = true
    · have hyeq : mulS a x = y := beq_iff_eq.1 hky
      subst hyeq
      rw [HashMap.getD_insert_self]
      exact ⟨⟨a, hl a List.mem_cons_self, rfl⟩, hx⟩
    · have hky' : (mulS a x == y) = false := by simpa using hky
      have hy' : t.contains y = true := by
        rcases hy with h | h
        · exact absurd h hky
        · exact h
      rw [HashMap.getD_insert]
      simp only [hky', Bool.false_eq_true, if_false]
      exact ht y hy'

theorem ctOuter (S : Node) (sigP : List Nat) :
    ∀ (l : List Nat), (∀ x ∈ l, x = oneS ∨ x ∈ sigP) → ∀ (st : HashMap Nat Nat × List Nat),
      CtInv S sigP st → CtInv S sigP (l.foldl (fun (st : HashMap Nat Nat × List Nat) x =>
        if st.1.contains x then st
        else (S.elems.foldl (fun t s => t.insert (mulS s x) x) st.1, x :: st.2)) st) := by
  intro l
  induction l with
  | nil => intro _ st h; exact h
  | cons x l ih =>
    intro hl st hst
    simp only [List.foldl_cons]
    apply ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    split_ifs with hc
    · exact hst
    · obtain ⟨h1, h2⟩ := hst
      refine ⟨fun y hy => ?_, fun r hr => ?_⟩
      · exact ctInner S x (x :: st.2) List.mem_cons_self S.elems (fun s hs => hs) st.1
          (fun y hy => ⟨(h1 y hy).1, List.mem_cons_of_mem _ (h1 y hy).2⟩) y hy
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact hl r List.mem_cons_self
        · exact h2 r hr

theorem ctMono (S : Node) :
    ∀ (l : List Nat) (st : HashMap Nat Nat × List Nat), ∀ r ∈ st.2,
      r ∈ (l.foldl (fun (st : HashMap Nat Nat × List Nat) x =>
        if st.1.contains x then st
        else (S.elems.foldl (fun t s => t.insert (mulS s x) x) st.1, x :: st.2)) st).2 := by
  intro l
  induction l with
  | nil => intro st r hr; exact hr
  | cons x l ih =>
    intro st r hr
    simp only [List.foldl_cons]
    apply ih
    split_ifs with hc
    · exact hr
    · exact List.mem_cons_of_mem _ hr

theorem cosetTab_spec (S : Node) (sigP : List Nat) :
    (∀ y, (cosetTab S sigP).1.contains y = true →
      ∃ s ∈ S.elems, y = mulS s ((cosetTab S sigP).1.getD y 0)) ∧
    (∀ y, (cosetTab S sigP).1.contains y = true →
      (cosetTab S sigP).1.getD y 0 ∈ (cosetTab S sigP).2) ∧
    (∀ r ∈ (cosetTab S sigP).2, r = oneS ∨ r ∈ sigP) ∧ oneS ∈ (cosetTab S sigP).2 := by
  have hinit : CtInv S sigP ((∅ : HashMap Nat Nat), ([] : List Nat)) :=
    ⟨fun y hy => by simp at hy, fun r hr => by simp at hr⟩
  have h := ctOuter S sigP (oneS :: sigP) (fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr hx) _ hinit
  refine ⟨fun y hy => (h.1 y hy).1, fun y hy => (h.1 y hy).2, h.2, ?_⟩
  show oneS ∈ ((oneS :: sigP).foldl _ ((∅ : HashMap Nat Nat), ([] : List Nat))).2
  simp only [List.foldl_cons]
  have hc : ((∅ : HashMap Nat Nat)).contains oneS = false := by simp
  rw [if_neg (by simp [hc])]
  exact ctMono S sigP _ oneS List.mem_cons_self

theorem mem_cosetUnion (S : Node) (O : HashSet Nat) (y : Nat) :
    y ∈ cosetUnion S O ↔ ∃ c ∈ O, ∃ s ∈ S.elems, y = mulS s c := by
  have inner : ∀ (c : Nat) (l : List Nat) (acc : HashSet Nat), y ∈ l.foldl (fun a' s => a'.insert (mulS s c)) acc ↔
      y ∈ acc ∨ ∃ s ∈ l, y = mulS s c := by
    intro c l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, HashSet.mem_insert]
      simp only [beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨s, hs, hy⟩)
        · exact Or.inr ⟨a, Or.inl rfl, h.symm⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, Or.inr hs, hy⟩
      · rintro (h | ⟨s, hs | hs, hy⟩)
        · exact Or.inl (Or.inr h)
        · subst hs; exact Or.inl (Or.inl hy.symm)
        · exact Or.inr ⟨s, hs, hy⟩
  have outer : ∀ (cs : List Nat) (acc : HashSet Nat), y ∈ cs.foldl (fun a c =>
      S.elems.foldl (fun a' s => a'.insert (mulS s c)) a) acc ↔
      y ∈ acc ∨ ∃ c ∈ cs, ∃ s ∈ S.elems, y = mulS s c := by
    intro cs
    induction cs with
    | nil => intro acc; simp
    | cons c cs ih =>
      intro acc
      rw [List.foldl_cons, ih, inner]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | ⟨s, hs, hy⟩) | ⟨c', hc', s, hs, hy⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, Or.inl rfl, s, hs, hy⟩
        · exact Or.inr ⟨c', Or.inr hc', s, hs, hy⟩
      · rintro (h | ⟨c', hc' | hc', s, hs, hy⟩)
        · exact Or.inl (Or.inl h)
        · subst hc'; exact Or.inl (Or.inr ⟨s, hs, hy⟩)
        · exact Or.inr ⟨c', hc', s, hs, hy⟩
  unfold cosetUnion
  rw [outer]
  have hempty : y ∉ (∅ : HashSet Nat) := by simp
  constructor
  · rintro (h | ⟨c, hc, s, hs, hy⟩)
    · exact absurd h hempty
    · exact ⟨c, HashSet.mem_toList.1 hc, s, hs, hy⟩
  · rintro ⟨c, hc, s, hs, hy⟩
    exact Or.inr ⟨c, HashSet.mem_toList.2 hc, s, hs, hy⟩

theorem pushNew_mem' (seen : HashSet ℕ) (q : List ℕ) (y : ℕ) : y ∈ (pushNew seen q y).2 := by
  unfold pushNew
  split_ifs with h
  · exact HashSet.contains_iff_mem.1 h
  · rw [HashSet.mem_insert]
    exact Or.inl (beq_self_eq_true y)

theorem expand_mem_aux (moves : List (ℕ → ℕ)) (x : ℕ) {f : ℕ → ℕ} :
    ∀ (ms : List (ℕ → ℕ)) (q : List ℕ) (seen : HashSet ℕ), f ∈ ms →
      f x ∈ (ms.foldl (fun acc g => pushNew acc.2 acc.1 (g x)) (q, seen)).2 := by
  intro ms
  induction ms with
  | nil => intro q seen h; simp at h
  | cons g ms ih =>
    intro q seen h
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact expand_mono moves x ms _ _ _ (pushNew_mem' seen q _)
    · exact ih _ _ h

theorem move_mem_bfs (moves : List (ℕ → ℕ)) (c₀ n : ℕ) {f : ℕ → ℕ} (hf : f ∈ moves) :
    f c₀ ∈ bfs moves [c₀] (n + 1) := by
  unfold bfs
  simp only [bfsAux]
  exact bfsAux_mono moves n _ _ _ (expand_mem_aux moves c₀ moves [] _ hf)

theorem big_orbit_false {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {S : Node}
    (hSnd : S.elems.Nodup) (hSR : ∀ y ∈ S.elems, pkSet R y) {tab : HashMap Nat Nat}
    {reps : List Nat} (hrsig : ∀ c ∈ reps, InSigma φ c)
    (hcons : ∀ c ∈ reps, ∀ s ∈ S.elems, tab.getD (mulS s c) 0 = c) {O : HashSet Nat}
    (hO : ∀ c ∈ O, pkSet R c ∧ c ∈ reps) {cap : Nat} (hcap : Nat.card R ≤ cap)
    (hpos : 0 < S.elems.length) (hbig : cap / S.elems.length < O.size) : False := by
  classical
  have hOnd : O.toList.Nodup := by
    have := HashSet.distinct_toList (m := O)
    exact List.Pairwise.imp (fun h => by simpa using h) this
  have hlnd : (S.elems ×ˢ O.toList).Nodup := hSnd.product hOnd
  have hLnd : ((S.elems ×ˢ O.toList).map (fun p => mulS p.1 p.2)).Nodup := by
    refine List.Nodup.map_on (fun p hp q hq hpq => ?_) hlnd
    obtain ⟨hp1, hp2⟩ := List.mem_product.1 hp
    obtain ⟨hq1, hq2⟩ := List.mem_product.1 hq
    have hp2' := (hO p.2 (HashSet.mem_toList.1 hp2)).2
    have hq2' := (hO q.2 (HashSet.mem_toList.1 hq2)).2
    have hc1 := hcons p.2 hp2' p.1 hp1
    have hc2 := hcons q.2 hq2' q.1 hq1
    have hcc : p.2 = q.2 := by rw [← hc1, ← hc2, hpq]
    have hss : p.1 = q.1 := by
      apply mulS_cancel hR (hSR p.1 hp1) (hSR q.1 hq1) (hrsig p.2 hp2')
      rw [hpq, hcc]
    exact Prod.ext hss hcc
  have hLR : ∀ y ∈ (S.elems ×ˢ O.toList).map (fun p => mulS p.1 p.2), pkSet R y := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hp1, hp2⟩ := List.mem_product.1 hp
    exact pkSet_mul hR (hSR p.1 hp1) (hO p.2 (HashSet.mem_toList.1 hp2)).1
  have hlen := card_le_of_pkSet hR _ hLnd hLR
  rw [List.length_map, List.length_product, HashSet.length_toList] at hlen
  have h1 : cap < S.elems.length * (cap / S.elems.length + 1) := Nat.lt_mul_div_succ cap hpos
  have h2 : S.elems.length * (cap / S.elems.length + 1) ≤ S.elems.length * O.size :=
    Nat.mul_le_mul_left _ hbig
  omega

theorem lattice_complete {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ)
    {cap : Nat} (hcap : Nat.card R ≤ cap) {sigP : List Nat}
    (hsigP1 : ∀ σ ∈ Sig 6 φ, pk σ ∈ sigP) (hsigP2 : ∀ y ∈ sigP, ∃ σ ∈ Sig 6 φ, pk σ = y)
    {nodes : List Node} {S0 : Node} (hlat : latOK cap sigP nodes S0 = true)
    (hS0 : ∀ y ∈ S0.elems, pkSet R y) :
    ∃ S ∈ nodes, ∀ y, pkSet R y ↔ y ∈ S.elems := by
  classical
  unfold latOK at hlat
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hlat
  obtain ⟨⟨S0', hS0'mem, hS0'eq⟩, hnodes⟩ := hlat
  have key : ∀ l : List Nat, (∀ x ∈ l, pkSet R x ∧ x ∈ sigP) →
      ∃ S ∈ nodes, (∀ x ∈ l, x ∈ S.elems) ∧ ∀ y ∈ S.elems, pkSet R y := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨S0', hS0'mem, by simp, ?_⟩
      rw [hS0'eq]; exact hS0
    | cons x l ih =>
      intro hl
      obtain ⟨S, hSmem, hlS, hSR⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      obtain ⟨hxR, hxsig⟩ := hl x List.mem_cons_self
      obtain ⟨⟨⟨hvalid, hcov⟩, hcons⟩, hcaps⟩ := hnodes S hSmem
      obtain ⟨hct1, hct2, hct3, hct4⟩ := cosetTab_spec S sigP
      obtain ⟨hgens, -⟩ := nodeValidW_spec hvalid
      have hSnd : S.elems.Nodup := nodeValidW_nodup hvalid
      have honeS : oneS ∈ S.elems := oneS_mem_of_valid hvalid
      have hpos : 0 < S.elems.length := List.length_pos_of_mem honeS
      have hrsig : ∀ c ∈ (cosetTab S sigP).2, InSigma φ c := by
        intro c hc
        rcases hct3 c hc with rfl | hc
        · exact inSigma_one
        · exact hsigP2 c hc
      have htabx := hcov x hxsig
      obtain ⟨s, hsS, hxs⟩ := hct1 x htabx
      have hrreps := hct2 x htabx
      set r := (cosetTab S sigP).1.getD x 0 with hr
      have hrR : pkSet R r := pkSet_of_mul hR (hSR s hsS) (hrsig r hrreps) (by rw [← hxs]; exact hxR)
      have hcapr := hcaps r hrreps
      unfold capOK at hcapr
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hcapr
      have hgenR : ∀ h ∈ S.gens ++ [r], pkSet R h := by
        intro h hh
        rcases List.mem_append.1 hh with hh | hh
        · exact hSR h (hgens h hh)
        · rw [List.mem_singleton.1 hh]; exact hrR
      have hOP : ∀ c ∈ cosetOrbit cap S (cosetTab S sigP).1 r,
          pkSet R c ∧ c ∈ (cosetTab S sigP).2 := by
        unfold cosetOrbit
        refine bfs_inv (fun c => pkSet R c ∧ c ∈ (cosetTab S sigP).2) _ ?_ [oneS] ?_ _
        · intro f hf c hc
          obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hf
          have hmul : pkSet R (mulS c h) := pkSet_mul hR hc.1 (hgenR h hh)
          have hmemsig : mulS c h ∈ sigP := by
            obtain ⟨ρ, hρ, hρe⟩ := hmul
            rw [← hρe]
            exact hsigP1 ρ (hR hρ)
          have htab := hcov _ hmemsig
          obtain ⟨s', hs'S, hs'e⟩ := hct1 _ htab
          have hc'reps := hct2 _ htab
          refine ⟨?_, hc'reps⟩
          exact pkSet_of_mul hR (hSR s' hs'S) (hrsig _ hc'reps) (by rw [← hs'e]; exact hmul)
        · intro c hc
          rw [List.mem_singleton] at hc
          subst hc
          exact ⟨pkSet_one, hct4⟩
      rcases hcapr with hbig | ⟨N, hNmem, hNeq⟩
      · exfalso
        exact big_orbit_false hR hSnd hSR hrsig hcons hOP hcap hpos hbig
      · have hmemC : ∀ y, y ∈ N.elems ↔ ∃ c ∈ cosetOrbit cap S (cosetTab S sigP).1 r,
            ∃ s ∈ S.elems, y = mulS s c := by
          intro y
          rw [hNeq, mem_sortSet, mem_cosetUnion]
        have honeO : oneS ∈ cosetOrbit cap S (cosetTab S sigP).1 r :=
          mem_bfs_of_mem _ List.mem_cons_self _
        have hrO : r ∈ cosetOrbit cap S (cosetTab S sigP).1 r := by
          have hmv := move_mem_bfs
            ((S.gens ++ [r]).map fun h c => (cosetTab S sigP).1.getD (mulS c h) 0) oneS
            (cap / S.elems.length)
            (f := fun c => (cosetTab S sigP).1.getD (mulS c r) 0)
            (List.mem_map.2 ⟨r, List.mem_append_right _ (List.mem_singleton_self r), rfl⟩)
          have e : (cosetTab S sigP).1.getD (mulS oneS r) 0 = r := hcons r hrreps oneS honeS
          rw [e] at hmv
          exact hmv
        refine ⟨N, hNmem, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact (hmemC _).2 ⟨r, hrO, s, hsS, hxs⟩
          · have hyS := hlS y hy
            exact (hmemC y).2 ⟨oneS, honeO, y, hyS, (mulS_one_right hR (hSR y hyS)).symm⟩
        · intro y hy
          obtain ⟨c, hc, s', hs', rfl⟩ := (hmemC y).1 hy
          exact pkSet_mul hR (hSR s' hs') (hOP c hc).1
  have hl := key (sigP.filter fun y => decide (pkSet R y)) (fun y hy =>
    ⟨of_decide_eq_true (List.mem_filter.1 hy).2, (List.mem_filter.1 hy).1⟩)
  obtain ⟨S, hSmem, hlS, hSR⟩ := hl
  refine ⟨S, hSmem, fun y => ⟨fun hy => hlS y (List.mem_filter.2 ?_), hSR y⟩⟩
  obtain ⟨r, hr, rfl⟩ := hy
  exact ⟨hsigP1 r (hR hr), by simpa using ⟨r, hr, rfl⟩⟩

end Lattice

end CFSG.Quasithin.H13.I1277

end
