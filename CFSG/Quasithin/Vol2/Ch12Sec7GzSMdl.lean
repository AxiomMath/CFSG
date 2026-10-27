module

public import Certificates.Data.S1277Struct
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBfsLem
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Set

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Bfs Std

section Closures

variable (T : KTab)

theorem mem_sortSet (S : HashSet Nat) (x : Nat) : x ∈ sortSet S ↔ x ∈ S := by
  unfold sortSet
  rw [List.mem_mergeSort, HashSet.mem_toList]

theorem mulCl_inv (gens : List Nat) (P : Nat → Prop) (hone : P (oneN T)) (hgens : ∀ g ∈ gens, P g)
    (hmul : ∀ g ∈ gens, ∀ x, P x → P (mulN T x g)) : ∀ e ∈ mulCl T gens, P e := by
  refine bfs_inv P (mulMoves T gens) ?_ (oneN T :: gens) ?_ _
  · intro f hf x hx
    unfold mulMoves at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact hmul g hg x hx
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hone
    · exact hgens x hx

theorem one_mem_mulCl (gens : List Nat) : oneN T ∈ mulCl T gens :=
  mem_bfs_of_mem _ List.mem_cons_self _

theorem mem_mulCl_of_mem {gens : List Nat} {g : Nat} (hg : g ∈ gens) : g ∈ mulCl T gens :=
  mem_bfs_of_mem _ (List.mem_cons_of_mem _ hg) _

theorem conjOrbit_inv (kgens gens0 : List Nat) (P : Nat → Prop)
    (hconj : ∀ g ∈ kgens, ∀ x, P x → P (mulN T (mulN T g x) (invN T g)))
    (hg : ∀ x ∈ gens0, P x) : ∀ e ∈ bfs (conjMoves T kgens) gens0 1000000, P e := by
  refine bfs_inv P (conjMoves T kgens) ?_ gens0 hg _
  intro f hf x hx
  unfold conjMoves at hf
  obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hf
  exact hconj g hg' x hx

theorem greedy_inv (A : List Nat) (P : Nat → Prop) (hone : P (oneN T))
    (hmul : ∀ x y, P x → P y → P (mulN T x y)) (hA : ∀ a ∈ A, P a) :
    ∀ (st : List Nat × HashSet Nat), (∀ a ∈ st.1, P a) → st.2 = mulCl T st.1 →
      let st' := A.foldl (fun (st : List Nat × HashSet Nat) a =>
        if st.2.contains a then st else (st.1 ++ [a], mulCl T (st.1 ++ [a]))) st
      (∀ a ∈ st'.1, P a) ∧ st'.2 = mulCl T st'.1 := by
  induction A with
  | nil => intro st h1 h2; exact ⟨h1, h2⟩
  | cons a A ih =>
    intro st h1 h2
    simp only [List.foldl_cons]
    have hA' : ∀ b ∈ A, P b := fun b hb => hA b (List.mem_cons_of_mem _ hb)
    by_cases hc : st.2.contains a = true
    · simp only [hc, if_true]
      exact ih hA' st h1 h2
    · simp only [hc]
      have hc' : (st.2.contains a) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, if_false]
      refine ih hA' (st.1 ++ [a], mulCl T (st.1 ++ [a])) ?_ rfl
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact h1 b hb
      · rw [List.mem_singleton.1 hb]; exact hA a List.mem_cons_self

theorem normClosure_spec (kgens gens0 : List Nat) (N : Node) (h : normClosure T kgens gens0 = some N)
    (P : Nat → Prop) (hone : P (oneN T)) (hmul : ∀ x y, P x → P y → P (mulN T x y))
    (hconj : ∀ g ∈ kgens, ∀ x, P x → P (mulN T (mulN T g x) (invN T g)))
    (hg : ∀ x ∈ gens0, P x) : (∀ e ∈ N.elems, P e) ∧ (∀ x ∈ gens0, x ∈ N.elems) := by
  unfold normClosure at h
  set A := sortSet (bfs (conjMoves T kgens) gens0 1000000) with hA
  have hAP : ∀ a ∈ A, P a := by
    intro a ha
    rw [hA, mem_sortSet] at ha
    exact conjOrbit_inv T kgens gens0 P hconj hg a ha
  set st := A.foldl (fun (st : List Nat × HashSet Nat) a =>
    if st.2.contains a then st else (st.1 ++ [a], mulCl T (st.1 ++ [a]))) ([], mulCl T []) with hst
  have hinv := greedy_inv T A P hone hmul hAP ([], mulCl T []) (by simp) rfl
  rw [← hst] at hinv
  dsimp only at h hinv
  split_ifs at h with hAll
  · cases h
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [mem_sortSet] at he
      rw [hinv.2] at he
      exact mulCl_inv T st.1 P hone hinv.1 (fun g hg' x hx => hmul x g hx (hinv.1 g hg')) e he
    · intro x hx
      simp only [mem_sortSet]
      have hxA : x ∈ A := by
        rw [hA, mem_sortSet]
        exact mem_bfs_of_mem _ hx _
      have := (List.all_eq_true.1 hAll) x hxA
      exact HashSet.contains_iff_mem.1 this

theorem mem_elemSet (l : List Nat) (x : Nat) :
    x ∈ (l.foldl (fun s x => s.insert x) (∅ : HashSet Nat)) ↔ x ∈ l := by
  rw [mem_foldl_insert]
  simp

theorem subsetL_iff (a b : List Nat) : subsetL a b = true ↔ ∀ x ∈ a, x ∈ b := by
  unfold subsetL
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    have := h x hx
    rw [← mem_elemSet b x]
    exact HashSet.contains_iff_mem.1 this
  · intro h x hx
    rw [HashSet.contains_iff_mem, mem_elemSet]
    exact h x hx

theorem nodeValid_spec {N : Node} (hN : nodeValid T N = true) :
    (∀ g ∈ N.gens, g ∈ N.elems) ∧
      ∀ P : Nat → Prop, P (oneN T) → (∀ x y, P x → P y → P (mulN T x y)) →
        (∀ g ∈ N.gens, P g) → ∀ e ∈ N.elems, P e := by
  unfold nodeValid at hN
  rw [Bool.and_eq_true] at hN
  obtain ⟨h1, h2⟩ := hN
  have hel : N.elems = sortSet (mulCl T N.gens) := beq_iff_eq.1 h1
  have hg : ∀ g ∈ N.gens, g ∈ N.elems := (subsetL_iff _ _).1 h2
  refine ⟨hg, fun P hone hmul hgP e he => ?_⟩
  rw [hel, mem_sortSet] at he
  exact mulCl_inv T N.gens P hone hgP (fun g hg' x hx => hmul x g hx (hgP g hg')) e he

theorem closedB_spec {kgens : List Nat} {N : Node} (hN : closedB T kgens N = true) :
    oneN T ∈ N.elems ∧ (∀ x ∈ N.elems, ∀ y ∈ N.elems, mulN T x y ∈ N.elems) ∧
      ∀ g ∈ kgens, ∀ x ∈ N.elems, mulN T (mulN T g x) (invN T g) ∈ N.elems := by
  unfold closedB at hN
  simp only [Bool.and_eq_true, List.all_eq_true, HashSet.contains_iff_mem, mem_elemSet] at hN
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN
  exact ⟨h1, fun x hx y hy => h2 x hx y hy, fun g hg x hx => h3 x hx g hg⟩

end Closures

section Classification

variable (T : KTab)

theorem classification {kgens : List Nat} {PCs nodes : List Node}
    (hlat : latticeOK T kgens PCs nodes = true) (hpc : pcOK T kgens PCs = true)
    (P : Nat → Prop) (hone : P (oneN T)) (hmul : ∀ x y, P x → P y → P (mulN T x y))
    (hconj : ∀ g ∈ kgens, ∀ x, P x → P (mulN T (mulN T g x) (invN T g)))
    (hK : ∀ x, P x → x ∈ klist T) (h2 : ∀ x, P x → isTwoN T x = true) :
    ∃ N ∈ nodes, ∀ x, P x ↔ x ∈ N.elems := by
  classical
  unfold latticeOK at hlat
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hlat
  obtain ⟨⟨⟨hbot, hvalid⟩, hPCvalid⟩, hjoin⟩ := hlat
  have hpool : ∀ x, P x → x ∈ poolElems T kgens := by
    intro x hx
    unfold poolElems twoElems
    rw [List.mem_filter, List.mem_filter]
    refine ⟨⟨hK x hx, h2 x hx⟩, ?_⟩
    simp only [Bool.not_eq_true']
    unfold cheapBad
    rw [Bool.eq_false_iff]
    intro hbad
    simp only [List.any_eq_true, Bool.not_eq_true'] at hbad
    obtain ⟨g, hg, hg2⟩ := hbad
    have := h2 _ (hmul x _ hx (hconj g hg x hx))
    rw [this] at hg2
    exact absurd hg2 (by simp)
  have key : ∀ l : List Nat, (∀ x ∈ l, P x) → (∀ x ∈ l, x ∈ poolElems T kgens) →
      ∃ N ∈ nodes, (∀ x ∈ l, x ∈ N.elems) ∧ ∀ y ∈ N.elems, P y := by
    intro l
    induction l with
    | nil =>
      intro _ _
      obtain ⟨N, hN, hNb⟩ := hbot
      have hNb' : N = botNode T := of_decide_eq_true hNb
      refine ⟨N, hN, by simp, fun y hy => ?_⟩
      rw [hNb'] at hy
      have : y = oneN T := by simpa [botNode] using hy
      rw [this]; exact hone
    | cons x l ih =>
      intro hP hpl
      obtain ⟨N, hN, hlN, hNP⟩ := ih (fun y hy => hP y (List.mem_cons_of_mem _ hy))
        (fun y hy => hpl y (List.mem_cons_of_mem _ hy))
      have hPx : P x := hP x List.mem_cons_self
      have hxpool : x ∈ poolElems T kgens := hpl x List.mem_cons_self
      unfold pcOK at hpc
      simp only [List.all_eq_true] at hpc
      have hx := hpc x hxpool
      obtain ⟨Nx, hNx⟩ : ∃ Nx, normClosure T kgens [x] = some Nx := by
        revert hx
        cases normClosure T kgens [x] with
        | none => simp
        | some Nx => intro _; exact ⟨Nx, rfl⟩
      rw [hNx] at hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, decide_eq_true_eq] at hx
      have hNxP := normClosure_spec T kgens [x] Nx hNx P hone hmul hconj
        (fun y hy => by rw [List.mem_singleton.1 hy]; exact hPx)
      have hall : Nx.elems.all (isTwoN T) = true := List.all_eq_true.2 fun y hy => h2 y (hNxP.1 y hy)
      obtain ⟨Pj, hPj, hPjeq⟩ : ∃ Pj ∈ PCs, Pj.elems = Nx.elems := by
        rcases hx with hx | ⟨Pj, hPj, hPjeq⟩
        · rw [hall] at hx; exact absurd hx (by simp)
        · exact ⟨Pj, hPj, beq_iff_eq.1 hPjeq⟩
      have hPjP : ∀ y ∈ Pj.elems, P y := by rw [hPjeq]; exact hNxP.1
      have hxPj : x ∈ Pj.elems := by rw [hPjeq]; exact hNxP.2 x List.mem_cons_self
      have hNvalid := (nodeValid_spec T (hvalid N hN).1)
      have hPjvalid := (nodeValid_spec T (hPCvalid Pj hPj))
      have hjoinNP := hjoin N hN Pj hPj
      rw [Bool.or_eq_true] at hjoinNP
      rcases hjoinNP with hsub | hjn
      ·
        refine ⟨N, hN, ?_, hNP⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact (subsetL_iff _ _).1 hsub y hxPj
        · exact hlN y hy
      ·
        cases hJ : joinNode T kgens N Pj with
        | none => rw [hJ] at hjn; simp at hjn
        | some J =>
          rw [hJ] at hjn
          have hJn := hjn
          simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, decide_eq_true_eq] at hJn
          have hJgens : ∀ y ∈ N.gens ++ Pj.gens, P y := by
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact hNP y (hNvalid.1 y hy)
            · exact hPjP y (hPjvalid.1 y hy)
          have hJspec := normClosure_spec T kgens _ J hJ P hone hmul hconj hJgens
          have hJall : J.elems.all (isTwoN T) = true :=
            List.all_eq_true.2 fun y hy => h2 y (hJspec.1 y hy)
          obtain ⟨N', hN', hN'eq⟩ : ∃ N' ∈ nodes, N'.elems = J.elems := by
            rcases hJn with hJn | ⟨N', hN', hN'eq⟩
            · rw [hJall] at hJn; exact absurd hJn (by simp)
            · exact ⟨N', hN', beq_iff_eq.1 hN'eq⟩
          have hclosed := closedB_spec T (hvalid N' hN').2
          have hmulJ : ∀ a b, a ∈ J.elems → b ∈ J.elems → mulN T a b ∈ J.elems := by
            intro a b ha hb
            rw [← hN'eq] at ha hb ⊢
            exact hclosed.2.1 a ha b hb
          have honeJ : oneN T ∈ J.elems := by rw [← hN'eq]; exact hclosed.1
          have hgJ : ∀ y ∈ N.gens ++ Pj.gens, y ∈ J.elems := hJspec.2
          have hNJ : ∀ y ∈ N.elems, y ∈ J.elems :=
            hNvalid.2 (fun y => y ∈ J.elems) honeJ (fun a b ha hb => hmulJ a b ha hb)
              (fun g hg => hgJ g (List.mem_append_left _ hg))
          have hPJ : ∀ y ∈ Pj.elems, y ∈ J.elems :=
            hPjvalid.2 (fun y => y ∈ J.elems) honeJ (fun a b ha hb => hmulJ a b ha hb)
              (fun g hg => hgJ g (List.mem_append_right _ hg))
          refine ⟨N', hN', ?_, fun y hy => hJspec.1 y (by rw [← hN'eq]; exact hy)⟩
          intro y hy
          rw [hN'eq]
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hPJ y hxPj
          · exact hNJ y (hlN y hy)
  have hl := key ((poolElems T kgens).filter fun x => decide (P x))
    (fun x hx => of_decide_eq_true (List.mem_filter.1 hx).2)
    (fun x hx => (List.mem_filter.1 hx).1)
  obtain ⟨N, hN, hlN, hNP⟩ := hl
  refine ⟨N, hN, fun x => ⟨fun hx => hlN x (List.mem_filter.2 ⟨hpool x hx, by simpa using hx⟩), hNP x⟩⟩

end Classification

end CFSG.Quasithin.H13.I1277

end
