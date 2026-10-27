module

public import CFSG.YGroups.DCE.PermBSpec
public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def forestRec (n : ℕ) (G : Array ByteArray) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut pos : Array ℕ := Array.replicate n n
  let mut tp : Array ℕ := Array.replicate n n
  let mut tl : Array ℕ := Array.replicate n 0
  let mut rt : Array ℕ := Array.replicate n n
  let mut off := 0
  for s in [0:n] do
    if rt[s]! == n then
      let r := B.orbitRec n s G
      for y in r.1 do
        pos := pos.set! y (off + r.2.1[y]!)
        tp := tp.set! y r.2.2.1[y]!
        tl := tl.set! y r.2.2.2[y]!
        rt := rt.set! y s
      off := off + r.1.size
  return (pos, tp, tl, rt)

@[expose] def forestValid (n : ℕ) (G : Array ByteArray)
    (f : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : Bool :=
  allLt n fun x =>
    decide (f.2.2.2[x]! < n) && f.2.2.2[f.2.2.2[x]!]! == f.2.2.2[x]! &&
      (f.2.2.2[x]! == x ||
        (decide (f.2.2.1[x]! < G.size) && decide (f.2.1[x]! < n) &&
          decide (f.1[f.2.1[x]!]! < f.1[x]!) && f.2.2.2[f.2.1[x]!]! == f.2.2.2[x]! &&
          bget G[f.2.2.1[x]!]! f.2.1[x]! == x))

theorem forestValid_spec {n : ℕ} {G : Array ByteArray} {f : Array ℕ × Array ℕ × Array ℕ × Array ℕ}
    (h : forestValid n G f = true) (K : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ i < G.size, ∃ g ∈ K, RepB n G[i]! g) (x : ℕ) (hx : x < n) :
    ∃ hr : f.2.2.2[x]! < n, f.2.2.2[f.2.2.2[x]!]! = f.2.2.2[x]! ∧
      ∃ g ∈ K, g ⟨f.2.2.2[x]!, hr⟩ = ⟨x, hx⟩ := by
  have key : ∀ m x (hx : x < n), f.1[x]! = m → ∃ hr : f.2.2.2[x]! < n,
      f.2.2.2[f.2.2.2[x]!]! = f.2.2.2[x]! ∧ ∃ g ∈ K, g ⟨f.2.2.2[x]!, hr⟩ = ⟨x, hx⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx hm
      have hv := allLt_spec h hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hv
      obtain ⟨⟨hrt, hrr⟩, hcase⟩ := hv
      refine ⟨hrt, hrr, ?_⟩
      rcases hcase with hroot | ⟨⟨⟨⟨htl, htp⟩, hpos⟩, hrtp⟩, hgen⟩
      · exact ⟨1, K.one_mem, Fin.ext hroot⟩
      · obtain ⟨hr', -, g, hgK, hg⟩ := ih _ (hm ▸ hpos) _ htp rfl
        obtain ⟨g', hg'K, hrep⟩ := hG _ htl
        refine ⟨g' * g, K.mul_mem hg'K hgK, ?_⟩
        have e1 : (⟨f.2.2.2[x]!, hrt⟩ : Fin n) = ⟨f.2.2.2[f.2.1[x]!]!, hr'⟩ :=
          Fin.ext hrtp.symm
        rw [Equiv.Perm.mul_apply, e1, hg]
        apply Fin.ext
        rw [← hrep.apply htp]
        exact hgen
  exact key _ x hx rfl

theorem foldl_count_eq_sum (p : ℕ → Bool) (m : ℕ) :
    (List.range m).foldl (fun a w => if p w then a + 1 else a) 0 =
      ∑ w ∈ Finset.range m, if p w then 1 else 0 := by
  have key : ∀ (l : List ℕ) (init : ℕ),
      l.foldl (fun a w => if p w then a + 1 else a) init =
        init + (l.map fun w => if p w then 1 else 0).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ih =>
      intro init
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      split_ifs <;> omega
  rw [key, zero_add]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem foldl_add_eq_sum_range (g : ℕ → ℕ) (m : ℕ) :
    (List.range m).foldl (fun a l => a + g l) 0 = ∑ l ∈ Finset.range m, g l := by
  have key : ∀ (l : List ℕ) (init : ℕ),
      l.foldl (fun a l => a + g l) init = init + (l.map g).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ih =>
      intro init
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      omega
  rw [key, zero_add]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem index_mul_card_map_of_ker_le {E G' : Type*} [Group E] [Group G'] [Finite E]
    (φ : E →* G') (P : Subgroup E) (hker : φ.ker ≤ P) :
    P.index * Nat.card (P.map φ) = Nat.card φ.range := by
  have h1 : (P.map φ).relIndex φ.range = P.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
      Subgroup.relIndex_top_right, sup_of_le_left hker]
  have h2 := Subgroup.relIndex_mul_card (H := P.map φ) (K := φ.range)
  rwa [inf_of_le_left (Subgroup.map_le_range φ P), h1] at h2

theorem card_filter_fin (n : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun x : Fin n => p x.1 = true).card =
      (List.range n).foldl (fun a w => if p w then a + 1 else a) 0 := by
  rw [foldl_count_eq_sum, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun w => if p w = true then 1 else 0) n
