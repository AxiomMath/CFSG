module

public import CFSG.Sporadic.Co1Patterson.TitsMultiHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.SuzRecog

open SimpleGraph CFSG.Sporadic.Co1Patterson

variable {V : Type*} {G : SimpleGraph V} {T : Set V → Prop} {b : V}

@[expose] def NullEdge (T : Set V → Prop) (γ : ∀ x, G.Walk b x) {x y : V} (h : G.Adj x y) :
    Prop :=
  HomotopicBy T ((γ x).concat h) (γ y)

theorem nullEdge_of_eq_concat (γ : ∀ x, G.Walk b x) {x y : V} (h : G.Adj x y)
    (hγ : γ y = (γ x).concat h) : NullEdge T γ h := by
  rw [NullEdge, hγ]

theorem NullEdge.symm {γ : ∀ x, G.Walk b x} {x y : V} {h : G.Adj x y} (hn : NullEdge T γ h) :
    NullEdge T γ h.symm := by
  have h₁ : HomotopicBy T (((γ x).concat h).concat h.symm) ((γ y).concat h.symm) := by
    simpa only [Walk.concat_eq_append] using hn.append_right (.cons h.symm .nil)
  have h₂ : HomotopicBy T (γ x) (((γ x).concat h).concat h.symm) := by
    simpa only [Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append, Walk.nil_append,
      Walk.append_nil] using homotopicBy_backtrack (T := T) (γ x) .nil h
  exact (h₂.trans h₁).symm

theorem NullEdge.of_triangle {γ : ∀ x, G.Walk b x} {x y z : V} {hxy : G.Adj x y}
    {hyz : G.Adj y z} (hxz : G.Adj x z) (hT : T {x, y, z}) (h₁ : NullEdge T γ hxy)
    (h₂ : NullEdge T γ hyz) : NullEdge T γ hxz := by
  have e₁ : HomotopicBy T ((γ x).concat hxz)
      ((γ x).append (.cons hxy (.cons hyz (.cons hxz.symm (.cons hxz .nil))))) := by
    rw [Walk.concat_eq_append]
    exact (ElemMoveBy.triangle (γ x) (.cons hxz .nil) hxy hyz hxz.symm hT).homotopicBy
  have e₂ : HomotopicBy T (((γ x).concat hxy).concat hyz)
      ((γ x).append (.cons hxy (.cons hyz (.cons hxz.symm (.cons hxz .nil))))) := by
    simpa only [Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append, Walk.nil_append,
      Walk.append_nil] using
      homotopicBy_backtrack (T := T) (((γ x).concat hxy).concat hyz) .nil hxz.symm
  have e₃ : HomotopicBy T (((γ x).concat hxy).concat hyz) ((γ y).concat hyz) := by
    simpa only [Walk.concat_eq_append] using h₁.append_right (.cons hyz .nil)
  exact (e₁.trans e₂.symm).trans (e₃.trans h₂)

theorem homotopicBy_append_of_forall_nullEdge {γ : ∀ x, G.Walk b x}
    (hn : ∀ x y (h : G.Adj x y), NullEdge T γ h) {u v : V} (w : G.Walk u v) :
    HomotopicBy T ((γ u).append w) (γ v) := by
  induction w with
  | nil => rw [Walk.append_nil]
  | @cons u u' v h w ih =>
    have : (γ u).append (.cons h w) = ((γ u).concat h).append w := by
      rw [Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append, Walk.nil_append]
    rw [this]
    exact ((hn u u' h).append_right w).trans ih

theorem triangulableBy_of_forall_nullEdge (γ : ∀ x, G.Walk b x)
    (hn : ∀ x y (h : G.Adj x y), NullEdge T γ h) : TriangulableBy G T := by
  intro u p
  have h₁ := (homotopicBy_append_of_forall_nullEdge hn p).append_left (γ u).reverse
  have h₂ : HomotopicBy T (((γ u).reverse.append (γ u)).append p) p := by
    simpa only [Walk.nil_append] using (homotopicBy_reverse_append (T := T) (γ u)).append_right p
  rw [← Walk.append_assoc] at h₂
  exact h₂.symm.trans (h₁.trans (homotopicBy_reverse_append (γ u)))

inductive Derivable (G : SimpleGraph V) (T : Set V → Prop) (tree : V → V → Prop) :
    V → V → Prop
  | tree {x y : V} : tree x y → Derivable G T tree x y
  | symm {x y : V} : Derivable G T tree x y → Derivable G T tree y x
  | tri {x y z : V} : G.Adj x z → T {x, y, z} → Derivable G T tree x y →
      Derivable G T tree y z → Derivable G T tree x z

theorem Derivable.nullEdge {tree : V → V → Prop} {γ : ∀ x, G.Walk b x}
    (htree : ∀ x y, tree x y → ∃ h : G.Adj x y, γ y = (γ x).concat h) {x y : V}
    (hd : Derivable G T tree x y) : ∃ h : G.Adj x y, NullEdge T γ h := by
  induction hd with
  | tree ht =>
    obtain ⟨h, hγ⟩ := htree _ _ ht
    exact ⟨h, nullEdge_of_eq_concat γ h hγ⟩
  | symm _ ih =>
    obtain ⟨h, hn⟩ := ih
    exact ⟨h.symm, hn.symm⟩
  | tri hxz hT _ _ ih₁ ih₂ =>
    obtain ⟨_, hn₁⟩ := ih₁
    obtain ⟨_, hn₂⟩ := ih₂
    exact ⟨hxz, hn₁.of_triangle hxz hT hn₂⟩

theorem triangulableBy_of_derivable {tree : V → V → Prop} (γ : ∀ x, G.Walk b x)
    (htree : ∀ x y, tree x y → ∃ h : G.Adj x y, γ y = (γ x).concat h)
    (hall : ∀ x y, G.Adj x y → Derivable G T tree x y) : TriangulableBy G T :=
  triangulableBy_of_forall_nullEdge γ fun x y h => by
    obtain ⟨_, hn⟩ := (hall x y h).nullEdge htree
    exact hn

namespace ElimCert

@[expose] def occB (s : Array ℕ) (y : ℕ) : Bool := (List.range s.size).any fun k => s[k]! == y

@[expose] def adjB (nbr : Array (Array ℕ)) (x y : ℕ) : Bool :=
  x != y && (occB nbr[x]! y || occB nbr[y]! x)

@[expose] def endsB (s : Array ℕ) (x y : ℕ) : Bool :=
  (s[0]! == x && s[1]! == y) || (s[0]! == y && s[1]! == x)

@[expose] def stepOK (n : ℕ) (nbr : Array (Array ℕ)) (par : Array ℕ) (tri : ℕ → ℕ → ℕ → Bool)
    (steps : Array (Array ℕ)) (i : ℕ) : Bool :=
  let s := steps[i]!
  s[0]! < n && s[1]! < n && adjB nbr s[0]! s[1]! &&
    ((s.size == 2 &&
        ((0 < s[1]! && par[s[1]!]! == s[0]!) || (0 < s[0]! && par[s[0]!]! == s[1]!))) ||
      (s.size == 5 && s[2]! < n && s[3]! < i && s[4]! < i && endsB steps[s[3]!]! s[0]! s[2]! &&
        endsB steps[s[4]!]! s[2]! s[1]! && tri s[0]! s[2]! s[1]!))

@[expose] def ok (n : ℕ) (nbr : Array (Array ℕ)) (par dep : Array ℕ) (tri : ℕ → ℕ → ℕ → Bool)
    (steps emap : Array (Array ℕ)) : Bool :=
  0 < n &&
    (List.range n).all (fun x => x == 0 ||
      (par[x]! < n && dep[par[x]!]! < dep[x]! && adjB nbr par[x]! x)) &&
    (List.range steps.size).all (stepOK n nbr par tri steps) &&
    (List.range n).all fun x => (List.range (nbr[x]!).size).all fun k =>
      x == (nbr[x]!)[k]! || (n ≤ (nbr[x]!)[k]! ||
        ((emap[x]!)[k]! < steps.size && endsB steps[(emap[x]!)[k]!]! x (nbr[x]!)[k]!))

end ElimCert

open ElimCert

@[expose] def nbrGraph (n : ℕ) (nbr : Array (Array ℕ)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (occB nbr[x.1]! y.1 = true ∨ occB nbr[y.1]! x.1 = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem nbrGraph_adj_iff {n : ℕ} {nbr : Array (Array ℕ)} {x y : Fin n} :
    (nbrGraph n nbr).Adj x y ↔ adjB nbr x.1 y.1 = true := by
  simp only [nbrGraph, adjB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Fin.val_inj]

noncomputable def treeWalk {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (par : Fin n → Fin n)
    (d : Fin n → ℕ) (hpar : ∀ x : Fin n, x.1 ≠ 0 → d (par x) < d x ∧ G.Adj (par x) x)
    (x : Fin n) : G.Walk ⟨0, hn⟩ x :=
  if hx : x.1 = 0 then (Walk.nil : G.Walk ⟨0, hn⟩ ⟨0, hn⟩).copy rfl (Fin.ext hx.symm)
  else (treeWalk G hn par d hpar (par x)).concat (hpar x hx).2
termination_by d x
decreasing_by exact (hpar x hx).1

theorem treeWalk_of_ne {n : ℕ} {G : SimpleGraph (Fin n)} {hn : 0 < n} {par : Fin n → Fin n}
    {d : Fin n → ℕ} {hpar : ∀ x : Fin n, x.1 ≠ 0 → d (par x) < d x ∧ G.Adj (par x) x}
    {x : Fin n} (hx : x.1 ≠ 0) :
    treeWalk G hn par d hpar x = (treeWalk G hn par d hpar (par x)).concat (hpar x hx).2 := by
  rw [treeWalk]
  simp only [hx, ↓reduceDIte]

theorem occB_iff {s : Array ℕ} {y : ℕ} : occB s y = true ↔ ∃ k < s.size, s[k]! = y := by
  simp only [occB, List.any_eq_true, List.mem_range, beq_iff_eq]

theorem derivable_of_endsB {n : ℕ} {G : SimpleGraph (Fin n)} {T : Set (Fin n) → Prop}
    {tree : Fin n → Fin n → Prop} {s : Array ℕ} {x y : ℕ} (hx : x < n) (hy : y < n)
    (h0 : s[0]! < n) (h1 : s[1]! < n) (d : Derivable G T tree ⟨s[0]!, h0⟩ ⟨s[1]!, h1⟩)
    (he : endsB s x y = true) : Derivable G T tree ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp only [endsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at he
  rcases he with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · have a : (⟨s[0]!, h0⟩ : Fin n) = ⟨x, hx⟩ := Fin.ext e0
    have b : (⟨s[1]!, h1⟩ : Fin n) = ⟨y, hy⟩ := Fin.ext e1
    rwa [a, b] at d
  · have a : (⟨s[0]!, h0⟩ : Fin n) = ⟨y, hy⟩ := Fin.ext e0
    have b : (⟨s[1]!, h1⟩ : Fin n) = ⟨x, hx⟩ := Fin.ext e1
    rw [a, b] at d
    exact d.symm

theorem triangulableBy_of_ok {n : ℕ} {nbr : Array (Array ℕ)} {par dep : Array ℕ}
    {tri : ℕ → ℕ → ℕ → Bool} {steps emap : Array (Array ℕ)} {T : Set (Fin n) → Prop}
    (htri : ∀ x y z : Fin n, tri x.1 y.1 z.1 = true → T {x, y, z})
    (h : ok n nbr par dep tri steps emap = true) : TriangulableBy (nbrGraph n nbr) T := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hparB⟩, hsteps⟩, hemap⟩ := h
  have hparB' : ∀ x : Fin n, x.1 ≠ 0 → par[x.1]! < n ∧ dep[par[x.1]!]! < dep[x.1]! ∧
      adjB nbr par[x.1]! x.1 = true := by
    intro x hx
    have := hparB x.1 x.2
    simpa [Bool.or_eq_true, beq_iff_eq, hx, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      using this
  let parF : Fin n → Fin n := fun x =>
    if hx : x.1 = 0 then ⟨0, hn⟩ else ⟨par[x.1]!, (hparB' x hx).1⟩
  let d : Fin n → ℕ := fun x => dep[x.1]!
  have hpar : ∀ x : Fin n, x.1 ≠ 0 → d (parF x) < d x ∧ (nbrGraph n nbr).Adj (parF x) x := by
    intro x hx
    simp only [parF, d, hx, ↓reduceDIte]
    exact ⟨(hparB' x hx).2.1, nbrGraph_adj_iff.2 (hparB' x hx).2.2⟩
  let tree : Fin n → Fin n → Prop := fun x y => y.1 ≠ 0 ∧ parF y = x
  have htree : ∀ x y, tree x y → ∃ h : (nbrGraph n nbr).Adj x y,
      treeWalk _ hn parF d hpar y = (treeWalk _ hn parF d hpar x).concat h := by
    rintro x y ⟨hy, rfl⟩
    exact ⟨(hpar y hy).2, treeWalk_of_ne hy⟩
  have key : ∀ i < steps.size, ∃ (hx : (steps[i]!)[0]! < n) (hz : (steps[i]!)[1]! < n),
      Derivable (nbrGraph n nbr) T tree ⟨_, hx⟩ ⟨_, hz⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hs := hsteps i hi
      simp only [stepOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨hx, hz⟩, hadj⟩, hcase⟩ := hs
      refine ⟨hx, hz, ?_⟩
      rcases hcase with ⟨-, ⟨hz0, hpz⟩ | ⟨hx0, hpx⟩⟩ | ⟨⟨⟨⟨⟨⟨-, hy⟩, hi₁⟩, hi₂⟩, he₁⟩, he₂⟩, ht⟩
      · refine .tree ⟨Nat.pos_iff_ne_zero.mp hz0, ?_⟩
        simp only [parF, Nat.pos_iff_ne_zero.mp hz0, ↓reduceDIte]
        exact Fin.ext hpz
      · refine .symm (.tree ⟨Nat.pos_iff_ne_zero.mp hx0, ?_⟩)
        simp only [parF, Nat.pos_iff_ne_zero.mp hx0, ↓reduceDIte]
        exact Fin.ext hpx
      · obtain ⟨hx₁, hz₁, d₁⟩ := ih _ hi₁ (hi₁.trans hi)
        obtain ⟨hx₂, hz₂, d₂⟩ := ih _ hi₂ (hi₂.trans hi)
        exact .tri (nbrGraph_adj_iff.2 hadj) (htri _ _ _ ht)
          (derivable_of_endsB hx hy hx₁ hz₁ d₁ he₁) (derivable_of_endsB hy hz hx₂ hz₂ d₂ he₂)
  have hlist : ∀ (x y : Fin n), x ≠ y → occB nbr[x.1]! y.1 = true →
      Derivable (nbrGraph n nbr) T tree x y := by
    intro x y hxy hocc
    obtain ⟨k, hk, hky⟩ := occB_iff.1 hocc
    have he := hemap x.1 x.2 k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, hky] at he
    rcases he with he | he | ⟨hj, he⟩
    · exact absurd (Fin.ext he) hxy
    · exact absurd y.2 (not_lt.2 he)
    · obtain ⟨h0, h1, d⟩ := key _ hj
      exact derivable_of_endsB x.2 y.2 h0 h1 d he
  refine triangulableBy_of_derivable (treeWalk _ hn parF d hpar) htree fun x y hxy => ?_
  obtain ⟨hne, hocc | hocc⟩ := hxy
  · exact hlist x y hne hocc
  · exact (hlist y x (Ne.symm hne) hocc).symm

theorem preconnected_of_ok {n : ℕ} {nbr : Array (Array ℕ)} {par dep : Array ℕ}
    {tri : ℕ → ℕ → ℕ → Bool} {steps emap : Array (Array ℕ)}
    (h : ok n nbr par dep tri steps emap = true) : (nbrGraph n nbr).Preconnected := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hparB⟩, -⟩, -⟩ := h
  have hparB' : ∀ x : Fin n, x.1 ≠ 0 → par[x.1]! < n ∧ dep[par[x.1]!]! < dep[x.1]! ∧
      adjB nbr par[x.1]! x.1 = true := by
    intro x hx
    have := hparB x.1 x.2
    simpa [Bool.or_eq_true, beq_iff_eq, hx, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      using this
  let parF : Fin n → Fin n := fun x =>
    if hx : x.1 = 0 then ⟨0, hn⟩ else ⟨par[x.1]!, (hparB' x hx).1⟩
  let d : Fin n → ℕ := fun x => dep[x.1]!
  have hpar : ∀ x : Fin n, x.1 ≠ 0 → d (parF x) < d x ∧ (nbrGraph n nbr).Adj (parF x) x := by
    intro x hx
    simp only [parF, d, hx, ↓reduceDIte]
    exact ⟨(hparB' x hx).2.1, nbrGraph_adj_iff.2 (hparB' x hx).2.2⟩
  intro x y
  exact ((treeWalk _ hn parF d hpar x).reverse.append (treeWalk _ hn parF d hpar y)).reachable

end CFSG.Sporadic.SuzRecog
