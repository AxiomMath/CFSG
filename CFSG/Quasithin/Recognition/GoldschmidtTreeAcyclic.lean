module

public import CFSG.Quasithin.Recognition.GoldschmidtTree

public section

open Monoid

universe u v

namespace CFSG.Quasithin

namespace GoldAmalgam

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def vtxGroup : Bool → Subgroup X.Universal
  | true => X.ofA.range
  | false => X.ofB.range

@[expose] def vtx : Bool → X.Universal →
    (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)
  | true, x => .inl (x : X.Universal ⧸ X.ofA.range)
  | false, x => .inr (x : X.Universal ⧸ X.ofB.range)

abbrev treeGraph : SimpleGraph ((X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) :=
  goldCosetGraph X.ofA.range X.ofB.range

theorem vtx_mul {t : Bool} {x y : X.Universal} (hy : y ∈ X.vtxGroup t) :
    X.vtx t (x * y) = X.vtx t x := by
  cases t
  · exact congrArg Sum.inr (QuotientGroup.mk_mul_of_mem x hy)
  · exact congrArg Sum.inl (QuotientGroup.mk_mul_of_mem x hy)

theorem adj_vtx_not (t : Bool) (x : X.Universal) : X.treeGraph.Adj (X.vtx t x) (X.vtx (!t) x) := by
  cases t
  · exact (goldCosetGraph_adj_base X.ofA.range X.ofB.range x).symm
  · exact goldCosetGraph_adj_base X.ofA.range X.ofB.range x

theorem adj_vtx_iff (t : Bool) (x : X.Universal) (w) :
    X.treeGraph.Adj (X.vtx t x) w ↔ ∃ y ∈ X.vtxGroup t, w = X.vtx (!t) (x * y) := by
  cases t
  · have h := goldCosetGraph_neighborSet_inr X.ofA.range X.ofB.range x
    have hw : X.treeGraph.Adj (.inr (x : X.Universal ⧸ X.ofB.range)) w ↔
        w ∈ Set.range (fun b : X.ofB.range =>
          (Sum.inl ((x * b : X.Universal) : X.Universal ⧸ X.ofA.range) :
            (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range))) := by
      rw [← h]
      rfl
    refine hw.trans ⟨?_, ?_⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  · have h := goldCosetGraph_neighborSet_inl X.ofA.range X.ofB.range x
    have hw : X.treeGraph.Adj (.inl (x : X.Universal ⧸ X.ofA.range)) w ↔
        w ∈ Set.range (fun a : X.ofA.range =>
          (Sum.inr ((x * a : X.Universal) : X.Universal ⧸ X.ofB.range) :
            (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range))) := by
      rw [← h]
      rfl
    refine hw.trans ⟨?_, ?_⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩

theorem vtx_eq_iff (t t' : Bool) (x x' : X.Universal) :
    X.vtx t x = X.vtx t' x' ↔ t = t' ∧ x⁻¹ * x' ∈ X.vtxGroup t := by
  cases t <;> cases t'
  · simp only [vtx, vtxGroup, Sum.inr.injEq, true_and]
    exact QuotientGroup.eq
  · simp [vtx]
  · simp [vtx]
  · simp only [vtx, vtxGroup, Sum.inl.injEq, true_and]
    exact QuotientGroup.eq

abbrev Letter (A B : Type u) : Type u := Σ b : Bool, goldVertexGroup A B b

@[expose] def lprod (l : List (Letter A B)) : X.Universal :=
  (l.map fun g => PushoutI.of (φ := X.diagram) g.1 g.2).prod

@[simp] theorem lprod_nil : X.lprod [] = 1 := rfl

@[simp] theorem lprod_cons (g : Letter A B) (l : List (Letter A B)) :
    X.lprod (g :: l) = PushoutI.of (φ := X.diagram) g.1 g.2 * X.lprod l := by
  simp [lprod]

theorem lprod_append (l₁ l₂ : List (Letter A B)) :
    X.lprod (l₁ ++ l₂) = X.lprod l₁ * X.lprod l₂ := by
  simp [lprod]

@[expose] def StrictList (l : List (Letter A B)) : Prop :=
  (∀ g ∈ l, g.2 ∉ (X.diagram g.1).range) ∧ l.IsChain (fun a b => a.1 ≠ b.1)

theorem lprod_not_mem_base_range {l : List (Letter A B)} (hl : l ≠ []) (hs : X.StrictList l) :
    X.lprod l ∉ (PushoutI.base X.diagram).range := by
  intro hmem
  let w : CoprodI.Word (goldVertexGroup A B) :=
    ⟨l, fun g hg h1 => hs.1 g hg (h1 ▸ Subgroup.one_mem _), hs.2⟩
  have hred : PushoutI.Reduced X.diagram w := hs.1
  have hprod : PushoutI.ofCoprodI w.prod = X.lprod l := by
    simp only [CoprodI.Word.prod, lprod, w, map_list_prod, List.map_map]
    rfl
  have hw := PushoutI.Reduced.eq_empty_of_mem_range X.diagram_injective hred
    (by rw [hprod]; exact hmem)
  apply hl
  have := congrArg CoprodI.Word.toList hw
  simpa [w] using this

@[expose] def WalkNB {V : Type*} {G : SimpleGraph V} {v w : V} (p : G.Walk v w) : Prop :=
  ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

theorem WalkNB.tail {V : Type*} {G : SimpleGraph V} {v u w : V} {h : G.Adj v u}
    {p : G.Walk u w} (hnb : WalkNB (SimpleGraph.Walk.cons h p)) : WalkNB p := by
  intro i hi
  have := hnb (i + 1) (by simpa using hi)
  simpa using this

@[expose] def flipN (t : Bool) : ℕ → Bool
  | 0 => t
  | n + 1 => !(flipN t n)

theorem flipN_not (t : Bool) (n : ℕ) : flipN (!t) n = flipN t (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [flipN, ih]

theorem flipN_eq_self_iff (t : Bool) (n : ℕ) : flipN t n = t ↔ Even n := by
  induction n with
  | zero => simp [flipN]
  | succ n ih =>
    rw [flipN, Nat.even_add_one, ← ih]
    cases t <;> cases flipN _ n <;> simp

@[expose] def StrictFrom (s : Bool) (l : List (Letter A B)) : Prop :=
  X.StrictList l ∧ ∀ g ∈ l.head?, g.1 = s

theorem strictFrom_nil (s : Bool) : X.StrictFrom s [] := ⟨⟨by simp, List.isChain_nil⟩, by simp⟩

theorem strictFrom_cons {s : Bool} {g : Letter A B} {l : List (Letter A B)} (hg : g.1 = s)
    (hgr : g.2 ∉ (X.diagram g.1).range) (hl : X.StrictFrom (!s) l) :
    X.StrictFrom s (g :: l) := by
  refine ⟨⟨?_, ?_⟩, by simpa using hg⟩
  · intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hgr
    · exact hl.1.1 g' hg'
  · refine List.IsChain.cons hl.1.2 ?_
    intro y hy
    have := hl.2 y hy
    rw [this, hg]
    cases s <;> simp

theorem vtxGroup_eq_range (b : Bool) :
    X.vtxGroup b = (PushoutI.of (φ := X.diagram) b).range := by
  cases b <;> rfl

theorem exists_letter {b : Bool} {y : X.Universal} (hy : y ∈ X.vtxGroup b)
    (hyn : y ∉ X.vtxGroup (!b)) :
    ∃ g : goldVertexGroup A B b, PushoutI.of (φ := X.diagram) b g = y ∧
      g ∉ (X.diagram b).range := by
  rw [X.vtxGroup_eq_range] at hy
  obtain ⟨g, rfl⟩ := hy
  refine ⟨g, rfl, ?_⟩
  rintro ⟨c, hc⟩
  apply hyn
  rw [X.vtxGroup_eq_range]
  refine ⟨X.diagram (!b) c, ?_⟩
  rw [PushoutI.of_apply_eq_base, ← hc, PushoutI.of_apply_eq_base]

theorem lift_walk {v w : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)}
    (p : X.treeGraph.Walk v w) (hnb : WalkNB p) (hlen : 1 ≤ p.length) (t : Bool)
    (x : X.Universal) (hv : v = X.vtx t x) :
    ∃ (y₀ : X.Universal) (z : List (Letter A B)),
      y₀ ∈ X.vtxGroup t ∧ X.StrictFrom (!t) z ∧ z.length + 1 = p.length ∧
      p.getVert 1 = X.vtx (!t) (x * y₀) ∧
      w = X.vtx (flipN t p.length) (x * y₀ * X.lprod z) := by
  induction p generalizing t x with
  | nil => simp at hlen
  | @cons v u w h p' ih =>
    subst hv
    obtain ⟨y₀, hy₀, hu⟩ := (X.adj_vtx_iff t x u).mp h
    cases p' with
    | nil =>
      refine ⟨y₀, [], hy₀, X.strictFrom_nil _, by simp, ?_, ?_⟩
      · simpa using hu
      · simpa [flipN] using hu
    | @cons _ u' _ h' p'' =>
      obtain ⟨y₁, z', hy₁, hz', hl, hget, hw⟩ :=
        ih hnb.tail (by simp) (!t) (x * y₀) hu
      have h0 := hnb 0 (by simp)
      rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ, hget,
        Bool.not_not] at h0
      have hy₁n : y₁ ∉ X.vtxGroup (!(!t)) := by
        rw [Bool.not_not]
        intro hmem
        apply h0
        rw [X.vtx_mul hmem, X.vtx_mul hy₀]
      obtain ⟨g, hg, hgr⟩ := X.exists_letter hy₁ hy₁n
      refine ⟨y₀, ⟨!t, g⟩ :: z', hy₀, ?_, ?_, ?_, ?_⟩
      · exact X.strictFrom_cons rfl hgr hz'
      · simp only [List.length_cons, SimpleGraph.Walk.length_cons] at hl ⊢
        omega
      · simpa using hu
      · refine hw.trans ?_
        have hfl : flipN (!t) (SimpleGraph.Walk.cons h' p'').length =
            flipN t (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h' p'')).length :=
          flipN_not t _
        rw [hfl]
        simp only [lprod_cons, hg, mul_assoc]

theorem vtxGroup_inf_vtxGroup_not (t : Bool) :
    X.vtxGroup t ⊓ X.vtxGroup (!t) = (PushoutI.base X.diagram).range := by
  cases t
  · rw [inf_comm]
    exact X.ofA_range_inf_ofB_range
  · exact X.ofA_range_inf_ofB_range

theorem strictFrom_getLast {s : Bool} {z : List (Letter A B)} (hz : X.StrictFrom s z) :
    ∀ g ∈ z.getLast?, g.1 = flipN s (z.length - 1) := by
  induction z generalizing s with
  | nil => simp
  | cons g' l ih =>
    have hg' : g'.1 = s := hz.2 g' (by simp)
    have hl : X.StrictFrom (!s) l := by
      refine ⟨⟨fun g hg => hz.1.1 g (List.mem_cons_of_mem _ hg), hz.1.2.tail⟩, ?_⟩
      intro y hy
      have := (List.isChain_cons.mp hz.1.2).1 y hy
      cases hs : g'.1 <;> cases hy1 : y.1 <;> simp_all
    cases l with
    | nil =>
      intro g hg
      simp at hg
      subst hg
      simpa [flipN] using hg'
    | cons g'' l'' =>
      intro g hg
      rw [List.getLast?_cons_cons] at hg
      rw [ih hl g hg]
      have hlen : (g' :: g'' :: l'').length - 1 = (g'' :: l'').length - 1 + 1 := by simp
      rw [hlen, ← flipN_not]

theorem strictFrom_odd_not_mem {t : Bool} {z : List (Letter A B)} (hz : X.StrictFrom (!t) z)
    (hodd : Odd z.length) : X.lprod z ∉ X.vtxGroup t := by
  intro hmem
  have hne : z ≠ [] := by
    rintro rfl
    simp at hodd
  by_cases hu : X.lprod z ∈ X.vtxGroup (!t)
  · apply X.lprod_not_mem_base_range hne hz.1
    rw [← X.vtxGroup_inf_vtxGroup_not t]
    exact ⟨hmem, hu⟩
  · have hu' : (X.lprod z)⁻¹ ∈ X.vtxGroup t := inv_mem hmem
    have hun : (X.lprod z)⁻¹ ∉ X.vtxGroup (!t) := fun h => hu (by simpa using inv_mem h)
    obtain ⟨g, hg, hgr⟩ := X.exists_letter (b := t) hu' hun
    have hlast : ∀ y ∈ z.getLast?, y.1 = !t := by
      intro y hy
      rw [X.strictFrom_getLast hz y hy]
      obtain ⟨k, hk⟩ := hodd
      have : z.length - 1 = 2 * k := by omega
      rw [this]
      clear hy this hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
        rw [this, flipN, flipN]
        simp [ih]
    apply X.lprod_not_mem_base_range (l := z ++ [⟨t, g⟩]) (by simp)
    · refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hz.1.1 y hy
        · rw [List.mem_singleton] at hy
          subst hy
          exact hgr
      · refine List.IsChain.append hz.1.2 (List.isChain_singleton _) ?_
        intro x hx y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy
        have := hlast x hx
        rw [this]
        cases t <;> simp
    · rw [lprod_append]
      simp only [lprod_cons, lprod_nil, mul_one]
      rw [hg, mul_inv_cancel]
      exact one_mem _

theorem not_closed_nb {v : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)}
    (p : X.treeGraph.Walk v v) (hnb : WalkNB p) (hlen : 1 ≤ p.length) : False := by
  obtain ⟨t, x, hv⟩ : ∃ (t : Bool) (x : X.Universal), v = X.vtx t x := by
    rcases v with q | q
    · exact ⟨true, q.out, by simp [vtx]⟩
    · exact ⟨false, q.out, by simp [vtx]⟩
  obtain ⟨y₀, z, hy₀, hz, hl, -, hw⟩ := X.lift_walk p hnb hlen t x hv
  obtain ⟨hflip, hmem⟩ := (X.vtx_eq_iff t _ x _).mp (hv.symm.trans hw)
  have hmem' : y₀ * X.lprod z ∈ X.vtxGroup t := by simpa [mul_assoc] using hmem
  have hz_mem : X.lprod z ∈ X.vtxGroup t := (Subgroup.mul_mem_cancel_left _ hy₀).mp hmem'
  have heven : Even p.length := (flipN_eq_self_iff t p.length).mp hflip.symm
  have hodd : Odd z.length := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  exact X.strictFrom_odd_not_mem hz hodd hz_mem

theorem WalkNB.of_isCycle {V : Type*} {G : SimpleGraph V} {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) : WalkNB c := by
  intro i hi
  have h3 := hc.three_le_length
  have hinj := hc.getVert_injOn
  by_cases h0 : i = 0
  · subst h0
    intro h
    rw [SimpleGraph.Walk.getVert_zero] at h
    have h2 : c.getVert 2 = c.getVert c.length := by
      rw [SimpleGraph.Walk.getVert_length]
      exact h.symm
    have := hinj (show 2 ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega)
      (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega) h2
    omega
  · intro h
    have := hinj (show i ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega)
      (show i + 2 ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega) h
    omega

theorem treeGraph_isAcyclic : X.treeGraph.IsAcyclic := by
  intro v c hc
  exact X.not_closed_nb c (WalkNB.of_isCycle hc) (by have := hc.three_le_length; omega)

theorem treeGraph_isTree : X.treeGraph.IsTree :=
  ⟨X.universalCompletion.cosetGraph_connected, X.treeGraph_isAcyclic⟩

end GoldAmalgam

end CFSG.Quasithin
