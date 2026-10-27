module

public import CFSG.Quasithin.Background.HMathieuEnum
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Quasithin.B45Exc.Tab

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.H.Mathieu
  CFSG.QuasithinUnique.Setup.X1

@[expose] def commA (n : ℕ) (a b : Array ℕ) : Bool := allLt n fun p => a[b[p]!]! == b[a[p]!]!

@[expose] def prodOK (n : ℕ) (a b c : Array ℕ) : Bool :=
  allLt n fun p => a[b[p]!]! == c[p]! && b[a[p]!]! == c[p]!

@[expose] def ncAt (n : ℕ) (pts : List ℕ) (a b : Array ℕ) : Bool :=
  pts.any fun p => decide (p < n) && a[b[p]!]! != b[a[p]!]!

structure InvTab (n : ℕ) where
  xs : Array (Array ℕ)
  pts : List ℕ
  comm : Array (Array Bool)
  prod : Array (Array ℕ)

namespace InvTab

variable {n : ℕ} (T : InvTab n)

@[expose] def m : ℕ := T.xs.size

@[expose] def elt (i : ℕ) : Array ℕ := if i < T.m then T.xs[i]! else idA n

@[expose] def key (a : Array ℕ) : List ℕ := T.pts.map fun p => a[p]!

@[expose] def commAt (i j : ℕ) : Bool := if i < T.m ∧ j < T.m then (T.comm[i]!)[j]! else true

@[expose] def prodAt (i j : ℕ) : ℕ :=
  if i < T.m then (if j < T.m then (T.prod[i]!)[j]! else i) else j

@[expose] def pairOK (i j : ℕ) : Bool :=
  if T.commAt i j then
    decide (T.prodAt i j ≤ T.m) && prodOK n T.xs[i]! T.xs[j]! (T.elt (T.prodAt i j))
  else ncAt n T.pts T.xs[i]! T.xs[j]!

@[expose] def symOK (i j : ℕ) : Bool := T.commAt i j == T.commAt j i && T.prodAt i j == T.prodAt j i

@[expose] def check (chunks : ℕ) : Bool :=
  T.pts.all (· < n) &&
  allLt T.m (fun i => isInvA n T.xs[i]! T.xs[i]! && !eqA n T.xs[i]! (idA n)) &&
  allLt T.m (fun i => allLt i fun j => T.key T.xs[i]! != T.key T.xs[j]!) &&
  parLt T.m chunks (fun i => allLt T.m fun j => if j < i then T.symOK i j else T.pairOK i j)

@[expose] def subprodsI : List ℕ → List ℕ
  | [] => [T.m]
  | y :: l => subprodsI l ++ (subprodsI l).map (T.prodAt y)

@[expose] def startI : List ℕ → ℕ
  | [] => 0
  | a :: _ => a + 1

@[expose] def greedyExtI (l : List ℕ) : List ℕ :=
  let S := T.subprodsI l
  ((List.range T.m).drop (startI l)).filter fun x =>
    (l.all fun y => T.commAt x y) && !(S.contains x) &&
      (S.all fun s => s == T.m || decide (x < T.prodAt x s))

@[expose] def forallGreedyI (pred : List ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, l => pred l
  | k + 1, l => (T.greedyExtI l).all fun x => forallGreedyI pred k (x :: l)

@[expose] def build (n : ℕ) (xs : Array (Array ℕ)) (pts : List ℕ) : InvTab n :=
  let m := xs.size
  let keyOf (a : Array ℕ) : List ℕ := pts.map fun p => a[p]!
  let keyMul (a b : Array ℕ) : List ℕ := pts.map fun p => a[b[p]!]!
  let index : Std.HashMap (List ℕ) ℕ :=
    (List.range m).foldl (fun h i => h.insert (keyOf xs[i]!) i)
      ((∅ : Std.HashMap (List ℕ) ℕ).insert (keyOf (idA n)) m)
  let comm : Array (Array Bool) :=
    Array.ofFn (n := m) fun i => Array.ofFn (n := m) fun j =>
      keyMul xs[i.val]! xs[j.val]! == keyMul xs[j.val]! xs[i.val]!
  let prod : Array (Array ℕ) :=
    Array.ofFn (n := m) fun i => Array.ofFn (n := m) fun j =>
      if (comm[i.val]!)[j.val]! then index.getD (keyMul xs[i.val]! xs[j.val]!) (m + 1) else 0
  { xs := xs, pts := pts, comm := comm, prod := prod }

end InvTab

namespace InvTab

variable {n : ℕ} {T : InvTab n}

@[expose] noncomputable def perm (T : InvTab n) (i : ℕ) : Equiv.Perm (Fin n) :=
  if i < T.m then permOfArr n T.xs[i]! else 1

theorem perm_of_le {i : ℕ} (hi : T.m ≤ i) : T.perm i = 1 := by
  rw [perm, ite_eq_right (by omega)]

theorem commA_iff {n : ℕ} {a b : Array ℕ} {g h : Equiv.Perm (Fin n)} (ha : Rep n a g)
    (hb : Rep n b h) : commA n a b = true ↔ g * h = h * g := by
  rw [commA, allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rw [beq_iff_eq, hb.apply x.2, ha.apply (h x).2, ha.apply x.2, hb.apply (g x).2] at this
    simpa [Equiv.Perm.mul_apply] using this
  · intro H p hp
    rw [beq_iff_eq, hb.apply hp, ha.apply (h ⟨p, hp⟩).2, ha.apply hp, hb.apply (g ⟨p, hp⟩).2]
    have := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ ⟨p, hp⟩ : Fin n) : ℕ)) H
    simpa [Equiv.Perm.mul_apply] using this

theorem prodOK_spec {n : ℕ} {a b c : Array ℕ} {g h k : Equiv.Perm (Fin n)} (ha : Rep n a g)
    (hb : Rep n b h) (hc : Rep n c k) (H : prodOK n a b c = true) : g * h = k ∧ h * g = k := by
  rw [prodOK, allLt_iff] at H
  constructor
  · refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
    rw [Equiv.Perm.mul_apply, ← ha (h x), ← hb x, ← hc x]
    exact this.1
  · refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
    rw [Equiv.Perm.mul_apply, ← hb (g x), ← ha x, ← hc x]
    exact this.2

theorem ncAt_spec {n : ℕ} {pts : List ℕ} {a b : Array ℕ} {g h : Equiv.Perm (Fin n)}
    (ha : Rep n a g) (hb : Rep n b h) (H : ncAt n pts a b = true) : g * h ≠ h * g := by
  rw [ncAt, List.any_eq_true] at H
  obtain ⟨p, -, hp⟩ := H
  rw [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hp
  obtain ⟨hpn, hne⟩ := hp
  intro hgh
  apply hne
  have e := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ ⟨p, hpn⟩ : Fin n) : ℕ)) hgh
  simp only [Equiv.Perm.mul_apply] at e
  rw [hb.apply hpn, ha.apply (h ⟨p, hpn⟩).2, ha.apply hpn, hb.apply (g ⟨p, hpn⟩).2]
  exact e

section Spec

variable {c : ℕ} (hc : 0 < c) (hT : T.check c = true)
include hc hT

theorem check_parts : (∀ p ∈ T.pts, p < n) ∧
    (∀ i < T.m, isInvA n T.xs[i]! T.xs[i]! = true ∧ eqA n T.xs[i]! (idA n) = false) ∧
      (∀ i < T.m, ∀ j < i, T.key T.xs[i]! ≠ T.key T.xs[j]!) ∧
      ∀ i < T.m, ∀ j < T.m, (if j < i then T.symOK i j else T.pairOK i j) = true := by
  simp only [check, Bool.and_eq_true] at hT
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hT
  refine ⟨fun p hp => ?_, fun i hi => ?_, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · have := List.all_eq_true.1 h0 p hp
    simpa using this
  · have := allLt_spec h1 hi
    simpa [Bool.and_eq_true] using this
  · have := allLt_spec (allLt_spec h2 hi) hj
    simpa using this
  · exact allLt_spec (parLt_spec hc h3 i hi) hj

theorem rep_elt {i : ℕ} : Rep n (T.elt i) (T.perm i) := by
  by_cases hi : i < T.m
  · have h := ((check_parts hc hT).2.1 i hi).1
    rw [elt, ite_eq_left hi, perm, ite_eq_left hi]
    exact (rep_permOfArr h).1
  · rw [elt, ite_eq_right hi, perm, ite_eq_right hi]
    exact rep_idA

theorem rep_xs {i : ℕ} (hi : i < T.m) : Rep n T.xs[i]! (T.perm i) := by
  have := rep_elt hc hT (i := i)
  rwa [elt, ite_eq_left hi] at this

theorem perm_mul_self {i : ℕ} (hi : i < T.m) : T.perm i * T.perm i = 1 := by
  have h := ((check_parts hc hT).2.1 i hi).1
  have h1 := rep_xs hc hT hi
  have h2 := rep_inv_of_isInvA h1 h
  have : T.perm i = (T.perm i)⁻¹ := h1.unique h2
  calc T.perm i * T.perm i = T.perm i * (T.perm i)⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel _

theorem perm_ne_one {i : ℕ} (hi : i < T.m) : T.perm i ≠ 1 := by
  intro h
  have h1 := ((check_parts hc hT).2.1 i hi).2
  have h2 : eqA n T.xs[i]! (idA n) = true := (eqA_iff (rep_xs hc hT hi) rep_idA).2 h
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem key_eq_of_perm_eq {i j : ℕ} (hi : i < T.m) (hj : j < T.m) (h : T.perm i = T.perm j) :
    T.key T.xs[i]! = T.key T.xs[j]! := by
  rw [key, key]
  refine List.map_congr_left fun p hp => ?_
  have hpn := (check_parts hc hT).1 p hp
  rw [(rep_xs hc hT hi).apply hpn, (rep_xs hc hT hj).apply hpn, h]

theorem perm_inj {i j : ℕ} (hi : i ≤ T.m) (hj : j ≤ T.m) (h : T.perm i = T.perm j) : i = j := by
  rcases Nat.lt_or_ge i T.m with hi' | hi' <;> rcases Nat.lt_or_ge j T.m with hj' | hj'
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (check_parts hc hT).2.2.1 j hj' i hlt (key_eq_of_perm_eq hc hT hj' hi' h.symm)
    · exact (check_parts hc hT).2.2.1 i hi' j hlt (key_eq_of_perm_eq hc hT hi' hj' h)
  · rw [perm_of_le hj'] at h
    exact absurd h (perm_ne_one hc hT hi')
  · rw [perm_of_le hi'] at h
    exact absurd h.symm (perm_ne_one hc hT hj')
  · omega

theorem perm_eq_one_iff {i : ℕ} (hi : i ≤ T.m) : T.perm i = 1 ↔ i = T.m := by
  constructor
  · intro h
    exact perm_inj hc hT hi le_rfl (h.trans (perm_of_le le_rfl).symm)
  · rintro rfl
    exact perm_of_le le_rfl

theorem pairOK_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < T.m) : T.pairOK i j = true := by
  have := (check_parts hc hT).2.2.2 i (by omega) j hj
  rwa [ite_eq_right (by omega)] at this

theorem symOK_of_lt {i j : ℕ} (hji : j < i) (hi : i < T.m) :
    T.commAt i j = T.commAt j i ∧ T.prodAt i j = T.prodAt j i := by
  have := (check_parts hc hT).2.2.2 i hi j (by omega)
  rw [ite_eq_left hji, symOK, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
  exact this

theorem spec_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < T.m) :
    (T.commAt i j = true ↔ T.perm i * T.perm j = T.perm j * T.perm i) ∧
      (T.commAt i j = true → T.prodAt i j ≤ T.m ∧ T.perm i * T.perm j = T.perm (T.prodAt i j)) := by
  have hi : i < T.m := by omega
  have hp := pairOK_of_le hc hT hij hj
  unfold pairOK at hp
  by_cases hca : T.commAt i j = true
  · rw [ite_eq_left hca, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hle, hpr⟩ := hp
    obtain ⟨h1, h2⟩ := prodOK_spec (rep_xs hc hT hi) (rep_xs hc hT hj) (rep_elt hc hT) hpr
    exact ⟨⟨fun _ => h1.trans h2.symm, fun _ => hca⟩, fun _ => ⟨hle, h1⟩⟩
  · rw [ite_eq_right hca] at hp
    have hnc := ncAt_spec (rep_xs hc hT hi) (rep_xs hc hT hj) hp
    exact ⟨⟨fun h => absurd h hca, fun h => absurd h hnc⟩, fun h => absurd h hca⟩

theorem commAt_iff {i j : ℕ} :
    T.commAt i j = true ↔ T.perm i * T.perm j = T.perm j * T.perm i := by
  by_cases hij : i < T.m ∧ j < T.m
  · rcases le_or_gt i j with hle | hlt
    · exact (spec_of_le hc hT hle hij.2).1
    · rw [(symOK_of_lt hc hT hlt hij.1).1, (spec_of_le hc hT (le_of_lt hlt) hij.1).1]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  · have htrue : T.commAt i j = true := by
      rw [commAt, ite_eq_right hij]
    refine ⟨fun _ => ?_, fun _ => htrue⟩
    rcases not_and_or.1 hij with h | h
    · rw [perm_of_le (not_lt.1 h), one_mul, mul_one]
    · rw [perm_of_le (not_lt.1 h), one_mul, mul_one]

theorem prodAt_spec {i j : ℕ} (hi : i ≤ T.m) (hj : j ≤ T.m) (hcij : T.commAt i j = true) :
    T.prodAt i j ≤ T.m ∧ T.perm i * T.perm j = T.perm (T.prodAt i j) := by
  by_cases hi' : i < T.m
  · by_cases hj' : j < T.m
    · rcases le_or_gt i j with hle | hlt
      · exact (spec_of_le hc hT hle hj').2 hcij
      · obtain ⟨hcs, hps⟩ := symOK_of_lt hc hT hlt hi'
        rw [hcs] at hcij
        obtain ⟨hle, heq⟩ := (spec_of_le hc hT (le_of_lt hlt) hi').2 hcij
        have hcomm := (commAt_iff hc hT).1 hcij
        rw [hps]
        exact ⟨hle, hcomm.symm.trans heq⟩
    · have hjm : j = T.m := by omega
      subst hjm
      rw [prodAt, ite_eq_left hi', ite_eq_right (lt_irrefl _), perm_of_le le_rfl, mul_one]
      exact ⟨le_of_lt hi', rfl⟩
  · have him : i = T.m := by omega
    subst him
    rw [prodAt, ite_eq_right (lt_irrefl _), perm_of_le le_rfl, one_mul]
    exact ⟨hj, rfl⟩

end Spec

end InvTab

namespace InvTab

variable {n : ℕ} {T : InvTab n}

@[expose] noncomputable def rinv (T : InvTab n) : List (Equiv.Perm (Fin n)) :=
  (List.range T.m).map T.perm

@[expose] def IsChain (T : InvTab n) (l : List ℕ) : Prop :=
  (∀ a ∈ l, a < T.m) ∧ ∀ a ∈ l, ∀ b ∈ l, T.commAt a b = true

@[expose] noncomputable def predOf (T : InvTab n) (pred : List ℕ → Bool) :
    List (Equiv.Perm (Fin n)) → Bool := fun l => pred (l.map (pos T.rinv))

theorem IsChain.cons {l : List ℕ} {x : ℕ} (hl : T.IsChain l) (hx : x < T.m)
    (hxl : ∀ y ∈ l, T.commAt x y = true) (hlx : ∀ y ∈ l, T.commAt y x = true)
    (hxx : T.commAt x x = true) : T.IsChain (x :: l) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · rcases List.mem_cons.1 ha with h | h
    · rw [h]
      exact hx
    · exact hl.1 a h
  · rcases List.mem_cons.1 ha with h | h <;> rcases List.mem_cons.1 hb with h' | h'
    · rw [h, h']
      exact hxx
    · rw [h]
      exact hxl b h'
    · rw [h']
      exact hlx a h
    · exact hl.2 a h b h'

theorem all_congr_mem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

section Sim

variable {c : ℕ} (hc : 0 < c) (hT : T.check c = true)
include hc hT

theorem pos_perm {i : ℕ} (hi : i ≤ T.m) : pos T.rinv (T.perm i) = i := by
  have key : ∀ k ≤ T.m, ∀ i ≤ k, ((List.range k).map T.perm).idxOf (T.perm i) = i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      rfl
    | succ k ih =>
      intro hk i hik
      have hnot : T.perm i ∉ (List.range k).map T.perm → True := fun _ => trivial
      clear hnot
      rw [List.range_succ, List.map_append, List.map_singleton]
      rcases Nat.lt_or_ge i k with hlt | hge
      · have hmem : T.perm i ∈ (List.range k).map T.perm :=
          List.mem_map.2 ⟨i, List.mem_range.2 hlt, rfl⟩
        rw [List.idxOf_append_of_mem hmem]
        exact ih (by omega) i (le_of_lt hlt)
      · have hnm : T.perm i ∉ (List.range k).map T.perm := by
          intro h
          obtain ⟨j, hj, hji⟩ := List.mem_map.1 h
          have := perm_inj hc hT (by have := List.mem_range.1 hj; omega) (by omega) hji
          have := List.mem_range.1 hj
          omega
        rw [List.idxOf_append_of_notMem hnm, List.length_map, List.length_range]
        rcases Nat.lt_or_ge k i with hlt' | hle'
        · have hnm' : T.perm i ∉ [T.perm k] := by
            rw [List.mem_singleton]
            intro h
            have := perm_inj hc hT (by omega) (by omega) h
            omega
          rw [List.idxOf_eq_length hnm', List.length_singleton]
          omega
        · have hik' : i = k := by omega
          subst hik'
          rw [List.idxOf_cons_self]
          rfl
  exact key T.m le_rfl i hi

theorem subprods_map {l : List ℕ} (hl : T.IsChain l) :
    (∀ s ∈ T.subprodsI l, s ≤ T.m) ∧ subprods (l.map T.perm) = (T.subprodsI l).map T.perm := by
  induction l with
  | nil => exact ⟨by simp [subprodsI], by simp [subprodsI, subprods, perm_of_le le_rfl]⟩
  | cons y l ih =>
    have hl' : T.IsChain l :=
      ⟨fun a ha => hl.1 a (List.mem_cons_of_mem y ha),
        fun a ha b hb => hl.2 a (List.mem_cons_of_mem y ha) b (List.mem_cons_of_mem y hb)⟩
    obtain ⟨hle, heq⟩ := ih hl'
    have hy : y < T.m := hl.1 y List.mem_cons_self
    have hcomm : ∀ s ∈ T.subprodsI l, T.commAt y s = true := by
      intro s hs
      rw [commAt_iff hc hT]
      have hyl : ∀ x ∈ l.map T.perm, T.perm y * x = x * T.perm y := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact (commAt_iff hc hT).1 (hl.2 y List.mem_cons_self a (List.mem_cons_of_mem y ha))
      have hsm : T.perm s ∈ subprods (l.map T.perm) := by
        rw [heq]
        exact List.mem_map.2 ⟨s, hs, rfl⟩
      exact commute_subprods hyl _ hsm
    refine ⟨fun s hs => ?_, ?_⟩
    · simp only [subprodsI, List.mem_append, List.mem_map] at hs
      rcases hs with hs | ⟨t, ht, rfl⟩
      · exact hle s hs
      · exact (prodAt_spec hc hT (le_of_lt hy) (hle t ht) (hcomm t ht)).1
    · rw [List.map_cons, subprods, heq, subprodsI, List.map_append, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      exact (prodAt_spec hc hT (le_of_lt hy) (hle s hs) (hcomm s hs)).2

theorem mem_subprods_map_iff {l : List ℕ} (hl : T.IsChain l) {x : ℕ} (hx : x ≤ T.m) :
    T.perm x ∈ subprods (l.map T.perm) ↔ x ∈ T.subprodsI l := by
  obtain ⟨hle, heq⟩ := subprods_map hc hT hl
  rw [heq, List.mem_map]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rwa [← perm_inj hc hT (hle s hs) hx hsx]
  · intro h
    exact ⟨x, h, rfl⟩

theorem greedyExt_map {l : List ℕ} (hl : T.IsChain l) :
    greedyExt T.rinv (l.map T.perm) = (T.greedyExtI l).map T.perm := by
  obtain ⟨hle, heq⟩ := subprods_map hc hT hl
  have hst : startPos T.rinv (l.map T.perm) = startI l := by
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [List.map_cons, startPos, startI]
      rw [pos_perm hc hT (le_of_lt (hl.1 a List.mem_cons_self))]
  unfold greedyExt greedyExtI
  rw [hst, show T.rinv.drop (startI l) = ((List.range T.m).drop (startI l)).map T.perm by
    rw [rinv, List.map_drop], List.filter_map]
  dsimp only
  congr 1
  apply List.filter_congr
  intro x hx
  have hxm : x < T.m := List.mem_range.1 (List.mem_of_mem_drop hx)
  simp only [Function.comp_apply]
  have h1 : ((l.map T.perm).all fun y => decide (T.perm x * y = y * T.perm x)) =
      l.all fun y => T.commAt x y := by
    rw [List.all_map]
    refine all_congr_mem fun y _ => ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, commAt_iff hc hT]
  have h2 : decide (T.perm x ∈ subprods (l.map T.perm)) = (T.subprodsI l).contains x := by
    rw [List.contains_eq_mem, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact mem_subprods_map_iff hc hT hl (le_of_lt hxm)
  have h3 : (l.all fun y => T.commAt x y) = true →
      ((subprods (l.map T.perm)).all fun s =>
        decide (s = 1) || decide (pos T.rinv (T.perm x) < pos T.rinv (T.perm x * s))) =
      (T.subprodsI l).all fun s => s == T.m || decide (x < T.prodAt x s) := by
    intro hxl
    rw [heq, List.all_map]
    refine all_congr_mem fun s hs => ?_
    simp only [Function.comp_apply]
    have hsm := hle s hs
    have hcs : T.commAt x s = true := by
      rw [commAt_iff hc hT]
      have hxl' : ∀ z ∈ l.map T.perm, T.perm x * z = z * T.perm x := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
        exact (commAt_iff hc hT).1 (List.all_eq_true.1 hxl a ha)
      have hsm' : T.perm s ∈ subprods (l.map T.perm) := by
        rw [heq]
        exact List.mem_map.2 ⟨s, hs, rfl⟩
      exact commute_subprods hxl' _ hsm'
    obtain ⟨hpm, hpe⟩ := prodAt_spec hc hT (le_of_lt hxm) hsm hcs
    rw [hpe, pos_perm hc hT (le_of_lt hxm), pos_perm hc hT hpm]
    have : decide (T.perm s = 1) = (s == T.m) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
      exact perm_eq_one_iff hc hT hsm
    rw [this]
  rw [h1, h2]
  cases hA : (l.all fun y => T.commAt x y)
  · simp
  · rw [h3 hA]


theorem map_pos_perm {l : List ℕ} (hl : ∀ a ∈ l, a ≤ T.m) :
    (l.map T.perm).map (pos T.rinv) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => pos_perm hc hT (hl a ha)

theorem forallGreedy_map (pred : List ℕ → Bool) :
    ∀ (k : ℕ) {l : List ℕ}, T.IsChain l →
      forallGreedy T.rinv (T.predOf pred) k (l.map T.perm) = T.forallGreedyI pred k l := by
  intro k
  induction k with
  | zero =>
    intro l hl
    simp only [forallGreedy, forallGreedyI, predOf]
    rw [map_pos_perm hc hT fun a ha => le_of_lt (hl.1 a ha)]
  | succ k ih =>
    intro l hl
    simp only [forallGreedy, forallGreedyI]
    rw [greedyExt_map hc hT hl, List.all_map]
    refine all_congr_mem fun x hx => ?_
    simp only [Function.comp_apply]
    have hx' := hx
    unfold greedyExtI at hx'
    rw [List.mem_filter] at hx'
    obtain ⟨hxr, hxc⟩ := hx'
    have hxm : x < T.m := List.mem_range.1 (List.mem_of_mem_drop hxr)
    simp only [Bool.and_eq_true] at hxc
    have hxl : ∀ y ∈ l, T.commAt x y = true := fun y hy => List.all_eq_true.1 hxc.1.1 y hy
    have hlx : ∀ y ∈ l, T.commAt y x = true := by
      intro y hy
      rw [commAt_iff hc hT]
      exact ((commAt_iff hc hT).1 (hxl y hy)).symm
    have hxx : T.commAt x x = true := by
      rw [commAt_iff hc hT]
    have hch : T.IsChain (x :: l) := hl.cons hxm hxl hlx hxx
    have := ih hch
    rwa [List.map_cons] at this

theorem forallGreedyI_sound {pred : List ℕ → Bool} {k : ℕ} (h : T.forallGreedyI pred k [] = true)
    (B : Subgroup (Equiv.Perm (Fin n))) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hR : ∀ x ∈ B, x ≠ 1 → ∃ i < T.m, x = T.perm i)
    (hcard : Nat.card B = 2 ^ k) :
    ∃ l : List ℕ, T.IsChain l ∧ pred l = true ∧ ∀ x, x ∈ B ↔ ∃ s ∈ T.subprodsI l, x = T.perm s := by
  classical
  have hnil : T.IsChain [] := ⟨by simp, by simp⟩
  have h' : forallGreedy T.rinv (T.predOf pred) k [] = true := by
    have := forallGreedy_map hc hT pred k hnil
    rw [List.map_nil] at this
    rw [this]
    exact h
  have hR' : ∀ x ∈ B, x ≠ 1 → x ∈ T.rinv := by
    intro x hx hx1
    obtain ⟨i, hi, rfl⟩ := hR x hx hx1
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  obtain ⟨l', -, hind, hmem, hpred⟩ := forallGreedy_sound h' B hcomm hsq hR' hcard
  have hl'B : ∀ y ∈ l', ∃ i < T.m, y = T.perm i := by
    intro y hy
    have hyB : y ∈ B := (hmem y).2 (mem_subprods_of_mem hy)
    have hci := isCommInvol_of_indepList hind
    have hy1 : y ≠ 1 := by
      clear hpred hmem
      induction hind with
      | nil => simp at hy
      | cons x l hx hx1 _ _ _ ih =>
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hx1
        · exact ih hy (isCommInvol_of_indepList ‹_›)
    exact hR y hyB hy1
  set lI := l'.map (pos T.rinv) with hlI
  have hback : lI.map T.perm = l' := by
    rw [hlI, List.map_map]
    conv_rhs => rw [← List.map_id l']
    refine List.map_congr_left fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := hl'B y hy
    simp only [Function.comp_apply, id]
    rw [pos_perm hc hT (le_of_lt hi)]
  have hlt : ∀ a ∈ lI, a < T.m := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, rfl⟩ := hl'B y hy
    rw [pos_perm hc hT (le_of_lt hi)]
    exact hi
  have hch : T.IsChain lI := by
    refine ⟨hlt, fun a ha b hb => ?_⟩
    rw [commAt_iff hc hT]
    have hci := isCommInvol_of_indepList hind
    have ha' : T.perm a ∈ l' := by rw [← hback]; exact List.mem_map.2 ⟨a, ha, rfl⟩
    have hb' : T.perm b ∈ l' := by rw [← hback]; exact List.mem_map.2 ⟨b, hb, rfl⟩
    exact hci.2 _ ha' _ hb'
  refine ⟨lI, hch, hpred, fun x => ?_⟩
  rw [hmem, ← hback, (subprods_map hc hT hch).2, List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

end Sim

end InvTab

end CFSG.Quasithin.B45Exc.Tab
