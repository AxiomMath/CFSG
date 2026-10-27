module

public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public import CFSG.Sporadic.Th.TableSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem tblEq_iff {S T : Table} : tblEq n S T = true ↔ ∀ i < n, ap S i = ap T i := by
  rw [tblEq, allIn_eq_true]
  exact ⟨fun h i hi => beq_iff_eq.1 (h i (Nat.zero_le _) hi),
    fun h i _ hi => beq_iff_eq.2 (h i hi)⟩

theorem rep_of_tblEq {S T : Table} {g : G} (hS : Rep n S g) (h : tblEq n T S = true) :
    Rep n T g := fun i hi => ((tblEq_iff.1 h) i hi).trans (hS i hi)

theorem rep_conjT {g gi x : Table} {gg xg : G} (hg : Rep n g gg) (hgi : Rep n gi gg⁻¹)
    (hx : Rep n x xg) : Rep n (conjT n g gi x) (gg * xg * gg⁻¹) :=
  Rep.compT (Rep.compT hg hx) hgi

theorem conjTreeOK_spec (H : Subgroup G) {gens gensInv : Array Table} {gg : ℕ → G}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    {x : Table} {xg : G} (hx : Rep n x xg) {elts : Array Table} {par lab : Array ℕ}
    (h : conjTreeOK n gens gensInv x elts par lab = true) :
    ∀ k < elts.size, ∃ c ∈ H, Rep n elts[k]! (c * xg * c⁻¹) := by
  simp only [conjTreeOK, Bool.and_eq_true, decide_eq_true_eq, allIn_eq_true] at h
  obtain ⟨⟨_, h0⟩, hk⟩ := h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk'
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, H.one_mem, by simpa using rep_of_tblEq hx h0⟩
    · obtain ⟨⟨hpar, hlab⟩, heq⟩ := hk k hpos hk'
      obtain ⟨c, hc, hrep⟩ := ih _ hpar (hpar.trans hk')
      obtain ⟨hgl, hgil, hgH⟩ := hg _ hlab
      refine ⟨gg lab[k]! * c, H.mul_mem hgH hc, ?_⟩
      have := rep_of_tblEq (rep_conjT hgl hgil hrep) heq
      simpa only [mul_inv_rev, mul_assoc] using this

@[expose] noncomputable def keyOf (n : ℕ) [MulAction G (Fin n)] (g : G) : ℕ :=
  (List.range n).foldr (fun i acc => idx n g i + n * acc) 0

theorem key_eq_keyOf {T : Table} {g : G} (h : Rep n T g) : key n T = keyOf n g := by
  have : ∀ l : List ℕ, (∀ i ∈ l, i < n) →
      l.foldr (fun i acc => ap T i + n * acc) 0 = l.foldr (fun i acc => idx n g i + n * acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih fun j hj => hl j (List.mem_cons_of_mem i hj),
        h i (hl i List.mem_cons_self)]
  exact this _ fun i hi => List.mem_range.1 hi

theorem pairwise_of_strictlyIncreasing :
    ∀ {l : List ℕ}, strictlyIncreasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have hbl := pairwise_of_strictlyIncreasing h.2
    refine List.Pairwise.cons (fun c hc => ?_) hbl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons hbl hc)

theorem map_key_eq {Ts : List Table} {gs : List G} (h : List.Forall₂ (Rep n) Ts gs) :
    Ts.map (key n) = gs.map (keyOf n) := by
  induction h with
  | nil => rfl
  | cons hT _ ih => rw [List.map_cons, List.map_cons, ih, key_eq_keyOf hT]

theorem nodup_of_keysDistinct {Ts : List Table} {gs : List G} (h : List.Forall₂ (Rep n) Ts gs)
    (hk : keysDistinct n Ts = true) : gs.Nodup := by
  have hsorted := (pairwise_of_strictlyIncreasing hk).imp (fun hab => Nat.ne_of_lt hab)
  have hkeys : (Ts.map (key n)).Nodup := (List.mergeSort_perm _ _).nodup_iff.1 hsorted
  rw [map_key_eq h] at hkeys
  exact List.Nodup.of_map _ hkeys

end CFSG.Sporadic.Schreier
