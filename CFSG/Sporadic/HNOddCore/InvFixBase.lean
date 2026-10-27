
module

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.XCheckBase
public import CFSG.Sporadic.HNOddCore.DCheckBase
public import CFSG.Sporadic.HNOddCore.Restrict
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

theorem isChain_of_zip_tail' : ∀ {L : List ℕ}, (∀ p ∈ L.zip L.tail, p.1 < p.2) →
    L.IsChain (· < ·)
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: L, h => by
    rw [List.isChain_cons]
    refine ⟨fun y hy => ?_, isChain_of_zip_tail' fun p hp => h p ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact h (a, b) (by simp)
    · rw [List.tail_cons, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp

theorem card_filter_range_eq_countP' (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range n).filter p).card = (List.range n).countP fun i => decide (p i) := by
  rw [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]

theorem fixList_spec {n : ℕ} {t : Array ℕ} {g : Perm (Fin n)} {L : List ℕ} (hrep : PRep n t g)
    (h : fixListOK n t L = true) :
    (∀ x : Fin n, g x = x ↔ x.val ∈ L) ∧
      (Finset.univ.filter fun x : Fin n => g x = x).card = L.length := by
  unfold fixListOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsort, hfix⟩, hcount⟩ := h
  have hnodup : L.Nodup :=
    ((isChain_of_zip_tail' hsort).pairwise).imp fun h => ne_of_lt h
  have hfixed : ∀ x : Fin n, g x = x ↔ t[x.val]! = x.val := by
    intro x
    rw [hrep x]
    exact ⟨fun e => by rw [e], fun e => Fin.ext e⟩
  set S := (Finset.range n).filter fun i => t[i]! = i
  have hS : S.card = L.length := by
    rw [card_filter_range_eq_countP', ← hcount]
    congr 1
  have hsub : L.toFinset ⊆ S := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨hxn, hxt⟩ := hfix x hx
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hxn, hxt⟩
  have hSL : S = L.toFinset := (Finset.eq_of_subset_of_card_le hsub (by
    rw [hS, List.toFinset_card_of_nodup hnodup])).symm
  have hmem : ∀ x : Fin n, g x = x ↔ x.val ∈ L := by
    intro x
    rw [hfixed, ← List.mem_toFinset, ← hSL]
    simp [S, x.isLt]
  refine ⟨hmem, ?_⟩
  rw [← hS]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [hSL, List.mem_toFinset]
    exact (hmem x).1 hx.2
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro i hi
    have hi' := Finset.mem_filter.1 hi
    refine ⟨⟨i, Finset.mem_range.1 hi'.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hfixed _).2 hi'.2⟩

theorem card_fix_eq {n : ℕ} {g : Perm (Fin n)} :
    Nat.card {x : Fin n // g x = x} = (Finset.univ.filter fun x : Fin n => g x = x).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cTab_eq : cTab hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)
    hStrongArr = cRec := by
  rw [cRec_eq, cABTab_eq, kTab_eq, wTab_eq, dTab_eq, uTab_eq, parTab_eq]
  rfl

end CFSG.Sporadic.HNOddCore
