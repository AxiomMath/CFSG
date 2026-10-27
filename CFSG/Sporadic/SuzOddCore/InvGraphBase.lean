
module

public import CFSG.Sporadic.SuzOddCore.InvPerms
public import CFSG.Certificates.NativeRefine
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Mathlib.Data.Fintype.Card

@[expose] public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_bPair
    {k : ℕ} (hk : k < (#[b0Arr, b1Arr] : Array (Array ℕ)).size) :
    Rep 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[k]! (smallGs k) := by
  have hk2 : k < 2 := hk
  interval_cases k
  · exact rep_b0
  · exact rep_b1

theorem suzM_eq_closure_gens :
    suzM =
      Subgroup.closure {g | ∃ k < (#[b0Arr, b1Arr] : Array (Array ℕ)).size, smallGs k = g} := by
  rw [suzM]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.size_toArray,
    List.length_cons, List.length_nil]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; rfl
    · right; rfl

theorem ncard_finSet {n : ℕ} {l : List ℕ} (hl : PointList n l) : (finSet n l).ncard = l.length := by
  classical
  have hset : finSet n l =
      ((l.pmap (fun x hx => (⟨x, hx⟩ : Fin n)) fun x hx => hl.lt x hx).toFinset : Set (Fin n)) := by
    ext p
    simp only [finSet, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_pmap]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_pmap]
  exact hl.sorted.nodup.pmap fun a _ b _ h => congrArg Fin.val h

end CFSG.Sporadic.SuzOddCore
