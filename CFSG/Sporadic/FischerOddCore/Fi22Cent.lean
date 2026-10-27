module

public import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def fi22CentPerm (L : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (fi22CentArr L)

theorem rep_fi22CentPerm
    {L : ℕ} (hL : L < 306) : Rep 3510 (fi22CentArr L) (fi22CentPerm L) :=
  (rep_permOfArr (fi22Cent_check.2.1 L hL)).1

theorem rep_fi22CentPerm_inv {L : ℕ} (hL : L < 306) :
    Rep 3510 (invCand 3510 (fi22CentArr L)) (fi22CentPerm L)⁻¹ :=
  (rep_permOfArr (fi22Cent_check.2.1 L hL)).2

@[expose] def fi22CentCase (c : ℕ) : ℕ := fi22CentCases.getD c 0

@[expose] def fi22CentT (c : ℕ) : Equiv.Perm (Fin 3510) := fi22ExtRep (fi22CentCase c)

@[expose] def fi22CentStrong (c : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := fi22CentStrongCount.getD c 0) fun j =>
    fi22CentArr (fi22CentStrongStart.getD c 0 + j.val)

abbrev fi22CentK (c : ℕ) : ℕ := min (fi22CentGenCount.getD c 0) (fi22CentStrong c).size

@[expose] def fi22HChain (c : ℕ) : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by decide) (fi22CentStrong c) (fi22CentK c)
    (Nat.min_le_right _ _) (fi22FinList 3510 (by decide) [0, 1, 2, 3, 6, 4]) (by decide)
    (fi22WordsArr (fi22CentGenCount.getD c 0) (fi22CentStrongCount.getD c 0)
      (fi22CentDerivations.getD c []))

@[expose] def fi22H (c : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) := (fi22HChain c).originalSubgroup

theorem fi22CentK_eq
    {c : ℕ} (hc : c < 5) : fi22CentK c = fi22CentGenCount.getD c 0 := by
  rw [fi22CentK, fi22CentStrong, Array.size_ofFn]
  obtain ⟨-, -, -, -, hs, hg, -⟩ := fi22Cent_check
  rw [hs, hg]
  interval_cases c <;> rfl

theorem fi22CentStrong_get {c : ℕ} (_hc : c < 5) {j : ℕ}
    (hj : j < fi22CentStrongCount.getD c 0) :
    (fi22CentStrong c)[j]! = fi22CentArr (fi22CentStrongStart.getD c 0 + j) := by
  rw [fi22CentStrong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem fi22CentStrong_line_lt {c : ℕ} (hc : c < 5) {j : ℕ}
    (hj : j < fi22CentStrongCount.getD c 0) : fi22CentStrongStart.getD c 0 + j < 306 := by
  obtain ⟨-, -, -, hst, hs, -⟩ := fi22Cent_check
  rw [hst]
  rw [hs] at hj
  interval_cases c <;> simp at hj ⊢ <;> omega

theorem fi22H_eq_closure {c : ℕ} (hc : c < 5) :
    fi22H c = Subgroup.closure
      {g | ∃ j < fi22CentGenCount.getD c 0,
        fi22CentPerm (fi22CentStrongStart.getD c 0 + j) = g} := by
  rw [fi22H, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ (fi22HChain c).original.toList ↔ _
  rw [fi22HChain, RawSchreierDatum.mem_ofArrays_original, Set.mem_ofPred_eq, fi22CentK_eq hc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j, hj, ?_⟩
    have hjs : j < fi22CentStrongCount.getD c 0 := by
      obtain ⟨-, -, -, -, hs, hg, -⟩ := fi22Cent_check
      rw [hs]; rw [hg] at hj
      interval_cases c <;> simp at hj ⊢ <;> omega
    rw [fi22CentPerm, fi22CentStrong_get hc hjs]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j, hj, ?_⟩
    have hjs : j < fi22CentStrongCount.getD c 0 := by
      obtain ⟨-, -, -, -, hs, hg, -⟩ := fi22Cent_check
      rw [hs]; rw [hg] at hj
      interval_cases c <;> simp at hj ⊢ <;> omega
    rw [fi22CentPerm, fi22CentStrong_get hc hjs]

@[expose] def fi22CentC : Equiv.Perm (Fin 3510) := fi22CentPerm fi22CentOuterLine

@[expose] def fi22CentSylowField (s i : ℕ) : ℕ := (fi22CentSylows.getD s []).getD i 0

@[expose] def fi22CentSylowSub (s : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {g | ∃ i < fi22CentSylowField s 4, fi22CentPerm (fi22CentSylowField s 3 + i) = g}

@[expose] def fi22CentWitField (w i : ℕ) : ℕ := (fi22CentWitnesses.getD w []).getD i 0

@[expose] def fi22CentWitRep (w : ℕ) : Equiv.Perm (Fin 3510) := fi22CentPerm (fi22CentWitField w 0)

@[expose] def fi22CentWitConj (w : ℕ) : Equiv.Perm (Fin 3510) := fi22CentPerm (fi22CentWitField w 1)

@[expose] def fi22SearchPool (j : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22CentPerm (fi22SearchPoolStart + j)

@[expose] def fi22SearchAcc (i : ℕ) : Equiv.Perm (Fin 3510) := fi22CentPerm (fi22SearchAccStart + i)

theorem CTUC_Fi22_centralizer_certificate_data :
    (∀ L < 306, Rep 3510 (fi22CentArr L) (fi22CentPerm L)) ∧
    fi22CentCases = [0, 1, 3, 4, 5] ∧
    (∀ c < 5, fi22H c = Subgroup.closure
      {g | ∃ j < fi22CentGenCount.getD c 0, fi22CentPerm (fi22CentStrongStart.getD c 0 + j) = g}) ∧
    (∀ c < 5, (fi22HChain c).base.toList.map Fin.val = [0, 1, 2, 3, 6, 4] ∧
      (fi22HChain c).originalCount = fi22CentGenCount.getD c 0 ∧
      (fi22HChain c).strongCount = fi22CentStrongCount.getD c 0) ∧
    fi22CentGenCount = [12, 9, 3, 9, 9] ∧ fi22CentStrongCount = [19, 16, 9, 19, 16] ∧
    fi22CentOrders = [1769472, 53084160, 3317760, 1045094400, 2903040] ∧
    fi22CentRefPoints.length = 4 ∧ fi22CentRefBounds.length = 4 ∧
    fi22CentSylows.length = 11 ∧ fi22CentWitnesses.length = 66 ∧
    fi22CentC = fi22CentPerm 79 ∧
    fi22SearchBase = [1122, 1226, 1920, 2321, 2506, 47, 0, 1, 6, 2] ∧
    fi22SearchNodeData.length = 138 ∧ fi22SearchPoolCount = 64 := by
  refine ⟨fun L hL => rep_fi22CentPerm hL, rfl, fun c hc => fi22H_eq_closure hc,
    fun c hc => ⟨rfl, fi22CentK_eq hc, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  change (fi22CentStrong c).size = _
  rw [fi22CentStrong, Array.size_ofFn]

end CFSG.Sporadic.FischerOddCore
