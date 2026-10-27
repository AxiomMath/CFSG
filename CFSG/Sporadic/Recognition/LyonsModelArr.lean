module

public import CFSG.Sporadic.Recognition.LyonsModelInputs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Equiv

def setOfArr (a : Array UInt32) : Set (Fin deg) := {i | ∃ p ∈ a, p.toNat = i.val}

theorem setOfArr_applyToSet {T : Table} {g : Perm (Fin deg)} (hT : Rep deg T g)
    {F : Array UInt32} (hF : ∀ p ∈ F, p.toNat < deg) :
    setOfArr (applyToSet T F) = g '' setOfArr F := by
  ext i
  simp only [setOfArr, applyToSet, Set.mem_ofPred_eq, Set.mem_image, Array.mem_mergeSort,
    Array.mem_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hp⟩
    refine ⟨⟨q.toNat, hF q hq⟩, ⟨q, hq, rfl⟩, Fin.ext ?_⟩
    have h := hT q.toNat (hF q hq)
    rw [idx_of_lt _ (hF q hq), Equiv.Perm.smul_def] at h
    exact h.symm.trans hp
  · rintro ⟨j, ⟨q, hq, hqj⟩, rfl⟩
    refine ⟨_, ⟨q, hq, rfl⟩, ?_⟩
    have h := hT q.toNat (hF q hq)
    rw [idx_of_lt _ (hF q hq), Equiv.Perm.smul_def] at h
    have hj : j = ⟨q.toNat, hF q hq⟩ := Fin.ext hqj.symm
    rw [hj]
    exact h

theorem table_eq_ofNat_iff {T : Table} {g : Perm (Fin deg)} (hT : Rep deg T g) (i : Fin deg) :
    T[i.val]! = UInt32.ofNat i.val ↔ g i = i := by
  have h := hT i.val i.isLt
  rw [idx_of_lt _ i.isLt, Equiv.Perm.smul_def] at h
  have hlt : i.val < 2 ^ 32 := lt_of_lt_of_le i.isLt (by norm_num [deg])
  rw [← UInt32.toNat_inj, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  change ap T i.val = i.val ↔ _
  rw [h, Fin.ext_iff]

theorem setOfArr_fixPts {T : Table} {g : Perm (Fin deg)} (hT : Rep deg T g) :
    setOfArr (fixPts T) = {i | g i = i} := by
  ext i
  simp only [setOfArr, fixPts, Set.mem_ofPred_eq, Array.mem_filterMap, Array.mem_range]
  have hlt : ∀ k : ℕ, k < deg → (UInt32.ofNat k).toNat = k := fun k hk => by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (lt_of_lt_of_le hk (by norm_num [deg]))]
  constructor
  · rintro ⟨p, ⟨k, hk, hkp⟩, hpi⟩
    by_cases hTk : (T[k]! == UInt32.ofNat k) = true
    · rw [ite_eq_left hTk, Option.some.injEq] at hkp
      subst hkp
      rw [hlt k hk] at hpi
      subst hpi
      exact (table_eq_ofNat_iff hT i).1 (beq_iff_eq.1 hTk)
    · rw [ite_eq_right hTk] at hkp
      exact absurd hkp (by simp)
  · intro hgi
    refine ⟨UInt32.ofNat i.val, ⟨i.val, i.isLt, ?_⟩, hlt _ i.isLt⟩
    rw [ite_eq_left (beq_iff_eq.2 ((table_eq_ofNat_iff hT i).2 hgi))]

theorem isStrictSet_lt {a : Array UInt32} (h : isStrictSet a = true) :
    ∀ p ∈ a, p.toNat < deg := by
  intro p hp
  unfold isStrictSet at h
  rw [Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp
  simpa using h.1 i hi

theorem isStrictSet_pairwise {a : Array UInt32} (h : isStrictSet a = true) :
    a.toList.Pairwise (· < ·) := by
  refine List.IsChain.pairwise ?_
  rw [List.isChain_iff_getElem]
  intro i hi
  unfold isStrictSet at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hi' : i + 1 < a.size := by simpa using hi
  have h2 := h.2 i (List.mem_range.2 (by omega))
  rw [decide_eq_true_eq, getElem!_pos a i (by omega), getElem!_pos a (i + 1) hi'] at h2
  simpa using h2

theorem setOfArr_inj {a b : Array UInt32} (ha : isStrictSet a = true) (hb : isStrictSet b = true)
    (h : setOfArr a = setOfArr b) : a = b := by
  have hmem : ∀ p : UInt32, p ∈ a ↔ p ∈ b := by
    intro p
    have key : ∀ {c d : Array UInt32}, isStrictSet c = true → setOfArr c = setOfArr d →
        p ∈ c → p ∈ d := by
      intro c d hc hcd hp
      have hlt := isStrictSet_lt hc p hp
      have hpc : (⟨p.toNat, hlt⟩ : Fin deg) ∈ setOfArr c := ⟨p, hp, rfl⟩
      rw [hcd] at hpc
      obtain ⟨q, hq, hqp⟩ := hpc
      have : q = p := UInt32.toNat_inj.1 hqp
      exact this ▸ hq
    exact ⟨key ha h, key hb h.symm⟩
  rw [← Array.toList_inj]
  exact List.Pairwise.eq_of_mem_iff (isStrictSet_pairwise ha) (isStrictSet_pairwise hb)
    (fun p => by simpa using hmem p)

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
