module

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase1

public import CFSG.Sporadic.Schreier.J4SNoCompCheck
public import CFSG.Sporadic.Schreier.J4SKernelBase1
public import CFSG.Sporadic.Schreier.J4SOddLocalBase1
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFormData
public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native MulAction
open scoped Matrix

theorem fixCard_rep
    {l : ℕ} (hl : l < 7) :
    fixCard (toRow (toVecD 112 repVecs[l]!)) = repCounts[l]! := by
  have h := fix_check l hl
  rw [fixCard_eq_card _ (fun a => etaV unMats repVecs[l]! a = repVecs[l]!) ?_]
  · exact h.1
  intro a ha
  rw [η_smul_toRow, ← ofRow_inj]
  constructor
  · intro e
    exact toVecD_injOn e (h.2 a ha)
  · intro e
    rw [e]

theorem bilV_rep_two :
    bilV (toRow (toVecD 112 repVecs[2]!)) = 1 := by
  rw [bilV_toRow, ite_eq_left bil_check.1]

theorem bilV_rep_three :
    bilV (toRow (toVecD 112 repVecs[3]!)) = 0 := by
  rw [bilV_toRow, bil_check.2]
  rfl

theorem outside_parts
    {l a : ℕ} (hl1 : 1 ≤ l) (hl : l < 7) (ha1 : 1 ≤ a) (ha : a < 2048) :
    a ∈ dSets[l]! ∨ ∃ j : Fin 11, ncommE unMats a (conjTab[l]!)[j.val]! = true := by
  have h := outside_check
  unfold outsideOK at h
  have h1 := List.all_eq_true.1 h l (List.mem_range'_1.2 ⟨hl1, by omega⟩)
  have h2 := List.all_eq_true.1 h1 a (List.mem_range'_1.2 ⟨ha1, by omega⟩)
  rcases Bool.or_eq_true_iff.1 h2 with h3 | h3
  · exact Or.inl (List.contains_iff_mem.1 h3)
  · obtain ⟨j, hj, h4⟩ := List.any_eq_true.1 h3
    exact Or.inr ⟨⟨j, List.mem_range.1 hj⟩, h4⟩

theorem conj_rep_mem
    {l : ℕ} (hl : l < 7) {r s : J} (hr : r ∈ N) (hs : s ∈ N)
    (e : (mRep l)⁻¹ * r * mRep l = s) : ∃ a < 2048, s = η a ∧ (a = 0 ∨ l = 0 ∨ a ∈ dSets[l]!) := by
  obtain ⟨a, ha, rfl⟩ := exists_η_eq hs
  refine ⟨a, ha, rfl, ?_⟩
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  by_cases hl0 : l = 0
  · exact Or.inr (Or.inl hl0)
  refine Or.inr (Or.inr ?_)
  rcases outside_parts (by omega) hl (by omega) ha with h | ⟨j, hj⟩
  · exact h
  · exfalso
    have hW := (rep_conjPair l j).1
    have hM := (rep_conjPair l j).2.2.1
    rw [← conjTab_get hl j] at hW hM
    refine ncommE_sound hW hM hj ?_
    rw [← e]
    have hc : r * u j = u j * r := N_comm r hr (u j) (u_mem_N j)
    calc (mRep l)⁻¹ * r * mRep l * ((mRep l)⁻¹ * u j * mRep l)
        = (mRep l)⁻¹ * (r * u j) * mRep l := by group
      _ = (mRep l)⁻¹ * (u j * r) * mRep l := by rw [hc]
      _ = (mRep l)⁻¹ * u j * mRep l * ((mRep l)⁻¹ * r * mRep l) := by group
