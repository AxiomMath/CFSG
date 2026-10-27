module

public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowBase

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer

theorem fi22CentOrder_check
    {c : ℕ} (hc : c < 5) : fi22CentOrderOK c = true := by
  interval_cases c
  · exact fi22CentOrder_check0
  · exact fi22CentOrder_check1
  · exact fi22CentOrder_check2
  · exact fi22CentOrder_check3
  · exact fi22CentOrder_check4

theorem fi22CentOrder_facts {c : ℕ} (hc : c < 5) :
    rawChainOK 3510 ((fi22CentStrong c).extract 0 (fi22CentK c)) (fi22CentStrong c)
      #[0, 1, 2, 3, 6, 4] (fi22CentWords c) 4 = true ∧
    (rawOrbitSizes 3510 (fi22CentStrong c) #[0, 1, 2, 3, 6, 4]).prod = fi22CentOrders.getD c 0 ∧
    ∀ j < fi22CentGenCount.getD c 0, fi22InP (fi22CentStrong c)[j]! = true ∧
      eqA 3510 (compA 3510 (fi22CentStrong c)[j]! (fi22ExtArr (21 + fi22CentCase c)))
        (compA 3510 (fi22ExtArr (21 + fi22CentCase c)) (fi22CentStrong c)[j]!) = true := by
  have h := fi22CentOrder_check hc
  unfold fi22CentOrderOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun j hj => by simpa using allLt_spec h3 hj⟩

theorem fi22HChain_arrays {c : ℕ} (hc : c < 5) :
    ChainArrays (fi22HChain c) ((fi22CentStrong c).extract 0 (fi22CentK c))
      (fi22CentStrong c) #[0, 1, 2, 3, 6, 4] (fi22CentWords c) := by
  have h := chainArrays_ofArrays (n := 3510) (hn := by decide) (k := fi22CentK c)
    (hk := Nat.min_le_right _ _) (base := fi22FinList 3510 (by decide) [0, 1, 2, 3, 6, 4])
    (hb := by decide) (W := fi22CentWords c)
    (chainCheckFacts (fi22CentOrder_facts hc).1).strong_inv
  have hb : ((fi22FinList 3510 (by decide) [0, 1, 2, 3, 6, 4]).map Fin.val).toArray =
      #[0, 1, 2, 3, 6, 4] := rfl
  rw [hb] at h
  exact h

theorem fi22HChain_valid
    {c : ℕ} (hc : c < 5) : ValidSchreier (fi22HChain c) :=
  (validSchreier_of_chainOK (fi22HChain_arrays hc) (by norm_num) (fi22CentOrder_facts hc).1).1

theorem card_fi22H
    {c : ℕ} (hc : c < 5) : Nat.card (fi22H c) = fi22CentOrders.getD c 0 := by
  rw [fi22H, card_originalSubgroup_of_chainOK (fi22HChain_arrays hc) (by norm_num)
    (fi22CentOrder_facts hc).1]
  exact (fi22CentOrder_facts hc).2.1

theorem siftA_iff_mem_fi22H
    {c : ℕ} (hc : c < 5) {g : Array ℕ} {G : Equiv.Perm (Fin 3510)}
    (hG : Rep 3510 g G) :
    siftA 3510 (rawLevels 3510 (fi22CentStrong c) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4] 0 g =
      true ↔ G ∈ fi22H c :=
  siftA_iff_mem_originalSubgroup (fi22HChain_arrays hc) (by norm_num) (fi22CentOrder_facts hc).1 hG

theorem fi22H_le
    {c : ℕ} (hc : c < 5) :
    fi22H c ≤ fi22P ⊓ Subgroup.centralizer {fi22CentT c} := by
  have hk : fi22CentCase c < 6 := by interval_cases c <;> decide
  rw [fi22H_eq_closure hc, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hjs : j < fi22CentStrongCount.getD c 0 := by
    obtain ⟨-, -, -, -, hs, hg, -⟩ := fi22Cent_check
    rw [hs]; rw [hg] at hj
    interval_cases c <;> simp at hj ⊢ <;> omega
  have hrep :
      Rep 3510 (fi22CentStrong c)[j]! (fi22CentPerm (fi22CentStrongStart.getD c 0 + j)) := by
    rw [fi22CentStrong_get hc hjs]
    exact rep_fi22CentPerm (fi22CentStrong_line_lt hc hjs)
  obtain ⟨hP, hcomm⟩ := (fi22CentOrder_facts hc).2.2 j hj
  have hc' := eq_of_eqA (rep_compA hrep (rep_fi22ExtRep hk)) (rep_compA (rep_fi22ExtRep hk) hrep)
    hcomm
  have e : fi22CentT c = fi22ExtRep (fi22CentCase c) := rfl
  refine ⟨(fi22InP_iff hrep).1 hP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [e]
  exact hc'

theorem CTUC_Fi22_literal_centralizer_subgroup_orders :
    (∀ c < 5, fi22H c ≤ fi22P ⊓ Subgroup.centralizer {fi22CentT c}) ∧
    (∀ c < 5, ValidSchreier (fi22HChain c)) ∧
    ((List.range 5).map fun c => Nat.card (fi22H c)) =
      [1769472, 53084160, 3317760, 1045094400, 2903040] ∧
    (∀ c < 5, (fi22HChain c).base.toList.map Fin.val = [0, 1, 2, 3, 6, 4]) ∧
    (∀ c < 5, ∀ (g : Array ℕ) (G : Equiv.Perm (Fin 3510)), Rep 3510 g G →
      (siftA 3510 (rawLevels 3510 (fi22CentStrong c) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4] 0 g =
        true ↔ G ∈ fi22H c)) := by
  refine ⟨fun c hc => fi22H_le hc, fun c hc => fi22HChain_valid hc, ?_, fun c _ => rfl,
    fun c hc g G hG => siftA_iff_mem_fi22H hc hG⟩
  rw [show ((List.range 5).map fun c => Nat.card (fi22H c)) =
    (List.range 5).map fun c => fi22CentOrders.getD c 0 from
      List.map_congr_left fun c hc => card_fi22H (List.mem_range.1 hc)]
  rfl

end CFSG.Sporadic.FischerOddCore
