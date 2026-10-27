module

public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem vt_mul_mem_left_eq {G : Type} [Group G] (M Q L B Z : Subgroup G)
    (hQL : Q ≤ L) (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) {q s : G} (hq : q ∈ Q) :
    Vt M L B Z (q * s) = Vt M L B Z s := by
  have key : ∀ m ∈ M, (q * s ∈ conjSubgroup m L ↔ s ∈ conjSubgroup m L) := by
    intro m hm
    have hmQ : m⁻¹ * q * m ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hm)) q).mp hq
      simpa using h
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have e : m⁻¹ * (q * s) * m = (m⁻¹ * q * m) * (m⁻¹ * s * m) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left L (hQL hmQ)
  unfold Vt
  congr 1
  apply le_antisymm
  · refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
    exact le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le ((key m hm).mp ht) le_rfl))
  · refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
    exact le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le ((key m hm).mpr ht) le_rfl))

theorem vt_conj_eq_of_comm_mem_Q {G : Type} [Group G] (M Q L B Z : Subgroup G)
    (hQL : Q ≤ L) (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) {y u : G} (hy : y ∈ M)
    (hZ : conjSubgroup y Z = Z) (hcomm : ⁅y, u⁆ ∈ Q) :
    conjSubgroup y (Vt M L B Z u) = Vt M L B Z u := by
  rw [conjSubgroup_Vt_eq hy hZ u]
  have e : y * u * y⁻¹ = ⁅y, u⁆ * u := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact vt_mul_mem_left_eq M Q L B Z hQL hMQ hcomm

theorem mem_normalizer_Vt_of_comm_mem {G : Type} [Group G] (M Q L B Z : Subgroup G)
    (hQL : Q ≤ L) (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) {y u : G} (hy : y ∈ M)
    (hZ : conjSubgroup y Z = Z) (hcomm : ⁅y, u⁆ ∈ Q) :
    y ∈ Subgroup.normalizer (Vt M L B Z u : Set G) := by
  rw [← conjSubgroup_eq_self_iff]
  exact vt_conj_eq_of_comm_mem_Q M Q L B Z hQL hMQ hy hZ hcomm

end CFSG.RankThree.GF2n.Stroth80
