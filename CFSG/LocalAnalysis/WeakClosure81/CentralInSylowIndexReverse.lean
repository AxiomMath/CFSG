module

public import CFSG.LocalAnalysis.WeakClosure81.CentralInSylowIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem centralInSylow_zpowers_of_odd_index (s : X) (hs : s * s = 1)
    (hodd : Odd (Subgroup.centralizer ({s} : Set X)).index) :
    CentralInSylow X (Subgroup.zpowers s) := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({s} : Set X)
  have hC2 : ¬ 2 ∣ C.index := by
    simpa [C] using hodd.not_two_dvd_nat
  have hsC : s ∈ C := by
    change s ∈ Subgroup.centralizer ({s} : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
  let sC : C := ⟨s, hsC⟩
  have hsC_sq : sC ^ 2 = 1 := by
    apply Subtype.ext
    simpa [sC, pow_two] using hs
  have hcyc : IsPGroup 2 (Subgroup.zpowers sC) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hsC_sq
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hcyc
  let K : Subgroup C := (Q : Subgroup C)
  let P : Subgroup X := K.map C.subtype
  have hP2 : IsPGroup 2 P := by
    simpa [P, K] using Q.2.map C.subtype
  have hPindex : P.index = K.index * C.index := by
    simpa [P] using Subgroup.index_map_subtype K
  have hK2 : ¬ 2 ∣ K.index := by
    simpa [K] using Sylow.not_dvd_index Q
  have hPnot : ¬ 2 ∣ P.index := by
    rw [hPindex]
    exact Nat.Prime.not_dvd_mul Nat.prime_two hK2 hC2
  have hPleC : P ≤ C := by
    simpa [P] using Subgroup.map_subtype_le K
  have hsP : s ∈ P := by
    refine Subgroup.mem_map.mpr ⟨sC, ?_, rfl⟩
    simpa [K] using hQle (Subgroup.mem_zpowers sC)
  refine ⟨hP2.toSylow hPnot, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr hsP
  · intro x hx p hp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hpc : p ∈ C := hPleC hp
    have hsp : Commute s p := (Subgroup.mem_centralizer_iff.mp hpc) s (by simp)
    rw [← hk]
    exact (hsp.zpow_left k).eq

theorem centralInSylow_zpowers_iff_odd_index (s : X) (hs : s * s = 1) :
    CentralInSylow X (Subgroup.zpowers s) ↔
      Odd (Subgroup.centralizer ({s} : Set X)).index :=
  ⟨odd_index_of_centralInSylow s, centralInSylow_zpowers_of_odd_index s hs⟩

end CFSG.LocalAnalysis.WeakClosure81
