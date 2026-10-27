module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem odd_index_of_centralInSylow (s : X)
    (h : CentralInSylow X (Subgroup.zpowers s)) :
    Odd (Subgroup.centralizer ({s} : Set X)).index := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({s} : Set X)
  obtain ⟨P, hSP, hcen⟩ := h
  have hPle : (P : Subgroup X) ≤ C := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = s := by simpa using hy
    rw [hy']
    exact hcen s (Subgroup.mem_zpowers s) p hp
  have hdvd : C.index ∣ P.index := Subgroup.index_dvd_of_le hPle
  have hoddP : Odd (P.index) := by
    refine Nat.not_even_iff_odd.mp ?_
    intro he
    exact (Sylow.not_dvd_index P) (by simpa [even_iff_two_dvd] using he)
  exact Odd.of_dvd_nat hoddP hdvd

end CFSG.LocalAnalysis.WeakClosure81
