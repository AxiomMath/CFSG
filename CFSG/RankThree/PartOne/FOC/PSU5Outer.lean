module

public import CFSG.RankThree.PartOne.FOC.CompGroup
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFive
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (psu5 fixSub innerAut LocalRankAut)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem outerComp_psu_five (h5 : 5 ∣ 2 ^ f + 1) [Finite (psu5 h)] : OuterComp 5 (psu5 h) := by
  intro _ β hβ5 hβout hra y hβy hy5 E hE
  exfalso
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (innerAut (psu5 h)).one_mem)
  have hord : orderOf β = 5 := orderOf_eq_prime hβ5 hβ1
  by_cases hD : β ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  · rcases Sec66T.psu5_aut_classification h β hβ5 with ⟨P, c, hc, hP5, hβP⟩ | ⟨φ, M, -, -, -, hnD, -⟩
    · obtain ⟨U, hU1, hU2, hUE⟩ := exists_two_subgroup_of_isComponentOf hE
      subst hβP
      refine Sec66T.psu5_D_case h h5 hc hP5 hβout hU1 hU2 (fun u hu => ?_) hra
      have : (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P) u = u :=
        hE.1 (hUE hu)
      rw [this]
      exact hu
    · exact hnD hD
  · exact Sec66T.psu5_F_case h h5 hord hD hra

end CFSG.RankThree.PartOne.FOC
