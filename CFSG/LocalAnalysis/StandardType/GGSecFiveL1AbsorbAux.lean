module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanProjection

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin
open scoped commutatorElement

theorem ggL1Ab_inf_isSubnormal {G : Type} [Group G] {X Z M : Subgroup G}
    (hXS : IsSubnormal X Z) (hMZ : M ≤ Z) : IsSubnormal (X ⊓ M) M := by
  have h := ggIsSubnormal_inf hXS M
  rwa [inf_eq_right.mpr hMZ] at h

theorem ggL1Ab_perfect_le_ggOTwoPrime_of_le {G : Type} [Group G] [Finite G]
    {P T : Subgroup G} (hPT : P ≤ T) (hP : ⁅P, P⁆ = P) : P ≤ ggOTwoPrime T :=
  (le_perfectCore_of_perfect hPT hP).trans (SecFiveRk1C.perfectCore_le_ggOTwoPrime T)

theorem ggL1Ab_commutator_ne_bot_of_not_commute {G : Type} [Group G] {P T : Subgroup G}
    {n u : G} (hu : u ∈ P) (hn : n ∈ T) (hnu : n * u ≠ u * n) :
    ⁅P, T⁆ ≠ ⊥ := by
  intro hbot
  have hmem : ⁅u, n⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.commutator_mem_commutator hu hn
  rw [Subgroup.mem_bot] at hmem
  exact hnu (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm

end CFSG.StandardType

end
