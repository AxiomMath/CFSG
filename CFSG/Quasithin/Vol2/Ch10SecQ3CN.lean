module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.H13.LocDblCComp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem commutator_eq_bot_of_le_centralizer {H K : Subgroup G} (hKT : H = K ⊔ T)
    (hKW : K ≤ Subgroup.centralizer (VZ T H : Set G)) :
    ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
  have hZW : quasithinOmegaOneCenter T ≤ VZ T H := le_conjClosure _ _
  have hKZ : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun k hk => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subgroup.mem_centralizer_iff.mp (hKW hk) z (hZW hz)
  have hH : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hKT]
    exact sup_le hKZ (L246C127.le_centralizer_omegaOneCenter T)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hH

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
