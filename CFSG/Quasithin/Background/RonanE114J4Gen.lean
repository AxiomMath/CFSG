module

public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.EmptyFaithful.E22NJ4

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin CFSG.Quasithin.A1b
open CFSG.Quasithin.E2P

theorem Hj_sup_centralizer_z0 :
    Hj ⊔ Subgroup.centralizer ({eta uJ 11 1131} : Set J) = ⊤ := by
  obtain ⟨g, hg, hgH⟩ := centralizer_z0_not_le_Hj
  have hgC : g ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg
  refine (isCoatom_Hj j4Facts).2 _ (lt_of_le_of_ne le_sup_left fun h => hgH ?_)
  rw [h]
  exact Subgroup.mem_sup_right hgC

theorem nParam_J_le_two_of_two_locals
    (hH : E1.nParam Hj ≤ 2)
    (hC : E1.nParam (Subgroup.centralizer ({eta uJ 11 1131} : Set J)) ≤ 2) :
    E1.nParam (⊤ : Subgroup J) ≤ 2 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have hP0 : IsSylowIn 2 P0 ⊤ := by
    obtain ⟨h2, h3⟩ := J4Two.P0_sylow
    exact ⟨le_top, h2, by rwa [Subgroup.relIndex_top_right]⟩
  refine E1.nParam_le_of_generated (n := 2) hP0
    (Δ := {Hj, Subgroup.centralizer ({eta uJ 11 1131} : Set J)}) ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    exact Hj_sup_centralizer_z0
  · intro D hD
    rcases hD with rfl | rfl
    · exact P0_le_Hj
    · exact J4Two.P0_le_centralizer
  · intro D hD
    rcases hD with rfl | rfl
    · exact_mod_cast hH
    · exact_mod_cast hC

end CFSG.Quasithin.RonanE114
