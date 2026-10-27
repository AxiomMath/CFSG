module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74N

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem ballStab_four_nbr_eq_bot (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F)
    (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5)
    {β : V} (hβ : Γ.Adj (P.vert 4) β) : ballStab Γ G 4 β = ⊥ := by
  have hv3 : valence Γ β = 3 := P71.valence_five_three F hβ h5
  obtain ⟨a2, ha2, hne⟩ := F.exists_adj_ne β (P.vert 4)
  have hv5 : valence Γ a2 = 5 := P71.valence_three_five F ha2 hv3
  obtain ⟨P2, hP2, -⟩ := exists_arc8_between F (SimpleGraph.dist_self : Γ.dist a2 a2 = 0)
    (i := 4) (by norm_num)
  have h5' : valence Γ (P2.vert 4) = 5 := by rw [hP2]; exact hv5
  have e1 := ballStab_three_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5
  have e2 := ballStab_three_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5'
  rw [hP2] at e2
  have hdα : Γ.dist β (P.vert 4) = 1 := dist_eq_one_iff_adj.mpr hβ.symm
  have hda : Γ.dist β a2 = 1 := dist_eq_one_iff_adj.mpr ha2
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hg1 : g ∈ Subgroup.zpowers (L.z (P.vert 4)) := by
    rw [← e1]
    refine mem_ballStab.2 fun w hw => mem_ballStab.1 hg w ?_
    have := F.isTree.connected.dist_triangle (u := β) (v := P.vert 4) (w := w)
    omega
  have hg2 : g ∈ Subgroup.zpowers (L.z a2) := by
    rw [← e2]
    refine mem_ballStab.2 fun w hw => mem_ballStab.1 hg w ?_
    have := F.isTree.connected.dist_triangle (u := β) (v := a2) (w := w)
    omega
  rcases eq_one_or_self_of_mem_zpowers (L.z_mul_self h5) hg1 with h | h
  · exact h
  · exfalso
    rw [h] at hg2
    rcases eq_one_or_self_of_mem_zpowers (L.z_mul_self hv5) hg2 with h' | h'
    · exact L.z_ne_one h5 h'
    · exact hne (h71c.z_injective h5 hv5 h').symm

end P74

end CFSG.Quasithin.Fan86
