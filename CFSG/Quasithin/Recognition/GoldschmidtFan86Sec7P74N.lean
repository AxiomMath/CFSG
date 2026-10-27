module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Con

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem ballStab_three_eq (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F)
    (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    ballStab Γ G 3 (P.vert 4) = Subgroup.zpowers (L.z (P.vert 4)) := by
  have hz : L.z (P.vert 4) ∈ ballStab Γ G 3 (P.vert 4) := z_mem_ballStab h71c h5 (by norm_num)
  refine le_antisymm (fun n hn => ?_) ((Subgroup.zpowers_le).2 hz)
  by_contra hnz
  have hn1 : n ≠ 1 := fun h => hnz (by rw [h]; exact one_mem _)
  have hnz' : n ≠ L.z (P.vert 4) := fun h => hnz (by rw [h]; exact Subgroup.mem_zpowers _)
  have hn4 := ballStab_three_le_four h40 h64 h71a h71c h72b h73b h5 hn
  have hz4 := ballStab_three_le_four h40 h64 h71a h71c h72b h73b h5 hz
  have hsq : n * n = 1 := by
    have := sq_mem_ballStab_five h40 h64 h71a h71c h72b h73b h5 hn
    rw [ballStab_five_eq_bot F h40 hΞ h62 h65 h5] at this
    exact this
  have hzsq := L.z_mul_self h5
  have hadj : Γ.Adj (P.vert 8) (P.vert 7) := (P.adj 7 (by norm_num)).symm
  have hd8 : Γ.dist (P.vert 4) (P.vert 8) = 4 := by
    have := Arc.dist_vert F.isTree P (i := 4) (j := 8) (by norm_num) (by norm_num)
    omega
  have hd7 : Γ.dist (P.vert 4) (P.vert 7) = 3 := by
    have := Arc.dist_vert F.isTree P (i := 4) (j := 7) (by norm_num) (by norm_num)
    omega
  have hmem : ∀ g ∈ ballStab Γ G 4 (P.vert 4), g ∈ MulAction.stabilizer G (P.vert 8) ⊓
      MulAction.stabilizer G (P.vert 7) := fun g hg =>
    Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 (mem_ballStab.1 hg _ hd8.le),
      MulAction.mem_stabilizer_iff.2 (mem_ballStab.1 hg _ (by omega))⟩
  have hnK : n ∉ nbrStab Γ G (P.vert 8) := fun h =>
    hn1 (eq_one_of_mem_nbrStab h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5 hn h)
  have hzK : L.z (P.vert 4) ∉ nbrStab Γ G (P.vert 8) := fun h =>
    L.z_ne_one h5 (eq_one_of_mem_nbrStab h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5 hz h)
  have hprod := F.mul_mem_nbrStab_of_sq_eq_one hadj (hmem n hn4) (hmem _ hz4) hsq hzsq hnK hzK
  have h1 := eq_one_of_mem_nbrStab h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5 (mul_mem hn hz)
    hprod
  exact hnz' (by
    have : n = (L.z (P.vert 4))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this, L.z_inv h5])

theorem ballStab_four_eq (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F)
    (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    ballStab Γ G 4 (P.vert 4) = Subgroup.zpowers (L.z (P.vert 4)) := by
  refine le_antisymm ?_ ?_
  · rw [← ballStab_three_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5]
    exact fixSet_anti (fun w hw => by
      show Γ.dist (P.vert 4) w ≤ 4
      have : Γ.dist (P.vert 4) w ≤ 3 := hw
      omega)
  · exact (Subgroup.zpowers_le).2 (z_mem_ballStab h71c h5 le_rfl)

end P74

end CFSG.Quasithin.Fan86
