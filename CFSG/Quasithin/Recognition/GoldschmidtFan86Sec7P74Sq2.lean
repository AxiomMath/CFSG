module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Sq
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74N1

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem sq_mem_nbrStab (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h73b : Fan73b F L) {α₀ w : V} (hα₀ : valence Γ α₀ = 5)
    (hd : Γ.dist α₀ w = 2) {b : G} (hb : b ∈ ballStab Γ G 2 α₀) : b * b ∈ nbrStab Γ G w := by
  obtain ⟨P, hP4, hP6⟩ := exists_arc8_between F hd (i := 4) (by norm_num)
  have hP6' : P.vert 6 = w := hP6
  have h5 : valence Γ (P.vert 4) = 5 := by rw [hP4]; exact hα₀
  have hadj : Γ.Adj w (P.vert 5) := by
    have := (P.adj 5 (by norm_num)).symm
    rwa [hP6'] at this
  have hadj7 : Γ.Adj w (P.vert 7) := by
    have := P.adj 6 (by norm_num)
    rwa [hP6'] at this
  have h73 := (h73b P h5).1
  rw [hP4] at h73
  rw [h73] at hb
  have hCst := calpha_eq_stab h71a h71c h5
  refine sq_mem_nbrStab_of_sup F hadj (V' := L.zGroup 2 α₀) (C' := L.calpha P) ?_ ?_ ?_ hb
  · intro v hv
    have hv2 := zGroup_le_ballStab_two h71c hv
    refine ⟨MulAction.mem_stabilizer_iff.2 (mem_ballStab.1 hv2 w (by omega)), ?_⟩
    refine MulAction.mem_stabilizer_iff.2 (mem_ballStab.1 hv2 _ ?_)
    have := Arc.dist_vert F.isTree P (i := 4) (j := 5) (by norm_num) (by norm_num)
    rw [hP4] at this
    omega
  · intro v hv
    exact zGroup_sq h40 h64 hα₀ hv
  · intro c hc
    rw [hCst, Arc.mem_stab] at hc
    refine ⟨?_, MulAction.mem_stabilizer_iff.2 (hc 5 (by norm_num))⟩
    have hcw : c • w = w := by
      have := hc 6 (by norm_num)
      rwa [hP6'] at this
    exact mem_nbrStab_of_fix_two F (MulAction.mem_stabilizer_iff.2 hcw) hadj hadj7
      (P.nb 5 (by norm_num))
      (hc 5 (by norm_num)) (hc 7 (by norm_num))

theorem sq_mem_ballStab_five (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {α : V}
    (hα : valence Γ α = 5) {n : G} (hn : n ∈ ballStab Γ G 3 α) :
    n * n ∈ ballStab Γ G 5 α := by
  have hn4 := ballStab_three_le_four h40 h64 h71a h71c h72b h73b hα hn
  refine mem_ballStab.2 fun u hu => ?_
  by_cases hu4 : Γ.dist α u ≤ 4
  · have := mem_ballStab.1 hn4 u hu4
    rw [mul_smul, this, this]
  · have hd : Γ.dist α u = 5 := by omega
    obtain ⟨P, hP0, hP5⟩ := exists_arc8_between F hd (i := 0) (by norm_num)
    have hP5' : P.vert 5 = u := hP5
    have h0 : valence Γ (P.vert 0) = 5 := by rw [hP0]; exact hα
    have h4 : valence Γ (P.vert 4) = 5 := P71.valence_four_of_zero F P h0
    have h2 : valence Γ (P.vert 2) = 5 := valence_vert F P h4 (by norm_num) (by norm_num)
    have d02 := Arc.dist_vert F.isTree P (i := 0) (j := 2) (by norm_num) (by norm_num)
    have d24 := Arc.dist_vert F.isTree P (i := 2) (j := 4) (by norm_num) (by norm_num)
    have d04 := Arc.dist_vert F.isTree P (i := 0) (j := 4) (by norm_num) (by norm_num)
    rw [hP0] at d02 d04
    have hb : n ∈ ballStab Γ G 2 (P.vert 2) := mem_ballStab.2 fun t ht => by
      have := F.isTree.connected.dist_triangle (u := α) (v := P.vert 2) (w := t)
      exact mem_ballStab.1 hn4 t (by omega)
    have hsq := sq_mem_nbrStab h40 h64 h71a h71c h73b h2 (w := P.vert 4) (by omega) hb
    have hadj : Γ.Adj (P.vert 4) u := by
      have := P.adj 4 (by norm_num)
      rwa [hP5'] at this
    exact mem_nbrStab.1 hsq u hadj

end P74

end CFSG.Quasithin.Fan86
