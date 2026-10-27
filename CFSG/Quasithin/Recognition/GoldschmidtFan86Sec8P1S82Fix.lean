module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fix_alpha_side (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) {m : Fin 5} {w : V}
    (hw : Γ.dist w α + 1 = Γ.dist w (D.beta m)) (hw3 : Γ.dist (D.beta m) w ≤ 3) :
    L.z (D.alpha i) • w = w := by
  rw [h.z_smul_eq_iff (D.valence_alpha F i)]
  have h1 := F.isTree.connected.dist_triangle (u := D.alpha i) (v := α) (w := w)
  have e1 : Γ.dist w (D.beta m) ≤ 3 := by rw [SimpleGraph.dist_comm]; exact hw3
  have e2 : Γ.dist α w = Γ.dist w α := SimpleGraph.dist_comm
  have e3 := D.dist_alpha_start F i
  omega

theorem fix_below_one (F : FanTree Γ G) (h : Fan71c F L) {i m : Fin 5} (hi : i ≠ m) {w : V}
    (hw : Γ.dist w (D.beta m) + 1 = Γ.dist w α) (hw1 : Γ.dist w (D.beta m) ≤ 1) :
    L.z (D.alpha i) • w = w := by
  rw [h.z_smul_eq_iff (D.valence_alpha F i), SimpleGraph.dist_comm, D.dist_alpha_below F h hi hw]
  omega

theorem fix_depth_two (F : FanTree Γ G) (h : Fan71c F L) {i j m : Fin 5} (hmi : i ≠ m)
    (hmj : j ≠ m) {w : V} (hw : Γ.dist w (D.beta m) = 2) (hwα : Γ.dist w α = 3) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • w = w := by
  obtain ⟨P, hP0, hP2⟩ := IsTree.exists_arc F.isTree 2 (D.beta m) w
    (by rw [SimpleGraph.dist_comm]; exact hw)
  have hcb : Γ.Adj (P.vert 1) (D.beta m) := by
    have := P.adj 0 (by norm_num)
    rw [hP0] at this
    exact this.symm
  have hcw : Γ.Adj (P.vert 1) w := by
    have := P.adj 1 (by norm_num)
    rw [hP2] at this
    exact this
  have hcα : P.vert 1 ≠ α := fun e => by
    have := dist_eq_one_iff_adj.2 hcw.symm
    rw [e, hwα] at this
    omega
  have hcβ : Γ.dist (P.vert 1) (D.beta m) = 1 := dist_eq_one_iff_adj.2 hcb
  have hcα2 : Γ.dist (P.vert 1) α = Γ.dist (P.vert 1) (D.beta m) + 1 := by
    have := IsTree.dist_succ_of_ne F.isTree hcb.symm (D.adj_start_beta m).symm hcα
      (by rw [SimpleGraph.dist_self, hcβ])
    rw [this]
  have hbelow_c : Γ.dist (P.vert 1) (D.beta m) + 1 = Γ.dist (P.vert 1) α := hcα2.symm
  have hbelow_w : Γ.dist w (D.beta m) + 1 = Γ.dist w α := by rw [hw, hwα]
  have key : ∀ s : Fin 5, s ≠ m → Γ.dist (D.alpha s) (P.vert 1) ≤ 4 ∧
      Γ.dist (D.alpha s) (D.beta m) ≤ 4 ∧ 4 < Γ.dist (D.alpha s) w := fun s hs => by
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.dist_comm, D.dist_alpha_below F h hs hbelow_c, hcα2, hcβ]
    · rw [SimpleGraph.dist_comm, D.dist_beta_alpha_ne F h hs]
      norm_num
    · rw [SimpleGraph.dist_comm, D.dist_alpha_below F h hs hbelow_w, hwα]
      norm_num
  obtain ⟨a1, a2, a3⟩ := key i hmi
  obtain ⟨b1, b2, b3⟩ := key j hmj
  have := mul_z_mem_nbrStab F h (D.valence_alpha F i) (D.valence_alpha F j) hcb hcw a1 a2 a3
    b1 b2 b3
  exact mem_nbrStab.1 this w hcw

end D10Set

end CFSG.Quasithin.Fan86
