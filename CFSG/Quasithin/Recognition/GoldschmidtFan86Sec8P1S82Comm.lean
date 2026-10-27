module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_smul_beta (F : FanTree Γ G) (h : Fan71c F L) {i m : Fin 5} (hmi : i ≠ m) {w : V}
    (hw : Γ.dist w (D.beta m) = 3) (hwα : Γ.dist w α = 4) :
    ∀ k, L.z w • D.beta k = D.beta (2 * m - k) := by
  have hvw : valence Γ w = 5 := valence_of_dist_even F D.val (by
    rw [SimpleGraph.dist_comm, hwα])
  have hbelow : Γ.dist w (D.beta m) + 1 = Γ.dist w α := by rw [hw, hwα]
  have hgα : L.z w ∈ MulAction.stabilizer G α := (h.z_mem_stabilizer_iff hvw α).2 (by rw [hwα])
  have hgβ : L.z w • D.beta m = D.beta m := (h.z_smul_eq_iff hvw _).2 (by rw [hw]; norm_num)
  have hgK : L.z w ∉ nbrStab Γ G α := fun hK => by
    have h5 := (h.z_smul_eq_iff hvw _).1 (mem_nbrStab.1 hK (D.beta i) (D.adj_start_beta i))
    rw [D.dist_beta_below F h hmi hbelow, hwα] at h5
    omega
  exact F.smul_eq_two_mul_sub D.val (inv_mem (D.x_mem_stabilizer F h)) D.adj_start_beta
    (D.beta_injective F h) (D.hxβ F h) hgα hgβ (L.z_mul_self hvw) hgK

theorem fix_depth_three (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) {i j m : Fin 5}
    (hmi : i ≠ m) (hmid : 2 * m - i = j) {w : V} (hw : Γ.dist w (D.beta m) = 3)
    (hwα : Γ.dist w α = 4) : (L.z (D.alpha i) * L.z (D.alpha j)) • w = w := by
  have hvw : valence Γ w = 5 := valence_of_dist_even F D.val (by
    rw [SimpleGraph.dist_comm, hwα])
  have hgα : L.z w ∈ MulAction.stabilizer G α := (h.z_mem_stabilizer_iff hvw α).2 (by rw [hwα])
  have hgβi : L.z w • D.beta i = D.beta j := by rw [D.z_smul_beta F h hmi hw hwα, hmid]
  have hadju : Γ.Adj (D.beta j) (L.z w • D.alpha i) := by
    have := (F.adj_smul (L.z w) (D.beta i) (D.alpha i)).2 (D.adj_beta_alpha i)
    rwa [hgβi] at this
  have hug : L.z w • D.alpha i ≠ α := fun e => D.alpha_ne_start i (by
    apply MulAction.injective (L.z w)
    show L.z w • D.alpha i = L.z w • α
    rw [e, MulAction.mem_stabilizer_iff.1 hgα])
  obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F j)
    (D.adj_start_beta j).symm (D.adj_beta_alpha j) (D.alpha_ne_start j).symm
  have hmemu : L.z w • D.alpha i ∈ Γ.neighborSet (D.beta j) := hadju
  rw [hts] at hmemu
  have hzu : L.z (L.z w • D.alpha i) = L.z (D.alpha j) ∨
      L.z (L.z w • D.alpha i) = L.z (D.alpha j) * L.z α := by
    rcases hmemu with h1 | h1 | h1
    · exact absurd h1 hug
    · left
      rw [h1]
    · right
      rw [h1]
      have h3 := h512.2.2.1 (D.beta j) α (D.alpha j) t (D.valence_beta F j) hts
        (D.alpha_ne_start j).symm hat hjt
      rw [eq_inv_of_mul_eq_one_right h3, mul_inv_rev, L.z_inv (D.valence_alpha F j),
        L.z_inv D.val]
  have hvδ : valence Γ (L.z (D.alpha i) • w) = 5 := by rw [valence_smul F]; exact hvw
  have hid : L.z (D.alpha i) * L.z (L.z w • D.alpha i) =
      L.z (L.z (D.alpha i) • w) * L.z w := by
    rw [L.equivariant (L.z w) (D.alpha i) (D.valence_alpha F i),
      L.equivariant (L.z (D.alpha i)) w hvw, L.z_inv hvw, L.z_inv (D.valence_alpha F i)]
    group
  obtain ⟨P, hP0, hP3⟩ := IsTree.exists_arc F.isTree 3 (D.beta m) w
    (by rw [SimpleGraph.dist_comm]; exact hw)
  have hcb : Γ.Adj (P.vert 1) (D.beta m) := by
    have := P.adj 0 (by norm_num)
    rw [hP0] at this
    exact this.symm
  have hcw : Γ.dist (P.vert 1) w = 2 := by
    have := Arc.dist_vert F.isTree P (i := 1) (j := 3) (by norm_num) le_rfl
    rw [hP3] at this
    simpa using this
  have hcα : P.vert 1 ≠ α := fun e => by
    have : Γ.dist w α = 2 := by rw [← e, SimpleGraph.dist_comm, hcw]
    omega
  have hcβ : Γ.dist (P.vert 1) (D.beta m) = 1 := dist_eq_one_iff_adj.2 hcb
  have hcα2 : Γ.dist (P.vert 1) α = Γ.dist (P.vert 1) (D.beta m) + 1 := by
    have := IsTree.dist_succ_of_ne F.isTree hcb.symm (D.adj_start_beta m).symm hcα
      (by rw [SimpleGraph.dist_self, hcβ])
    rw [this]
  have hfc : L.z (D.alpha i) • P.vert 1 = P.vert 1 := (h.z_smul_eq_iff (D.valence_alpha F i) _).2
    (by rw [SimpleGraph.dist_comm, D.dist_alpha_below F h hmi hcα2.symm, hcα2, hcβ])
  have hdc : Γ.dist (L.z (D.alpha i) • w) (P.vert 1) = 2 := by
    have := dist_smul F (L.z (D.alpha i)) w (P.vert 1)
    rw [hfc] at this
    rw [this, SimpleGraph.dist_comm, hcw]
  have hδw : L.z (L.z (D.alpha i) • w) • w = w := by
    rw [h.z_smul_eq_iff hvδ]
    have := F.isTree.connected.dist_triangle (u := L.z (D.alpha i) • w) (v := P.vert 1) (w := w)
    omega
  have hA : (L.z (D.alpha i) * L.z (L.z w • D.alpha i)) • w = w := by
    rw [hid, mul_smul, L.z_smul_self hvw, hδw]
  have hzαw : L.z α • w = w := (h.z_smul_eq_iff D.val w).2 (by rw [SimpleGraph.dist_comm, hwα])
  rcases hzu with hzu | hzu
  · rw [hzu] at hA
    exact hA
  · rw [hzu, ← mul_assoc, mul_smul, hzαw] at hA
    exact hA

end D10Set

end CFSG.Quasithin.Fan86
