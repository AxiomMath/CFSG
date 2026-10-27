module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Ball

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zpow_eq_one_or_self_of_mul_self {g : G} (hg : g * g = 1) (n : ℤ) :
    g ^ n = 1 ∨ g ^ n = g := by
  rcases Int.even_or_odd' n with ⟨q, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hg, one_zpow, one_mul, zpow_one]

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem mul_z_alpha_not_mem_zpowers (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5}
    (hij : i ≠ j) : L.z (D.alpha i) * L.z (D.alpha j) ∉ Subgroup.zpowers (L.z α) := by
  rintro ⟨n, hn0⟩
  have hn : L.z α ^ n = L.z (D.alpha i) * L.z (D.alpha j) := hn0
  have hd := D.dist_alpha_alpha F h hij
  have hvi := D.valence_alpha F i
  have hvj := D.valence_alpha F j
  rcases zpow_eq_one_or_self_of_mul_self (L.z_mul_self D.val) n with h1 | h1
  · rw [h1] at hn
    have : L.z (D.alpha i) = L.z (D.alpha j) := by
      have h2 : L.z (D.alpha i) = (L.z (D.alpha j))⁻¹ := eq_inv_of_mul_eq_one_left hn.symm
      rw [h2, L.z_inv hvj]
    have := h.z_injective hvi hvj this
    rw [this, SimpleGraph.dist_self] at hd
    omega
  · rw [h1] at hn
    have h3 : L.z (D.alpha i) * L.z (D.alpha j) * L.z α ≠ 1 := by
      refine h.2.2 _ _ _ hvi hvj D.val ?_ ?_ ?_ ?_
      · intro e
        rw [e, SimpleGraph.dist_self] at hd
        omega
      · exact fun e => D.alpha_ne_start i e
      · exact fun e => D.alpha_ne_start j e
      · rintro ⟨β, hβ⟩
        have hi : D.alpha i ∈ Γ.neighborSet β := by rw [← hβ]; simp
        have hj : D.alpha j ∈ Γ.neighborSet β := by rw [← hβ]; simp
        have h1 := dist_eq_one_iff_adj.2 hi
        have h2 := dist_eq_one_iff_adj.2 hj
        have := F.isTree.connected.dist_triangle (u := D.alpha i) (v := β) (w := D.alpha j)
        rw [SimpleGraph.dist_comm (u := β) (v := D.alpha i)] at h1
        omega
    apply h3
    rw [← hn]
    exact L.z_mul_self D.val

theorem moves_delta (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L) {i j m k : Fin 5}
    (hij : i ≠ j) (hmi : i ≠ m) (hmj : j ≠ m) (hmid : 2 * m - i = j) (hkm : m ≠ k) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • D.delta k ≠ D.delta k := by
  intro hfix
  have h : Fan71c F L := h7.2.2.1
  have hρm : (L.z (D.alpha i) * L.z (D.alpha j)) • D.delta m = D.delta m :=
    D.fix_ball F h h512 hmi hmj hmid (by rw [D.dist_beta_delta F m])
  obtain ⟨P, h0, h4, h8, -, -⟩ := D.exists_arc8 F h hkm
  have hst : L.z (D.alpha i) * L.z (D.alpha j) ∈ P.stab G := by
    refine (Arc.mem_stab G).2 ?_
    exact Arc.fixes_of_ends F.isTree F.adj_smul P (by rw [h0]; exact hρm) (by rw [h8]; exact hfix)
  have hne : P.vert 0 ≠ P.vert 8 := by
    rw [h0, h8]
    exact fun e => hkm (D.delta_injective e)
  have hcal := ZLab.calpha_eq_stab h7.1 h P (by rw [h0]; exact D.valence_delta F m) hne
  have hzG : L.z (D.alpha i) * L.z (D.alpha j) ∈ L.zGroup 2 (P.vert 4) := by
    rw [h4]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure
        (L.z_mem_zSet (by rw [D.dist_start_alpha F i]) (D.valence_alpha F i)))
      (Subgroup.subset_closure
        (L.z_mem_zSet (by rw [D.dist_start_alpha F j]) (D.valence_alpha F j)))
  have h73 := (h7.2.2.2.2.2.2.1 P (by rw [h4]; exact D.val)).2
  have hmem : L.z (D.alpha i) * L.z (D.alpha j) ∈ L.zGroup 2 (P.vert 4) ⊓ L.calpha P :=
    Subgroup.mem_inf.2 ⟨hzG, hcal ▸ hst⟩
  rw [h73, h4] at hmem
  exact D.mul_z_alpha_not_mem_zpowers F h hij hmem

end D10Set

end CFSG.Quasithin.Fan86
