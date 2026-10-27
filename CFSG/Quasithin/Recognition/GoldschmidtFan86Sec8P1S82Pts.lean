module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Far

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem dist_alpha_same_le (F : FanTree Γ G) (s : Fin 5) {n : ℕ} (hn : n ≤ 4) :
    Γ.dist (D.alpha s) ((D.P s).vert n) ≤ 2 := by
  show Γ.dist ((D.P s).vert 2) ((D.P s).vert n) ≤ 2
  rcases le_total n 2 with h | h
  · have h2 := D.dist_arc F s h (by norm_num : 2 ≤ 4)
    rw [SimpleGraph.dist_comm]
    omega
  · have h2 := D.dist_arc F s h hn
    omega

theorem fixed_iff_left (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) {n : ℕ}
    (hn : n ≤ 4) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • (D.P i).vert n = (D.P i).vert n ↔ n ≤ 2 := by
  have hzi : L.z (D.alpha i) • (D.P i).vert n = (D.P i).vert n :=
    (h.z_smul_eq_iff (D.valence_alpha F i) _).2 (by have := D.dist_alpha_same_le F i hn; omega)
  have hdj : Γ.dist (D.alpha j) ((D.P i).vert n) = 2 + n :=
    D.dist_vert_ne F h hij.symm (m := 2) (m' := n) (by norm_num) hn
  constructor
  · intro hfix
    by_contra hlt
    exact h.mul_z_smul_ne (D.valence_alpha F j) hzi (by rw [hdj]; omega) hfix
  · intro hle
    rw [mul_smul, (h.z_smul_eq_iff (D.valence_alpha F j) _).2 (by rw [hdj]; omega), hzi]

theorem fixed_iff_right (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) {n : ℕ}
    (hn : n ≤ 4) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • (D.P j).vert n = (D.P j).vert n ↔ n ≤ 2 := by
  have hzj : L.z (D.alpha j) • (D.P j).vert n = (D.P j).vert n :=
    (h.z_smul_eq_iff (D.valence_alpha F j) _).2 (by have := D.dist_alpha_same_le F j hn; omega)
  have hdi : Γ.dist (D.alpha i) ((D.P j).vert n) = 2 + n :=
    D.dist_vert_ne F h hij (m := 2) (m' := n) (by norm_num) hn
  have hcomm : L.z (D.alpha i) * L.z (D.alpha j) = L.z (D.alpha j) * L.z (D.alpha i) :=
    h.z_comm_of_dist_le (D.valence_alpha F i) (D.valence_alpha F j)
      (by rw [D.dist_alpha_alpha F h hij])
  constructor
  · intro hfix
    by_contra hlt
    rw [hcomm] at hfix
    exact h.mul_z_smul_ne (D.valence_alpha F i) hzj (by rw [hdi]; omega) hfix
  · intro hle
    rw [mul_smul, hzj, (h.z_smul_eq_iff (D.valence_alpha F i) _).2 (by rw [hdi]; omega)]

theorem fixed_mid (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) {i j m : Fin 5}
    (hmi : i ≠ m) (hmj : j ≠ m) (hmid : 2 * m - i = j) {n : ℕ} (hn : n ≤ 4) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • (D.P m).vert n = (D.P m).vert n := by
  refine D.fix_ball F h h512 hmi hmj hmid ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · show Γ.dist (D.beta m) ((D.P m).vert 0) ≤ 3
    rw [D.start m, SimpleGraph.dist_comm, D.dist_start_beta F m]
    norm_num
  · have := D.dist_arc F m (a := 1) (b := n) hpos hn
    show Γ.dist ((D.P m).vert 1) ((D.P m).vert n) ≤ 3
    omega

theorem fixed_iff_other (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L)
    {i j m k : Fin 5} (hij : i ≠ j) (hmi : i ≠ m) (hmj : j ≠ m) (hmid : 2 * m - i = j)
    (hki : i ≠ k) (hkj : j ≠ k) (hkm : m ≠ k) {n : ℕ} (hn : n ≤ 4) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • (D.P k).vert n = (D.P k).vert n ↔ n ≤ 3 := by
  have h : Fan71c F L := h7.2.2.1
  have hd : ∀ s : Fin 5, s ≠ k → Γ.dist (D.alpha s) ((D.P k).vert n) = 2 + n := fun s hs =>
    D.dist_vert_ne F h hs (m := 2) (m' := n) (by norm_num) hn
  constructor
  · intro hfix
    by_contra hlt
    have h4 : n = 4 := by omega
    subst h4
    exact D.moves_delta F h7 h512 hij hmi hmj hmid hkm hfix
  · intro hle
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · rw [mul_smul, (h.z_smul_eq_iff (D.valence_alpha F j) _).2 (by rw [hd j hkj]; omega),
        (h.z_smul_eq_iff (D.valence_alpha F i) _).2 (by rw [hd i hki]; omega)]
    · have h3 : n = 3 := by omega
      subst h3
      have key : ∀ s : Fin 5, s ≠ k → Γ.dist (D.alpha s) (D.alpha k) ≤ 4 ∧
          Γ.dist (D.alpha s) (D.beta k) ≤ 4 ∧ 4 < Γ.dist (D.alpha s) (D.xi k) := fun s hs => by
        refine ⟨by rw [D.dist_alpha_alpha F h hs], ?_, ?_⟩
        · rw [SimpleGraph.dist_comm, D.dist_beta_alpha_ne F h hs]
          norm_num
        · have h5 : Γ.dist (D.alpha s) (D.xi k) = 2 + 3 := hd s hs
          omega
      obtain ⟨a1, a2, a3⟩ := key i hki
      obtain ⟨b1, b2, b3⟩ := key j hkj
      exact mem_nbrStab.1 (mul_z_mem_nbrStab F h (D.valence_alpha F i) (D.valence_alpha F j)
        (D.adj_beta_alpha k).symm (D.adj_alpha_xi k) a1 a2 a3 b1 b2 b3) _ (D.adj_alpha_xi k)

end D10Set

end CFSG.Quasithin.Fan86
