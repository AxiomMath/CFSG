module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fcomm_fixes_ball_left (F : FanTree Γ G) {a b : G} {c : V} {r : ℕ}
    (ha : ∀ w, Γ.dist c w ≤ r → a • w = w) (hb : b • c = c) :
    ∀ w, Γ.dist c w ≤ r → fcomm a b • w = w := by
  intro w hw
  have hbw : Γ.dist c (b • w) ≤ r := by
    have := dist_smul F b c w
    rw [hb] at this
    omega
  have h1 : a • (b • w) = b • w := ha _ hbw
  have h2 : a⁻¹ • w = w := inv_smul_eq_iff.2 (ha w hw).symm
  unfold fcomm
  rw [mul_smul, mul_smul, mul_smul, h1, inv_smul_smul, h2]

theorem fcomm_fixes_ball_right (F : FanTree Γ G) {a b : G} {c : V} {r : ℕ}
    (hb : ∀ w, Γ.dist c w ≤ r → b • w = w) (ha : a • c = c) :
    ∀ w, Γ.dist c w ≤ r → fcomm a b • w = w := by
  intro w hw
  have haw : Γ.dist c (a • w) ≤ r := by
    have := dist_smul F a c w
    rw [ha] at this
    omega
  have h1 : b⁻¹ • (a • w) = a • w := inv_smul_eq_iff.2 (hb _ haw).symm
  unfold fcomm
  rw [mul_smul, mul_smul, mul_smul, hb w hw, h1, inv_smul_smul]

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem dist_beta_beta (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) :
    Γ.dist (D.beta i) (D.beta j) = 2 :=
  D.dist_vert_ne F h hij (m := 1) (m' := 1) (by norm_num) (by norm_num)

theorem y_fixes_beta (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (k l : Fin 5) : D.y δ' k • D.beta l = D.beta l := by
  refine (D.y_fixed_iff F h h81 hY k (by rw [D.dist_start_beta F l]; norm_num)).2 (Or.inr ?_)
  by_cases hkl : k = l
  · rw [hkl, SimpleGraph.dist_self]
    norm_num
  · rw [D.dist_beta_beta F h hkl]

theorem y_mem_nbrStab' (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (k : Fin 5) : D.y δ' k ∈ nbrStab Γ G α := by
  refine mem_nbrStab.2 fun w hw => ?_
  obtain ⟨l, rfl⟩ := D.exists_beta_eq F h hw
  exact D.y_fixes_beta F h h81 hY k l

theorem y_mul_self' (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') (k : Fin 5) :
    D.y δ' k * D.y δ' k = 1 := by
  have hZ := D.isZ2Pair_translate F h hY k
  have hv := D.valence_ypair F hY
  have hva : valence Γ ((D.x ^ k.val)⁻¹ • δ') = 5 := by rw [valence_smul F]; exact hv
  have hc : L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ') =
      L.z ((D.x ^ k.val)⁻¹ • δ') * L.z (D.delta k) := by
    refine h.z_comm_of_dist_le (D.valence_delta F k) hva ?_
    have h1 := F.isTree.connected.dist_triangle (u := D.delta k) (v := D.alpha k)
      (w := (D.x ^ k.val)⁻¹ • δ')
    have h2 : Γ.dist (D.delta k) (D.alpha k) = 2 := by
      rw [SimpleGraph.dist_comm, D.dist_alpha_delta F k]
    have h3 : Γ.dist (D.alpha k) ((D.x ^ k.val)⁻¹ • δ') = 2 := hZ.2.2.2.2.1
    omega
  rw [D.y_eq F h hv k]
  calc L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ') *
        (L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ'))
      = L.z (D.delta k) * (L.z ((D.x ^ k.val)⁻¹ • δ') * L.z (D.delta k)) *
        L.z ((D.x ^ k.val)⁻¹ • δ') := by group
    _ = 1 := by
      rw [← hc]
      calc L.z (D.delta k) * (L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ')) *
            L.z ((D.x ^ k.val)⁻¹ • δ')
          = (L.z (D.delta k) * L.z (D.delta k)) *
            (L.z ((D.x ^ k.val)⁻¹ • δ') * L.z ((D.x ^ k.val)⁻¹ • δ')) := by group
        _ = 1 := by rw [L.z_mul_self (D.valence_delta F k), L.z_mul_self hva, one_mul]

theorem y_fixes_ball_beta (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i : Fin 5) : ∀ w, Γ.dist (D.beta i) w ≤ 2 → D.y δ' i • w = w := by
  intro w hw
  have hα : Γ.dist α w ≤ 4 := by
    have := F.isTree.connected.dist_triangle (u := α) (v := D.beta i) (w := w)
    rw [D.dist_start_beta F i] at this
    omega
  exact (D.y_fixed_iff F h h81 hY i hα).2 (Or.inr hw)

theorem fcomm_y_fixes_ball_left (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i j : Fin 5) :
    ∀ w, Γ.dist (D.beta i) w ≤ 2 → fcomm (D.y δ' i) (D.y δ' j) • w = w :=
  fcomm_fixes_ball_left F (D.y_fixes_ball_beta F h h81 hY i) (D.y_fixes_beta F h h81 hY j i)

theorem fcomm_y_fixes_ball_right (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i j : Fin 5) :
    ∀ w, Γ.dist (D.beta j) w ≤ 2 → fcomm (D.y δ' i) (D.y δ' j) • w = w :=
  fcomm_fixes_ball_right F (D.y_fixes_ball_beta F h h81 hY j) (D.y_fixes_beta F h h81 hY i j)

theorem fcomm_y_mem_ballStab (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i j : Fin 5) : fcomm (D.y δ' i) (D.y δ' j) ∈ ballStab Γ G 2 α := by
  have h := (h7.2.2.2.2.2.1 α D.val).2.2.1 (D.y δ' i)⁻¹
    (inv_mem (D.y_mem_nbrStab' F h7.2.2.1 h81 hY i)) (D.y δ' j)⁻¹
    (inv_mem (D.y_mem_nbrStab' F h7.2.2.1 h81 hY j))
  simpa [fcomm] using h

end D10Set

end CFSG.Quasithin.Fan86
