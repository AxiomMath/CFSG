module

public import CFSG.Quasithin.H13.GoldschmidtU43BComm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def br (x y : G) : G := x * y * x⁻¹ * y⁻¹

theorem br_swap (x y : G) : br y x = (br x y)⁻¹ := by
  unfold br
  group

theorem br_one_right (x : G) : br x 1 = 1 := by
  unfold br
  group

theorem br_one_left (y : G) : br 1 y = 1 := by
  unfold br
  group

theorem br_eq_one_of_comm {x y : G} (h : x * y = y * x) : br x y = 1 := by
  unfold br
  calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [h]
    _ = 1 := by group

theorem mul_eq_br_mul (x y : G) : x * y = br x y * (y * x) := by
  unfold br
  group

theorem comm_of_br_eq_one {x y : G} (h : br x y = 1) : x * y = y * x := by
  rw [mul_eq_br_mul, h, one_mul]

theorem br_conj (g x y : G) : br (g⁻¹ * x * g) (g⁻¹ * y * g) = g⁻¹ * br x y * g := by
  unfold br
  group

theorem br_zp_right (x y : G) (i : ZMod 2) : br x (zp y i) = zp (br x y) i := by
  rcases zmod_two_cases i with rfl | rfl
  · rw [zp_zero, zp_zero]
    exact br_one_right x
  · rw [zp_one, zp_one]

theorem br_zp_left (x y : G) (i : ZMod 2) : br (zp x i) y = zp (br x y) i := by
  rcases zmod_two_cases i with rfl | rfl
  · rw [zp_zero, zp_zero]
    exact br_one_left y
  · rw [zp_one, zp_one]

namespace Swap

variable {z t w : G} [Finite G] (d : Swap z t w)
include d

theorem br_mem_V {b b' : G} (hb : b ∈ Bg z t) (hb' : b' ∈ Bg z t) : br b b' ∈ Vg z t :=
  d.comm_mem_V hb hb'

omit [Finite G] in
theorem V_comm {c c' : G} (hc : c ∈ Vg z t) (hc' : c' ∈ Vg z t) : c * c' = c' * c :=
  d.V_central (N1_le_B (d.Vg_le_N1 hc)) hc'

omit [Finite G] in
theorem conj_V {b c : G} (hb : b ∈ Bg z t) (hc : c ∈ Vg z t) : b * c * b⁻¹ = c := by
  calc b * c * b⁻¹ = (c * b) * b⁻¹ := by rw [d.V_central hb hc]
    _ = c := by group

theorem br_mul_right {x y y' : G} (hx : x ∈ Bg z t) (hy : y ∈ Bg z t) (hy' : y' ∈ Bg z t) :
    br x (y * y') = br x y * br x y' := by
  have e : br x (y * y') = br x y * (y * br x y' * y⁻¹) := by
    unfold br
    group
  rw [e, d.conj_V hy (d.br_mem_V hx hy')]

theorem br_mul_left {x x' y : G} (hx : x ∈ Bg z t) (hx' : x' ∈ Bg z t) (hy : y ∈ Bg z t) :
    br (x * x') y = br x y * br x' y := by
  have e : br (x * x') y = (x * br x' y * x⁻¹) * br x y := by
    unfold br
    group
  rw [e, d.conj_V hx (d.br_mem_V hx' hy)]
  exact d.V_comm (d.br_mem_V hx' hy) (d.br_mem_V hx hy)

omit [Finite G] in
theorem br_V_left {v b : G} (hv : v ∈ Vg z t) (hb : b ∈ Bg z t) : br v b = 1 :=
  br_eq_one_of_comm (d.V_central hb hv).symm

omit [Finite G] in
theorem br_V_right {b v : G} (hb : b ∈ Bg z t) (hv : v ∈ Vg z t) : br b v = 1 :=
  br_eq_one_of_comm (d.V_central hb hv)

end Swap

end CFSG.Quasithin.H13.U43
