module

public import CFSG.Quasithin.H13.GoldschmidtU43BNorm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin.H13.A5.Orth

variable {G : Type} [Group G]

structure Comm4 (g : Fin 4 → G) : Prop where
  sq : ∀ i, g i * g i = 1
  comm : ∀ i j, g i * g j = g j * g i

@[expose] def crd (g : Fin 4 → G) (c : V4) : G :=
  zp (g 0) (c 0) * zp (g 1) (c 1) * zp (g 2) (c 2) * zp (g 3) (c 3)

theorem crd_zero (g : Fin 4 → G) : crd g 0 = 1 := by
  simp [crd, zp_zero]

theorem zp_crd (g : Fin 4 → G) (m : V4) (b : ZMod 2) : zp (crd g m) b = crd g (b • m) := by
  rcases zmod_two_cases b with rfl | rfl
  · rw [zp_zero, zero_smul, crd_zero]
  · rw [zp_one, one_smul]

theorem crd_idc (g : Fin 4 → G) (i : Fin 4) : crd g (idc i) = g i := by
  fin_cases i <;> simp [crd, idc, zp_zero, zp_one]

theorem comm4_mk {g0 g1 g2 g3 : G} (s0 : g0 * g0 = 1) (s1 : g1 * g1 = 1) (s2 : g2 * g2 = 1)
    (s3 : g3 * g3 = 1) (c01 : g0 * g1 = g1 * g0) (c02 : g0 * g2 = g2 * g0)
    (c03 : g0 * g3 = g3 * g0) (c12 : g1 * g2 = g2 * g1) (c13 : g1 * g3 = g3 * g1)
    (c23 : g2 * g3 = g3 * g2) : Comm4 ![g0, g1, g2, g3] := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simpa
  · fin_cases i <;> fin_cases j <;> simp <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm

namespace Comm4

variable {g : Fin 4 → G} (hg : Comm4 g)
include hg

theorem zp_comm (i j : Fin 4) (a b : ZMod 2) :
    zp (g i) a * zp (g j) b = zp (g j) b * zp (g i) a := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [zp_zero, zp_one, hg.comm i j]

theorem commute (i j : Fin 4) (a b : ZMod 2) : Commute (zp (g i) a) (zp (g j) b) :=
  hg.zp_comm i j a b

theorem crd_add (c d : V4) : crd g (c + d) = crd g c * crd g d := by
  unfold crd
  simp only [Pi.add_apply]
  rw [← zp_add (hg.sq 0), ← zp_add (hg.sq 1), ← zp_add (hg.sq 2), ← zp_add (hg.sq 3)]
  simp only [mul_assoc]
  rw [(hg.commute 3 0 (c 3) (d 0)).left_comm, (hg.commute 2 0 (c 2) (d 0)).left_comm,
    (hg.commute 1 0 (c 1) (d 0)).left_comm, (hg.commute 3 1 (c 3) (d 1)).left_comm,
    (hg.commute 2 1 (c 2) (d 1)).left_comm, (hg.commute 3 2 (c 3) (d 2)).left_comm]

theorem conj_crd (k : G) (M : Fin 4 → V4) (hM : ∀ i, k * g i * k⁻¹ = crd g (M i)) (c : V4) :
    k * crd g c * k⁻¹ = crd g (app M c) := by
  have e : k * crd g c * k⁻¹ = (k * zp (g 0) (c 0) * k⁻¹) * (k * zp (g 1) (c 1) * k⁻¹) *
      (k * zp (g 2) (c 2) * k⁻¹) * (k * zp (g 3) (c 3) * k⁻¹) := by
    unfold crd
    group
  rw [e, conj_zp, conj_zp, conj_zp, conj_zp, hM 0, hM 1, hM 2, hM 3, zp_crd g, zp_crd g,
    zp_crd g, zp_crd g]
  unfold app
  rw [hg.crd_add, hg.crd_add, hg.crd_add]

theorem crd_injective (hind : ∀ c, crd g c = 1 → c = 0) {c c' : V4} (h : crd g c = crd g c') :
    c = c' := by
  have h1 : crd g (c + c') = 1 := by
    rw [hg.crd_add, ← h, ← hg.crd_add]
    have : c + c = 0 := by
      have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact h2 _
    rw [this, crd_zero]
  have := hind _ h1
  funext i
  have hi := congrFun this i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact key _ _ hi

end Comm4

end CFSG.Quasithin.H13.U43
