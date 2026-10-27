module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.StandardType.GGSporKHeis13Conj
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HeisThirteen
import CFSG.Open.Defs

public section

namespace CFSG.StandardType.SporadicShape

open scoped commutatorElement

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

private theorem gkh_comm_z_xy {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y) (m a b : ℕ) :
    Commute (z ^ m) (x ^ a * y ^ b) :=
  ((hzx.pow_left m).pow_right a).mul_right ((hzy.pow_left m).pow_right b)

private theorem gkh_z_pow_inv {G : Type*} [Group G] {z : G} (hz : z ^ 13 = 1) (m : ℕ) :
    (z ^ (9 * m))⁻¹ = z ^ (4 * m) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_add, show 9 * m + 4 * m = 13 * m by ring, pow_mul, hz,
    one_pow]

private theorem gkh_comm_xy {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) : ⁅x, y⁆ = z ^ 9 := by
  have hgd : x * y * x⁻¹ = y * z ^ 9 := gd_conj hzx hzy hyx hz
  have hy9 : y * z ^ 9 * y⁻¹ = z ^ 9 := by
    rw [← (hzy.pow_left 9).eq]; group
  rw [commutatorElement_def, hgd, hy9]

private theorem gkh_yx {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (p q : ℕ) :
    y ^ q * x ^ p = x ^ p * y ^ q * z ^ (4 * p * q) := by
  have h := gpow_dpow hzx hzy hyx hz p q
  have h2 : y ^ q * x ^ p = x ^ p * y ^ q * (z ^ (9 * p * q))⁻¹ := by rw [h]; group
  rw [show 9 * p * q = 9 * (p * q) by ring, gkh_z_pow_inv hz, show 4 * (p * q) = 4 * p * q by ring]
    at h2
  exact h2

private theorem gkh_mul {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (p q s r t v : ℕ) :
    (x ^ p * y ^ q * z ^ s) * (x ^ r * y ^ t * z ^ v) =
      x ^ (p + r) * y ^ (q + t) * z ^ (s + v + 4 * r * q) := by
  have h1 : z ^ s * (x ^ r * y ^ t) = (x ^ r * y ^ t) * z ^ s :=
    (gkh_comm_z_xy hzx hzy s r t).eq
  have h2 : y ^ q * x ^ r = x ^ r * y ^ q * z ^ (4 * r * q) := gkh_yx hzx hzy hyx hz r q
  have h3 : z ^ (4 * r * q) * y ^ t = y ^ t * z ^ (4 * r * q) :=
    ((hzy.pow_left (4 * r * q)).pow_right t).eq
  calc (x ^ p * y ^ q * z ^ s) * (x ^ r * y ^ t * z ^ v)
      = x ^ p * y ^ q * (z ^ s * (x ^ r * y ^ t)) * z ^ v := by group
    _ = x ^ p * y ^ q * ((x ^ r * y ^ t) * z ^ s) * z ^ v := by rw [h1]
    _ = x ^ p * y ^ q * (x ^ r * y ^ t) * (z ^ s * z ^ v) := by group
    _ = x ^ p * (y ^ q * x ^ r) * y ^ t * (z ^ s * z ^ v) := by group
    _ = x ^ p * (x ^ r * y ^ q * z ^ (4 * r * q)) * y ^ t * (z ^ s * z ^ v) := by rw [h2]
    _ = x ^ p * (x ^ r * y ^ q) * (z ^ (4 * r * q) * y ^ t) * (z ^ s * z ^ v) := by group
    _ = x ^ p * (x ^ r * y ^ q) * (y ^ t * z ^ (4 * r * q)) * (z ^ s * z ^ v) := by rw [h3]
    _ = x ^ (p + r) * y ^ (q + t) * z ^ (s + v + 4 * r * q) := by
          rw [show x ^ p * (x ^ r * y ^ q) * (y ^ t * z ^ (4 * r * q)) * (z ^ s * z ^ v) =
                (x ^ p * x ^ r) * (y ^ q * y ^ t) * (z ^ (4 * r * q) * (z ^ s * z ^ v)) by
                  group,
            ← pow_add, ← pow_add, ← pow_add, ← pow_add,
            show 4 * r * q + (s + v) = s + v + 4 * r * q by ring]

private theorem gkh_conj_z {G : Type*} [Group G] {g c : G} (h : Commute c g) : g * c * g⁻¹ = c := by
  rw [← h.eq]; group

private theorem gkh_comm_yx {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (B C : ℕ) :
    ⁅y ^ B, x ^ C⁆ = z ^ (4 * C * B) := by
  have h4 : ⁅y, x⁆ = z ^ 4 := by
    rw [← commutatorElement_inv, gkh_comm_xy hzx hzy hyx hz]
    exact (by simpa using gkh_z_pow_inv hz 1)
  have hC : ⁅y, x ^ C⁆ = z ^ (4 * C) := by
    have hcomm : Commute x ⁅y, x⁆ := by rw [h4]; exact (hzx.pow_left 4).symm
    have := Commute.commutatorElement_pow_right hcomm C
    rw [← this, h4, ← pow_mul]
  have hB : ⁅y ^ B, x ^ C⁆ = z ^ (4 * C * B) := by
    have hcomm : Commute y ⁅y, x ^ C⁆ := by rw [hC]; exact (hzy.pow_left (4 * C)).symm
    have := Commute.commutatorElement_pow_left hcomm B
    rw [← this, hC, ← pow_mul]
  exact hB

private theorem gkh_comm_xy_pow {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (A D : ℕ) :
    ⁅x ^ A, y ^ D⁆ = z ^ (9 * A * D) := by
  have hcomm : Commute x ⁅x, y⁆ := by rw [gkh_comm_xy hzx hzy hyx hz]; exact (hzx.pow_left 9).symm
  have hA : ⁅x ^ A, y⁆ = z ^ (9 * A) := by
    have := Commute.commutatorElement_pow_left hcomm A
    rw [← this, gkh_comm_xy hzx hzy hyx hz, ← pow_mul]
  have hcomm2 : Commute y ⁅x ^ A, y⁆ := by rw [hA]; exact (hzy.pow_left (9 * A)).symm
  have := Commute.commutatorElement_pow_right hcomm2 D
  rw [← this, hA, ← pow_mul]

private theorem gkh_comm_pow {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (A B C D : ℕ) :
    ⁅x ^ A * y ^ B, x ^ C * y ^ D⁆ = z ^ (9 * A * D + 4 * B * C) := by
  have hxA : Commute (x ^ A) (x ^ C) := (Commute.refl x).pow_left A |>.pow_right C
  have hA4 : Commute (z ^ (4 * C * B)) (x ^ A) := (hzx.pow_left (4 * C * B)).pow_right A
  have hA9 : Commute (z ^ (9 * A * D)) (x ^ A) := (hzx.pow_left (9 * A * D)).pow_right A
  have hC9 : Commute (z ^ (9 * A * D)) (x ^ C) := (hzx.pow_left (9 * A * D)).pow_right C
  have h1 : ⁅x ^ A * y ^ B, x ^ C⁆ = z ^ (4 * C * B) := by
    rw [commutatorElement_mul_left_eq_conj_mul, hxA.commutator_eq, gkh_comm_yx hzx hzy hyx hz,
      mul_one, gkh_conj_z hA4]
  have h2 : ⁅x ^ A * y ^ B, y ^ D⁆ = z ^ (9 * A * D) := by
    rw [commutatorElement_mul_left_eq_conj_mul, gkh_comm_xy_pow hzx hzy hyx hz,
      ((Commute.refl y).pow_left B |>.pow_right D).commutator_eq, mul_one]
    group
  rw [commutatorElement_mul_right_eq_mul_conj, h1, h2,
    show z ^ (4 * C * B) * x ^ C * z ^ (9 * A * D) * (x ^ C)⁻¹ =
      z ^ (4 * C * B) * (x ^ C * z ^ (9 * A * D) * (x ^ C)⁻¹) by group,
    gkh_conj_z hC9,
    ← pow_add, show 4 * C * B + 9 * A * D = 9 * A * D + 4 * B * C by ring]

private theorem gkh_comm_strip_left {G : Type*} [Group G] {u v c : G} (hcu : Commute c u)
    (hcv : Commute c v) :
    ⁅u * c, v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hcv.commutator_eq, mul_one]
  group

private theorem gkh_comm_strip_right {G : Type*} [Group G] {u v c : G} (hcu : Commute c u)
    (hcv : Commute c v) :
    ⁅u, v * c⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, hcu.symm.commutator_eq, mul_one]
  group

private theorem gkh_comm_z {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (A B C D M N : ℕ) :
    ⁅x ^ A * y ^ B * z ^ M, x ^ C * y ^ D * z ^ N⁆ = z ^ (9 * A * D + 4 * B * C) := by
  have hLN : Commute (z ^ N) (x ^ A * y ^ B) := gkh_comm_z_xy hzx hzy N A B
  have hRN : Commute (z ^ N) (x ^ C * y ^ D) := gkh_comm_z_xy hzx hzy N C D
  have hLM : Commute (z ^ M) (x ^ A * y ^ B) := gkh_comm_z_xy hzx hzy M A B
  have hRM : Commute (z ^ M) (x ^ C * y ^ D) := gkh_comm_z_xy hzx hzy M C D
  have hMN : Commute (z ^ M) (z ^ N) := (Commute.refl z).pow_left M |>.pow_right N
  have hMRL : Commute (z ^ M) (x ^ C * y ^ D * z ^ N) := hRM.mul_right hMN
  rw [gkh_comm_strip_left (u := x ^ A * y ^ B) (v := x ^ C * y ^ D * z ^ N) (c := z ^ M)
      hLM hMRL,
    gkh_comm_strip_right (u := x ^ A * y ^ B) (v := x ^ C * y ^ D) (c := z ^ N) hLN hRN,
    gkh_comm_pow hzx hzy hyx hz]

private theorem gkh_pow_xy {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (p q n : ℕ) :
    (x ^ p * y ^ q) ^ n = x ^ (p * n) * y ^ (q * n) * z ^ (4 * p * q * n.choose 2) := by
  have h := heis_pow_choose hzx hzy hyx hz p q n
  have h2 : (x ^ p * y ^ q) ^ n =
      x ^ (p * n) * y ^ (q * n) * (z ^ (9 * p * q * n.choose 2))⁻¹ := by rw [h]; group
  rw [show 9 * p * q * n.choose 2 = 9 * (p * q * n.choose 2) by ring, gkh_z_pow_inv hz,
    show 4 * (p * q * n.choose 2) = 4 * p * q * n.choose 2 by ring] at h2
  exact h2

private theorem gkh_pow {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (p q s n : ℕ) :
    (x ^ p * y ^ q * z ^ s) ^ n =
      x ^ (p * n) * y ^ (q * n) * z ^ (s * n + 4 * p * q * n.choose 2) := by
  have hc : Commute (x ^ p * y ^ q) (z ^ s) := (gkh_comm_z_xy hzx hzy s p q).symm
  rw [hc.mul_pow, gkh_pow_xy hzx hzy hyx hz, ← pow_mul]
  rw [show x ^ (p * n) * y ^ (q * n) * z ^ (4 * p * q * n.choose 2) * z ^ (s * n) =
        x ^ (p * n) * y ^ (q * n) * (z ^ (4 * p * q * n.choose 2) * z ^ (s * n)) by group,
    ← pow_add, show 4 * p * q * n.choose 2 + s * n = s * n + 4 * p * q * n.choose 2 by ring]

private theorem gkh_zyx {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) (p q s : ℕ) :
    z ^ s * y ^ q * x ^ p = x ^ p * y ^ q * z ^ (s + 4 * p * q) := by
  calc z ^ s * y ^ q * x ^ p
      = z ^ s * (y ^ q * x ^ p) := by simp only [mul_assoc]
    _ = z ^ s * (x ^ p * y ^ q * z ^ (4 * p * q)) := by rw [gkh_yx hzx hzy hyx hz]
    _ = (z ^ s * (x ^ p * y ^ q)) * z ^ (4 * p * q) := by simp only [mul_assoc]
    _ = (x ^ p * y ^ q * z ^ s) * z ^ (4 * p * q) := by
          rw [show z ^ s * (x ^ p * y ^ q) = x ^ p * y ^ q * z ^ s from
            (gkh_comm_z_xy hzx hzy s p q).eq]
    _ = x ^ p * y ^ q * (z ^ s * z ^ (4 * p * q)) := by simp only [mul_assoc]
    _ = x ^ p * y ^ q * z ^ (s + 4 * p * q) := by rw [← pow_add]

private theorem gkh_conj_pow3 {G : Type*} [Group G] {x y z : G} {u : G} (A B M : ℕ) :
    (u * x * u⁻¹) ^ A * (u * y * u⁻¹) ^ B * (u * z * u⁻¹) ^ M =
      u * (x ^ A * y ^ B * z ^ M) * u⁻¹ := by
  rw [conj_pow, conj_pow, conj_pow, ← conj_mul, ← conj_mul]

private theorem gkh_conj_u_z {G : Type*} [Group G] {x y z : G} (hz : z ^ 13 = 1)
    (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) {u : G}
    (hux : u * x = z ^ 8 * (y ^ 7 * (x ^ 7 * u)))
    (huy : u * y = z ^ 6 * (y ^ 7 * (x ^ 5 * u))) :
    u * z * u⁻¹ = z := by
  rw [CFSG.StandardType.SporadicShape.heis13_conj_z hz hzx hzy hyx hux huy,
    show (((7 : ℕ) : ℤ) * ((7 : ℕ) : ℤ) - ((5 : ℕ) : ℤ) * ((7 : ℕ) : ℤ)) =
      ((14 : ℕ) : ℤ) by norm_num, zpow_natCast,
    show (14 : ℕ) = 13 + 1 by norm_num, pow_add, hz, one_mul, pow_one]

private theorem gkh_conj_kx {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {k : G}
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k))) :
    k * x * k⁻¹ = x ^ 6 * y ^ 10 * z ^ 251 := by
  have h : k * x * k⁻¹ = z ^ 11 * y ^ 10 * x ^ 6 := by rw [hkx]; group
  rw [h, gkh_zyx hzx hzy hyx hz 6 10 11]

private theorem gkh_conj_ky {G : Type*} [Group G] {x y z : G} (hzx : Commute z x)
    (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {k : G}
    (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k))) :
    k * y * k⁻¹ = x ^ 1 * y ^ 7 * z ^ 31 := by
  have h : k * y * k⁻¹ = z ^ 3 * y ^ 7 * x ^ 1 := by rw [hky]; group
  rw [h, gkh_zyx hzx hzy hyx hz 1 7 3]

private theorem gkh_conj_k_z {G : Type*} [Group G] {x y z : G} (hz : z ^ 13 = 1)
    (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) {k : G}
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k)))
    (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k))) :
    k * z * k⁻¹ = z ^ 6 := by
  rw [CFSG.StandardType.SporadicShape.heis13_conj_z hz hzx hzy hyx hkx hky,
    show (((6 : ℕ) : ℤ) * ((7 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) * ((10 : ℕ) : ℤ)) =
      ((32 : ℕ) : ℤ) by norm_num, zpow_natCast,
    show (32 : ℕ) = 13 * 2 + 6 by norm_num, pow_add, pow_mul, hz, one_pow, one_mul]

private theorem gkh_conj_k_inv_z {G : Type*} [Group G] {x y z : G} (hz : z ^ 13 = 1)
    (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) {k : G}
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k)))
    (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k))) :
    k⁻¹ * z * k = z ^ 11 := by
  have hkz := gkh_conj_k_z hz hzx hzy hyx hkx hky
  have h1 : k * (k⁻¹ * z * k) * k⁻¹ = k * z ^ 11 * k⁻¹ := by
    rw [show k * (k⁻¹ * z * k) * k⁻¹ = z by group, ← conj_pow, hkz,
      show (z ^ 6) ^ 11 = z by
        rw [← pow_mul, show 6 * 11 = 13 * 5 + 1 by norm_num, pow_add, pow_mul, hz, one_pow,
          one_mul, pow_one]]
  exact mul_left_cancel (mul_right_cancel h1)

private def gkh_E (A B : ℕ) : ℕ := 9 * A * (7 * A + 7 * B) + 4 * B * (7 * A + 5 * B)

private theorem gkh_conj_u {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {u : G}
    (hux : u * x = z ^ 8 * (y ^ 7 * (x ^ 7 * u)))
    (huy : u * y = z ^ 6 * (y ^ 7 * (x ^ 5 * u))) (A B M : ℕ) :
    ∃ K : ℕ, u * (x ^ A * y ^ B * z ^ M) * u⁻¹ =
      x ^ (7 * A + 5 * B) * y ^ (7 * A + 7 * B) * z ^ K := by
  have huz : u * z * u⁻¹ = z := gkh_conj_u_z hz hzx hzy hyx hux huy
  have hX : u * x * u⁻¹ = x ^ 7 * y ^ 7 * z ^ 204 := by
    have h : u * x * u⁻¹ = z ^ 8 * y ^ 7 * x ^ 7 := by rw [hux]; group
    rw [h, gkh_zyx hzx hzy hyx hz 7 7 8]
  have hY : u * y * u⁻¹ = x ^ 5 * y ^ 7 * z ^ 146 := by
    have h : u * y * u⁻¹ = z ^ 6 * y ^ 7 * x ^ 5 := by rw [huy]; group
    rw [h, gkh_zyx hzx hzy hyx hz 5 7 6]
  refine ⟨((204 * A + 4 * 7 * 7 * A.choose 2) + (146 * B + 4 * 5 * 7 * B.choose 2) +
    4 * (5 * B) * (7 * A)) + M, ?_⟩
  calc u * (x ^ A * y ^ B * z ^ M) * u⁻¹
      = (u * x * u⁻¹) ^ A * (u * y * u⁻¹) ^ B * (u * z * u⁻¹) ^ M :=
        (gkh_conj_pow3 A B M).symm
    _ = (x ^ 7 * y ^ 7 * z ^ 204) ^ A * (x ^ 5 * y ^ 7 * z ^ 146) ^ B * z ^ M := by
        rw [hX, hY, huz]
    _ = x ^ (7 * A) * y ^ (7 * A) * z ^ (204 * A + 4 * 7 * 7 * A.choose 2) *
          (x ^ (5 * B) * y ^ (7 * B) * z ^ (146 * B + 4 * 5 * 7 * B.choose 2)) * z ^ M := by
        rw [gkh_pow hzx hzy hyx hz, gkh_pow hzx hzy hyx hz]
    _ = x ^ (7 * A + 5 * B) * y ^ (7 * A + 7 * B) *
          z ^ (((204 * A + 4 * 7 * 7 * A.choose 2) + (146 * B + 4 * 5 * 7 * B.choose 2) +
            4 * (5 * B) * (7 * A)) + M) := by
        rw [gkh_mul hzx hzy hyx hz,
          show x ^ (7 * A + 5 * B) * y ^ (7 * A + 7 * B) *
                z ^ ((204 * A + 4 * 7 * 7 * A.choose 2) + (146 * B + 4 * 5 * 7 * B.choose 2) +
                  4 * (5 * B) * (7 * A)) * z ^ M =
              x ^ (7 * A + 5 * B) * y ^ (7 * A + 7 * B) *
                (z ^ ((204 * A + 4 * 7 * 7 * A.choose 2) + (146 * B + 4 * 5 * 7 * B.choose 2) +
                  4 * (5 * B) * (7 * A)) * z ^ M) by group,
            ← pow_add]

private theorem gkh_conj_k {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {k : G}
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k)))
    (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k))) (A B M : ℕ) :
    ∃ K : ℕ, k * (x ^ A * y ^ B * z ^ M) * k⁻¹ =
      x ^ (6 * A + 1 * B) * y ^ (10 * A + 7 * B) * z ^ K := by
  have hkz : k * z * k⁻¹ = z ^ 6 := gkh_conj_k_z hz hzx hzy hyx hkx hky
  have hX : k * x * k⁻¹ = x ^ 6 * y ^ 10 * z ^ 251 := gkh_conj_kx hzx hzy hyx hz hkx
  have hY : k * y * k⁻¹ = x ^ 1 * y ^ 7 * z ^ 31 := gkh_conj_ky hzx hzy hyx hz hky
  refine ⟨((251 * A + 4 * 6 * 10 * A.choose 2) + (31 * B + 4 * 1 * 7 * B.choose 2) +
    4 * (1 * B) * (10 * A)) + 6 * M, ?_⟩
  calc k * (x ^ A * y ^ B * z ^ M) * k⁻¹
      = (k * x * k⁻¹) ^ A * (k * y * k⁻¹) ^ B * (k * z * k⁻¹) ^ M :=
        (gkh_conj_pow3 A B M).symm
    _ = (x ^ 6 * y ^ 10 * z ^ 251) ^ A * (x ^ 1 * y ^ 7 * z ^ 31) ^ B * (z ^ 6) ^ M := by
        rw [hX, hY, hkz]
    _ = x ^ (6 * A) * y ^ (10 * A) * z ^ (251 * A + 4 * 6 * 10 * A.choose 2) *
          (x ^ (1 * B) * y ^ (7 * B) * z ^ (31 * B + 4 * 1 * 7 * B.choose 2)) * (z ^ 6) ^ M := by
        rw [gkh_pow hzx hzy hyx hz, gkh_pow hzx hzy hyx hz]
    _ = x ^ (6 * A + 1 * B) * y ^ (10 * A + 7 * B) *
          z ^ (((251 * A + 4 * 6 * 10 * A.choose 2) + (31 * B + 4 * 1 * 7 * B.choose 2) +
            4 * (1 * B) * (10 * A)) + 6 * M) := by
        rw [gkh_mul hzx hzy hyx hz, ← pow_mul,
          show x ^ (6 * A + 1 * B) * y ^ (10 * A + 7 * B) *
                z ^ ((251 * A + 4 * 6 * 10 * A.choose 2) + (31 * B + 4 * 1 * 7 * B.choose 2) +
                  4 * (1 * B) * (10 * A)) * z ^ (6 * M) =
              x ^ (6 * A + 1 * B) * y ^ (10 * A + 7 * B) *
                (z ^ ((251 * A + 4 * 6 * 10 * A.choose 2) + (31 * B + 4 * 1 * 7 * B.choose 2) +
                  4 * (1 * B) * (10 * A)) * z ^ (6 * M)) by group,
            ← pow_add]

private theorem gkh_u_comm {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {u : G}
    (hux : u * x = z ^ 8 * (y ^ 7 * (x ^ 7 * u)))
    (huy : u * y = z ^ 6 * (y ^ 7 * (x ^ 5 * u))) (A B M : ℕ) :
    ⁅x ^ A * y ^ B * z ^ M, u * (x ^ A * y ^ B * z ^ M) * u⁻¹⁆ = z ^ (gkh_E A B) := by
  obtain ⟨K, hK⟩ := gkh_conj_u hzx hzy hyx hz hux huy A B M
  rw [hK, gkh_comm_z hzx hzy hyx hz]
  rfl

private theorem gkh_w_comm {G : Type*} [Group G] {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    (hyx : y * x = x * (y * z ^ 4)) (hz : z ^ 13 = 1) {u k : G}
    (hux : u * x = z ^ 8 * (y ^ 7 * (x ^ 7 * u)))
    (huy : u * y = z ^ 6 * (y ^ 7 * (x ^ 5 * u)))
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k)))
    (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k))) (A B M : ℕ) :
    ⁅x ^ A * y ^ B * z ^ M,
        (k⁻¹ * u * k) * (x ^ A * y ^ B * z ^ M) * (k⁻¹ * u * k)⁻¹⁆ =
      z ^ (11 * gkh_E (6 * A + 1 * B) (10 * A + 7 * B)) := by
  obtain ⟨K, hK⟩ := gkh_conj_k hzx hzy hyx hz hkx hky A B M
  have hik : k⁻¹ * z * k = z ^ 11 := gkh_conj_k_inv_z hz hzx hzy hyx hkx hky
  have e1 : x ^ A * y ^ B * z ^ M = k⁻¹ * (k * (x ^ A * y ^ B * z ^ M) * k⁻¹) * k := by
    group
  have e2 : (k⁻¹ * u * k) * (k⁻¹ * (k * (x ^ A * y ^ B * z ^ M) * k⁻¹) * k) *
        (k⁻¹ * u * k)⁻¹ = k⁻¹ * (u * (k * (x ^ A * y ^ B * z ^ M) * k⁻¹) * u⁻¹) * k := by
    group
  have hcc := (conjugate_commutatorElement (k * (x ^ A * y ^ B * z ^ M) * k⁻¹)
    (u * (k * (x ^ A * y ^ B * z ^ M) * k⁻¹) * u⁻¹) k⁻¹).symm
  simp only [inv_inv] at hcc
  have hcomm := gkh_u_comm hzx hzy hyx hz hux huy (6 * A + 1 * B) (10 * A + 7 * B) K
  rw [e1, e2, hcc, hK, hcomm,
    show k⁻¹ * z ^ (gkh_E (6 * A + 1 * B) (10 * A + 7 * B)) * k =
      (k⁻¹ * z * k) ^ (gkh_E (6 * A + 1 * B) (10 * A + 7 * B)) by
        simpa only [inv_inv] using
          (conj_pow (a := k⁻¹) (b := z) (i := gkh_E (6 * A + 1 * B) (10 * A + 7 * B))).symm,
    hik, pow_mul]

private theorem gkh_finite_check (i j : ZMod 13)
    (h1 : 9 * (i * (7 * i + 7 * j)) + 4 * (j * (7 * i + 5 * j)) = 0)
    (h2 : 11 * (9 * ((6 * i + 1 * j) * (7 * (6 * i + 1 * j) + 7 * (10 * i + 7 * j))) +
          4 * ((10 * i + 7 * j) * (7 * (6 * i + 1 * j) + 5 * (10 * i + 7 * j)))) = 0) :
    i = 0 ∧ j = 0 := by
  revert i j
  decide


theorem heis13_invariant_dichotomy {G : Type*} [Group G] {x y z u k : G}
    (hx : x ^ 13 = 1) (hy : y ^ 13 = 1) (hz : z ^ 13 = 1) (hz1 : z ≠ 1)
    (hzx : z * x = x * z) (hzy : z * y = y * z) (hyx : y * x = x * (y * z ^ 4))
    (hS : Nat.card (Subgroup.closure ({x, y} : Set G)) = 13 ^ 3)
    (hux : u * x = z ^ 8 * (y ^ 7 * (x ^ 7 * u))) (huy : u * y = z ^ 6 * (y ^ 7 * (x ^ 5 * u)))
    (hkx : k * x = z ^ 11 * (y ^ 10 * (x ^ 6 * k))) (hky : k * y = z ^ 3 * (y ^ 7 * (x ^ 1 * k)))
    (N : Subgroup G) (hzN : Subgroup.zpowers z ≤ N) (hNS : N ≤ Subgroup.closure ({x, y} : Set G))
    (hNu : ∀ a ∈ N, u * a * u⁻¹ ∈ N)
    (hNw : ∀ a ∈ N, (k⁻¹ * u * k) * a * (k⁻¹ * u * k)⁻¹ ∈ N) :
    N = Subgroup.zpowers z ∨ N = Subgroup.closure ({x, y} : Set G) := by
  set S : Subgroup G := Subgroup.closure ({x, y} : Set G) with hSdef
  have hScard : Nat.card S = 13 ^ 3 := by rw [hSdef]; exact hS
  have hxy9 : ⁅x, y⁆ = z ^ 9 := gkh_comm_xy hzx hzy hyx hz
  haveI hSfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hScard]; norm_num)
  have hzS : z ∈ S := by
    have hxS : x ∈ S := Subgroup.subset_closure (by simp)
    have hyS : y ∈ S := Subgroup.subset_closure (by simp)
    have hz4 : z ^ 4 = y⁻¹ * x⁻¹ * y * x := by
      calc z ^ 4 = y⁻¹ * x⁻¹ * (x * (y * z ^ 4)) := by group
        _ = y⁻¹ * x⁻¹ * (y * x) := by rw [hyx]
        _ = y⁻¹ * x⁻¹ * y * x := by group
    have hz4S : z ^ 4 ∈ S := by
      rw [hz4]
      exact S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem hyS) (S.inv_mem hxS)) hyS) hxS
    have hz40 : z ^ 40 = z := by
      rw [show (40 : ℕ) = 13 * 3 + 1 by norm_num, pow_add, pow_mul, hz, one_pow, one_mul, pow_one]
    have hz_eq : z = (z ^ 4) ^ 10 := by rw [← pow_mul, show 4 * 10 = 40 by norm_num, hz40]
    rw [hz_eq]
    exact S.pow_mem hz4S 10
  have horder : orderOf z = 13 := by
    have hdvd : orderOf z ∣ 13 := (orderOf_dvd_iff_pow_eq_one).2 hz
    rcases (by norm_num : Nat.Prime 13).eq_one_or_self_of_dvd (orderOf z) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hzpow : ∀ m : ℕ, z ^ m = 1 ↔ 13 ∣ m := by
    intro m
    rw [← orderOf_dvd_iff_pow_eq_one, horder]
  by_cases hNz : N = Subgroup.zpowers z
  · exact Or.inl hNz
  · right
    have hex : ∃ a ∈ N, a ∉ Subgroup.zpowers z := by
      by_contra h
      push Not at h
      exact hNz (le_antisymm h hzN)
    obtain ⟨a, haN, haz⟩ := hex
    have haS : a ∈ S := hNS haN
    obtain ⟨i, j, m0, hi, hj, -, ha_eq⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm (r := 13) (by norm_num) hx hy
        (by rw [hxy9]; exact (show Commute z x from hzx).pow_left 9)
        (by rw [hxy9]; exact (show Commute z y from hzy).pow_left 9) haS
    have ha : a = x ^ i * y ^ j * z ^ (9 * m0) := by
      rw [ha_eq, hxy9, ← pow_mul]
    have hne : i ≠ 0 ∨ j ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨hi0, hj0⟩ := h
      apply haz
      rw [ha, hi0, hj0]
      simp only [pow_zero, one_mul, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨(9 * m0 : ℕ), by rw [zpow_natCast]⟩
    have hsome : ⁅a, u * a * u⁻¹⁆ ≠ 1 ∨
        ⁅a, (k⁻¹ * u * k) * a * (k⁻¹ * u * k)⁻¹⁆ ≠ 1 := by
      by_contra h
      push Not at h
      obtain ⟨h1, h2⟩ := h
      rw [ha] at h1 h2
      have e1 : z ^ (gkh_E i j) = 1 := by
        rw [← gkh_u_comm hzx hzy hyx hz hux huy i j (9 * m0)]
        exact h1
      have e2 : z ^ (11 * gkh_E (6 * i + 1 * j) (10 * i + 7 * j)) = 1 := by
        rw [← gkh_w_comm hzx hzy hyx hz hux huy hkx hky i j (9 * m0)]
        exact h2
      have hd1 : 13 ∣ gkh_E i j := (hzpow _).1 e1
      have hd2 : 13 ∣ 11 * gkh_E (6 * i + 1 * j) (10 * i + 7 * j) := (hzpow _).1 e2
      have hc1 : (gkh_E i j : ZMod 13) = 0 := (ZMod.natCast_eq_zero_iff _ 13).2 hd1
      have hc2 : (((11 * gkh_E (6 * i + 1 * j) (10 * i + 7 * j) : ℕ)) : ZMod 13) = 0 :=
        (ZMod.natCast_eq_zero_iff _ 13).2 hd2
      have hf1 : 9 * ((i : ZMod 13) * (7 * (i : ZMod 13) + 7 * (j : ZMod 13))) +
          4 * ((j : ZMod 13) * (7 * (i : ZMod 13) + 5 * (j : ZMod 13))) = 0 := by
        rw [← hc1]
        unfold gkh_E
        push_cast
        ring
      have hf2 : 11 * (9 * (((6 * (i : ZMod 13) + 1 * (j : ZMod 13))) *
            (7 * (6 * (i : ZMod 13) + 1 * (j : ZMod 13)) +
              7 * (10 * (i : ZMod 13) + 7 * (j : ZMod 13)))) +
          4 * ((10 * (i : ZMod 13) + 7 * (j : ZMod 13)) *
            (7 * (6 * (i : ZMod 13) + 1 * (j : ZMod 13)) +
              5 * (10 * (i : ZMod 13) + 7 * (j : ZMod 13))))) = 0 := by
        rw [← hc2]
        unfold gkh_E
        push_cast
        ring
      obtain ⟨hi0, hj0⟩ := gkh_finite_check (i : ZMod 13) (j : ZMod 13) hf1 hf2
      have hi13 : 13 ∣ i := (ZMod.natCast_eq_zero_iff i 13).1 hi0
      have hj13 : 13 ∣ j := (ZMod.natCast_eq_zero_iff j 13).1 hj0
      have hi0' : i = 0 := by omega
      have hj0' : j = 0 := by omega
      rcases hne with h | h
      · exact h hi0'
      · exact h hj0'
    have hnonab : ¬ ∀ p q : N, p * q = q * p := by
      intro hcomm
      rcases hsome with h1 | h2
      · have huau : u * a * u⁻¹ ∈ N := hNu a haN
        apply h1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hcomm ⟨a, haN⟩ ⟨u * a * u⁻¹, huau⟩)
      · have hwaw : (k⁻¹ * u * k) * a * (k⁻¹ * u * k)⁻¹ ∈ N := hNw a haN
        apply h2
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hcomm ⟨a, haN⟩ ⟨(k⁻¹ * u * k) * a * (k⁻¹ * u * k)⁻¹, hwaw⟩)
    have hcard_dvd : Nat.card N ∣ 13 ^ 3 := by
      have h := Subgroup.card_subgroup_dvd_card (N.subgroupOf S)
      rw [hScard] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv] at h
    obtain ⟨k0, hk0le, hk0eq⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 13)).1 hcard_dvd
    have hcard_eq : Nat.card N = 13 ^ 3 := by
      rcases Nat.lt_or_ge k0 3 with hlt | hge
      · exfalso
        have hcomm : ∀ p q : N, p * q = q * p := by
          interval_cases k0
          · haveI : Subsingleton N := (Nat.card_eq_one_iff_unique.mp (by simpa using hk0eq)).1
            intro p q
            exact Subsingleton.elim _ _
          · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
            haveI : IsCyclic N := isCyclic_of_prime_card (by simpa using hk0eq)
            intro p q
            exact mul_comm' p q
          · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
            intro p q
            exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 13)
              (by simpa using hk0eq)).is_comm.comm p q
        exact hnonab hcomm
      · have hk0 : k0 = 3 := by omega
        rw [hk0eq, hk0]
    have hcardS_le : Nat.card S ≤ Nat.card N := by rw [hScard, hcard_eq]
    have hfin : N = S := Subgroup.eq_of_le_of_card_ge hNS hcardS_le
    exact hfin.trans hSdef

end CFSG.StandardType.SporadicShape
