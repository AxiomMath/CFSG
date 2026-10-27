module

public import CFSG.Sporadic.Recognition.JankoWongSec4Cubes
public import CFSG.Sporadic.Recognition.JankoWongSec4VOne

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

@[expose] def act2 (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 := ![-(w 2), -(w 3), w 0, w 1]

@[expose] def actV (i : ZMod 3) (s t w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  w 0 • ![i, i, 0, 0] + w 1 • ![i, -i, 0, 0] + w 2 • s + w 3 • t

theorem vec4_eq (u : Fin 4 → ZMod 3) : u = ![u 0, u 1, u 2, u 3] := by
  funext j
  fin_cases j <;> rfl

theorem a2_vec (w : Fin 4 → ZMod 3) :
    w 0 • (Pi.single 2 1 : Fin 4 → ZMod 3) + w 1 • (Pi.single 3 1 : Fin 4 → ZMod 3) +
      w 2 • -(Pi.single 0 1 : Fin 4 → ZMod 3) + w 3 • -(Pi.single 1 1 : Fin 4 → ZMod 3) =
      act2 w := by
  revert w
  decide

theorem coord_vec (a b c d : ZMod 3) :
    a • (Pi.single 0 1 : Fin 4 → ZMod 3) + b • (Pi.single 1 1 : Fin 4 → ZMod 3) +
      c • (Pi.single 2 1 : Fin 4 → ZMod 3) + d • (Pi.single 3 1 : Fin 4 → ZMod 3) =
      ![a, b, c, d] := by
  revert a b c d
  decide

theorem c1_vec (x : ZMod 3) : x • (Pi.single 0 1 : Fin 4 → ZMod 3) +
    x • (Pi.single 1 1 : Fin 4 → ZMod 3) = ![x, x, 0, 0] := by
  revert x
  decide

theorem c2_vec (x : ZMod 3) : x • (Pi.single 0 1 : Fin 4 → ZMod 3) +
    (-x) • (Pi.single 1 1 : Fin 4 → ZMod 3) = ![x, -x, 0, 0] := by
  revert x
  decide

theorem neg_single2 : -(Pi.single 2 1 : Fin 4 → ZMod 3) = ![0, 0, -1, 0] := by decide

theorem neg_single3 : -(Pi.single 3 1 : Fin 4 → ZMod 3) = ![0, 0, 0, -1] := by decide

theorem solveY (i s0 s1 s2 s3 t0 t1 t2 t3 : ZMod 3) (hi : i * i = 1)
    (e3 : s2 = -0 * i + -0 * i + i * s0 + i * t0)
    (e4 : s3 = -0 * i + -0 * -i + i * s1 + i * t1)
    (f3 : t2 = -0 * i + -0 * i + i * s0 + -i * t0)
    (f4 : t3 = -0 * i + -0 * -i + i * s1 + -i * t1)
    (g0 : s0 * i + s1 * i + s2 * s0 + s3 * t0 = 0)
    (g1 : s0 * i + s1 * -i + s2 * s1 + s3 * t1 = 0)
    (g2 : s0 * 0 + s1 * 0 + s2 * s2 + s3 * t2 = -1)
    (g3 : s0 * 0 + s1 * 0 + s2 * s3 + s3 * t3 = 0)
    (k0 : t0 * i + t1 * i + t2 * s0 + t3 * t0 = 0)
    (k1 : t0 * i + t1 * -i + t2 * s1 + t3 * t1 = 0)
    (k2 : t0 * 0 + t1 * 0 + t2 * s2 + t3 * t2 = 0)
    (k3 : t0 * 0 + t1 * 0 + t2 * s3 + t3 * t3 = -1) :
    s0 = -1 ∧ s1 = 0 ∧ s2 = -i ∧ s3 = -i ∧ t0 = 0 ∧ t1 = -1 ∧ t2 = -i ∧ t3 = i := by
  subst e3 e4 f3 f4
  revert i s0 s1 t0 t1
  decide

theorem solveY' (i : ZMod 3) (hi : i * i = 1) (s t : Fin 4 → ZMod 3)
    (E1 : s = act2 (actV i s t (act2 ![i, i, 0, 0])))
    (E2 : t = act2 (actV i s t (act2 ![i, -i, 0, 0])))
    (E3 : actV i s t s = ![0, 0, -1, 0])
    (E4 : actV i s t t = ![0, 0, 0, -1]) :
    s = ![-1, 0, -i, -i] ∧ t = ![0, -1, -i, i] := by
  rw [vec4_eq s, vec4_eq t] at E1 E2 E3 E4 ⊢
  have e3 := congrFun E1 2
  have e4 := congrFun E1 3
  have f3 := congrFun E2 2
  have f4 := congrFun E2 3
  have g0 := congrFun E3 0
  have g1 := congrFun E3 1
  have g2 := congrFun E3 2
  have g3 := congrFun E3 3
  have k0 := congrFun E4 0
  have k1 := congrFun E4 1
  have k2 := congrFun E4 2
  have k3 := congrFun E4 3
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := solveY i (s 0) (s 1) (s 2) (s 3) (t 0) (t 1) (t 2)
    (t 3) hi e3 e4 f3 f4 g0 g1 g2 g3 k0 k1 k2 k3
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  exact ⟨rfl, rfl⟩

section Algebra

variable {G : Type*} [Group G]

theorem three_dvd_sub_of_cast_eq {p q : ℤ} (h : (p : ZMod 3) = (q : ZMod 3)) :
    (3 : ℤ) ∣ p - q := by
  exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub q p 3).mp h.symm

theorem heis_rel {A x y : G} (hAy : A * y = y * A) (h19 : y⁻¹ * x * y = x * A⁻¹) {i : ℤ}
    (hi : i = 1 ∨ i = -1) : x * y ^ (-i) = y ^ (-i) * x * A ^ i := by
  have e0 : x * y = y * x * A⁻¹ := by
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * (x * A⁻¹) := by rw [h19]
      _ = y * x * A⁻¹ := by group
  have hAy' : A * y⁻¹ = y⁻¹ * A := (Commute.inv_right (show Commute A y from hAy)).eq
  rcases hi with rfl | rfl
  · have e1 : y * x = x * y * A := by rw [e0]; group
    simp only [zpow_neg_one, zpow_one]
    calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
      _ = y⁻¹ * (x * y * A) * y⁻¹ := by rw [e1]
      _ = y⁻¹ * x * y * (A * y⁻¹) := by group
      _ = y⁻¹ * x * y * (y⁻¹ * A) := by rw [hAy']
      _ = y⁻¹ * x * A := by group
  · simp only [neg_neg, zpow_one, zpow_neg_one]
    exact e0

theorem heis_core {A x y w z m : G} {k i : ℤ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    (hAx : A * x = x * A) (hAy : A * y = y * A) (hAw : A * w = w * A)
    (hxy : x * y = y * x * A ^ i) (hxw : x * w = w * x) (hyw : y * w = w * y)
    (hzA : cj A z = A) (hzx : cj x z = x⁻¹) (hzy : cj y z = y⁻¹) (hzw : cj w z = w⁻¹)
    (hm : m = A ^ k * x⁻¹ * y * w) (hmz : cj m z = m⁻¹) : (3 : ℤ) ∣ k + i := by
  have cA : ∀ (n : ℤ) (g : G), A * g = g * A → A ^ n * g = g * A ^ n :=
    fun n g hg => ((show Commute A g from hg).zpow_left n).eq
  have hAy' : A ^ i * y⁻¹ = y⁻¹ * A ^ i :=
    (((show Commute A y from hAy).zpow_left i).inv_right).eq
  have hwx : w⁻¹ * x = x * w⁻¹ := ((show Commute x w from hxw).inv_right).eq.symm
  have hwy : w⁻¹ * y⁻¹ = y⁻¹ * w⁻¹ := ((show Commute y w from hyw).inv_inv).eq.symm
  have h1 : cj m z = A ^ k * x * y⁻¹ * w⁻¹ := by
    rw [hm, cj_mul_left, cj_mul_left, cj_mul_left, cj_zpow_left, hzA, cj_inv_left, hzx, hzy, hzw,
      inv_inv]
  have h2 : m⁻¹ = w⁻¹ * y⁻¹ * x * A ^ (-k) := by
    rw [hm]
    group
  have h3 : A ^ k * x * y⁻¹ * w⁻¹ = w⁻¹ * y⁻¹ * x * A ^ (-k) := by rw [← h1, hmz, h2]
  have hyx : y⁻¹ * x = x * y⁻¹ * A ^ i := by
    calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * x * A ^ i) * y⁻¹ := by rw [hxy]
      _ = x * (A ^ i * y⁻¹) := by group
      _ = x * (y⁻¹ * A ^ i) := by rw [hAy']
      _ = x * y⁻¹ * A ^ i := by group
  have h4 : w⁻¹ * y⁻¹ * x * A ^ (-k) = x * y⁻¹ * w⁻¹ * A ^ (i - k) := by
    calc w⁻¹ * y⁻¹ * x * A ^ (-k) = w⁻¹ * (y⁻¹ * x) * A ^ (-k) := by group
      _ = w⁻¹ * (x * y⁻¹ * A ^ i) * A ^ (-k) := by rw [hyx]
      _ = (w⁻¹ * x) * y⁻¹ * (A ^ i * A ^ (-k)) := by group
      _ = (x * w⁻¹) * y⁻¹ * (A ^ i * A ^ (-k)) := by rw [hwx]
      _ = x * (w⁻¹ * y⁻¹) * A ^ (i - k) := by group
      _ = x * (y⁻¹ * w⁻¹) * A ^ (i - k) := by rw [hwy]
      _ = x * y⁻¹ * w⁻¹ * A ^ (i - k) := by group
  have hAx' : A ^ k * x = x * A ^ k := cA k x hAx
  have hAy'' : A ^ k * y⁻¹ = y⁻¹ * A ^ k := (((show Commute A y from hAy).zpow_left k).inv_right).eq
  have hAw'' : A ^ k * w⁻¹ = w⁻¹ * A ^ k := (((show Commute A w from hAw).zpow_left k).inv_right).eq
  have h5 : A ^ k * x * y⁻¹ * w⁻¹ = x * y⁻¹ * w⁻¹ * A ^ k := by
    calc A ^ k * x * y⁻¹ * w⁻¹ = (A ^ k * x) * y⁻¹ * w⁻¹ := by group
      _ = (x * A ^ k) * y⁻¹ * w⁻¹ := by rw [hAx']
      _ = x * (A ^ k * y⁻¹) * w⁻¹ := by group
      _ = x * (y⁻¹ * A ^ k) * w⁻¹ := by rw [hAy'']
      _ = x * y⁻¹ * (A ^ k * w⁻¹) := by group
      _ = x * y⁻¹ * (w⁻¹ * A ^ k) := by rw [hAw'']
      _ = x * y⁻¹ * w⁻¹ * A ^ k := by group
  have h6 : A ^ k = A ^ (i - k) := by
    have : x * y⁻¹ * w⁻¹ * A ^ k = x * y⁻¹ * w⁻¹ * A ^ (i - k) := by
      rw [← h5, h3, h4]
    exact mul_left_cancel this
  have h7 : A ^ (k + k) = A ^ i := by
    have e2 : A ^ k * A ^ k = A ^ (i - k) * A ^ k := by rw [← h6]
    rw [zpow_add, e2]
    group
  have h8 : A ^ (k + k - i) = 1 := by rw [zpow_sub, h7, mul_inv_cancel]
  have h9 := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := A) (i := k + k - i)).mpr h8
  rw [orderOf_eq_prime hA3 hA1] at h9
  have h10 : (3 : ℤ) ∣ k + k - i := by exact_mod_cast h9
  omega

end Algebra

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

section NoCerts

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (h : Sec4Hyp c a₁ v v₁)

include h in
theorem Sec4Hyp.v1_mem_Kg : v₁ ∈ c.Kg := by
  have e : v₁⁻¹ * (c.a : G) * v₁ = (c.a : G) := h.rel.sigma1_by_v1
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc v₁ * (c.a : G) = v₁ * (v₁⁻¹ * (c.a : G) * v₁) := by rw [e]
    _ = (c.a : G) * v₁ := by group

include h in
theorem Sec4Hyp.braid : c.a2 a₁ * v₁ = v₁ * c.a2 a₁ * v₁ * c.a2 a₁ := by
  have hcube : (v₁ * c.a2 a₁) ^ 3 = 1 := h.rel.v1_a2_cube
  have hz : S.z * S.z = 1 := Ctx.z_mul_z (S := S)
  rw [pow_three'] at hcube
  have e1 : v₁ * c.a2 a₁ * (v₁ * c.a2 a₁) = (v₁ * c.a2 a₁)⁻¹ := eq_inv_of_mul_eq_one_left hcube
  have e2 : (v₁ * c.a2 a₁)⁻¹ = c.a2 a₁ * v₁ := by
    rw [mul_inv_rev, h.a2_inv, h.v1_inv]
    calc c.a2 a₁ * S.z * (v₁ * S.z) = c.a2 a₁ * (S.z * v₁) * S.z := by group
      _ = c.a2 a₁ * (v₁ * S.z) * S.z := by rw [h.v1_comm_z]
      _ = c.a2 a₁ * v₁ * (S.z * S.z) := by group
      _ = c.a2 a₁ * v₁ := by rw [hz, mul_one]
  rw [e2] at e1
  rw [← e1]
  group

include h in
theorem Sec4Hyp.cj_braid (g : G) :
    cj g (c.a2 a₁ * v₁) = cj (cj (cj (cj g v₁) (c.a2 a₁)) v₁) (c.a2 a₁) := by
  rw [h.braid, cj_mul_right, cj_mul_right, cj_mul_right]

theorem Ctx.cj_mem_MG (c : Ctx S) {g y : G} (hg : g ∈ c.Kg) (hy : y ∈ c.MG) : cj y g ∈ c.MG := by
  have := c.MG_conj (c.Kg.inv_mem hg) hy
  simpa [cj] using this

end NoCerts

section Certs


namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} {W : Subgroup G} (hφ : Phi1 c φ₁)
  (h : Sec4Hyp c a₁ v v₁) (hW : c.IsW W)

include hφ h hW in
theorem cd_cj_of_coords {cd : G → Fin 4 → ZMod 3} (hcd : IsCd c a₁ v φ₁ cd) {g y : G}
    (hg : g ∈ c.Kg) (hy : y ∈ c.MG) {w : Fin 4 → ZMod 3} (hw : cd y = w) :
    cd (cj y g) = w 0 • cd (cj φ₁ g) + w 1 • cd (cj (cj φ₁ v) g) +
      w 2 • cd (cj (phi3 c a₁ φ₁) g) + w 3 • cd (cj (phi4 c a₁ v φ₁) g) := by
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  obtain ⟨k, p₁, p₂, p₃, p₄, hnf⟩ := hφ.normal_form h hW hy
  have hag : cj (c.a : G) g = (c.a : G) :=
    cj_eq_self_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have hcw : cd y = (p₁ : ZMod 3) • (Pi.single 0 1 : Fin 4 → ZMod 3) +
      (p₂ : ZMod 3) • (Pi.single 1 1 : Fin 4 → ZMod 3) +
      (p₃ : ZMod 3) • (Pi.single 2 1 : Fin 4 → ZMod 3) +
      (p₄ : ZMod 3) • (Pi.single 3 1 : Fin 4 → ZMod 3) := by
    rw [hnf, hcd.cd_five hM1 hM2 hM3 hM4, hcd.phi1, hcd.phi2, hcd.phi3, hcd.phi4]
  have hcjy : cj y g = (c.a : G) ^ k * (cj φ₁ g) ^ p₁ * (cj (cj φ₁ v) g) ^ p₂ *
      (cj (phi3 c a₁ φ₁) g) ^ p₃ * (cj (phi4 c a₁ v φ₁) g) ^ p₄ := by
    rw [hnf]
    simp only [cj_mul_left, cj_zpow_left, hag]
  have hwy : w = ![(p₁ : ZMod 3), (p₂ : ZMod 3), (p₃ : ZMod 3), (p₄ : ZMod 3)] := by
    rw [← hw, hcw, coord_vec]
  have w0 : w 0 = (p₁ : ZMod 3) := by rw [hwy]; rfl
  have w1 : w 1 = (p₂ : ZMod 3) := by rw [hwy]; rfl
  have w2 : w 2 = (p₃ : ZMod 3) := by rw [hwy]; rfl
  have w3 : w 3 = (p₄ : ZMod 3) := by rw [hwy]; rfl
  rw [hcjy, hcd.cd_five (c.cj_mem_MG hg hM1) (c.cj_mem_MG hg hM2) (c.cj_mem_MG hg hM3)
    (c.cj_mem_MG hg hM4), w0, w1, w2, w3]

include hφ h hW in
theorem cd_cj_a2 {cd : G → Fin 4 → ZMod 3} (hcd : IsCd c a₁ v φ₁ cd) {y : G} (hy : y ∈ c.MG) :
    cd (cj y (c.a2 a₁)) = act2 (cd y) := by
  have e := hφ.cd_cj_of_coords h hW hcd h.a2_mem_Kg hy rfl
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  rw [hφ.phi3_by_a2 h, hφ.phi4_by_a2 h, hcd.inv hM1, hcd.inv hM2, hcd.phi3, hcd.phi4, hcd.phi1,
    hcd.phi2] at e
  rw [e]
  exact a2_vec (cd y)

include hφ h hW in
theorem cd_cj_v1 {cd : G → Fin 4 → ZMod 3} (hcd : IsCd c a₁ v φ₁ cd) {i : ZMod 3}
    (hX1 : cd (cj φ₁ v₁) = ![i, i, 0, 0]) (hX2 : cd (cj (cj φ₁ v) v₁) = ![i, -i, 0, 0])
    {y : G} (hy : y ∈ c.MG) :
    cd (cj y v₁) = actV i (cd (cj (phi3 c a₁ φ₁) v₁)) (cd (cj (phi4 c a₁ v φ₁) v₁)) (cd y) := by
  rw [hφ.cd_cj_of_coords h hW hcd h.v1_mem_Kg hy rfl, hX1, hX2]
  rfl

include hφ h hW in
theorem exists_cd_v1 {cd : G → Fin 4 → ZMod 3} (hcd : IsCd c a₁ v φ₁ cd) {i : ℤ}
    (hi : i = 1 ∨ i = -1) (hX1 : cj φ₁ v₁ = φ₁ ^ i * (cj φ₁ v) ^ i)
    (hX2 : cj (cj φ₁ v) v₁ = φ₁ ^ i * (cj φ₁ v) ^ (-i)) :
    cd (cj (phi3 c a₁ φ₁) v₁) = ![-1, 0, -(i : ZMod 3), -(i : ZMod 3)] ∧
      cd (cj (phi4 c a₁ v φ₁) v₁) = ![0, -1, -(i : ZMod 3), (i : ZMod 3)] := by
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hKg := h.v1_mem_Kg
  have hii : (i : ZMod 3) * (i : ZMod 3) = 1 := by
    rcases hi with rfl | rfl <;> decide
  have hX1' : cd (cj φ₁ v₁) = ![(i : ZMod 3), (i : ZMod 3), 0, 0] := by
    rw [hX1, hcd.add _ (c.MG.zpow_mem hM1 i) _ (c.MG.zpow_mem hM2 i), hcd.zpow hM1,
      hcd.zpow hM2, hcd.phi1, hcd.phi2]
    exact c1_vec _
  have hX2' : cd (cj (cj φ₁ v) v₁) = ![(i : ZMod 3), -(i : ZMod 3), 0, 0] := by
    rw [hX2, hcd.add _ (c.MG.zpow_mem hM1 i) _ (c.MG.zpow_mem hM2 (-i)), hcd.zpow hM1,
      hcd.zpow hM2, hcd.phi1, hcd.phi2, Int.cast_neg]
    exact c2_vec _
  have hm3 : cj (phi3 c a₁ φ₁) v₁ ∈ c.MG := c.cj_mem_MG hKg hM3
  have hm4 : cj (phi4 c a₁ v φ₁) v₁ ∈ c.MG := c.cj_mem_MG hKg hM4
  obtain ⟨Sv, hS⟩ : ∃ Sv, Sv = cd (cj (phi3 c a₁ φ₁) v₁) := ⟨_, rfl⟩
  obtain ⟨Tv, hT⟩ : ∃ Tv, Tv = cd (cj (phi4 c a₁ v φ₁) v₁) := ⟨_, rfl⟩
  have V : ∀ y ∈ c.MG, cd (cj y v₁) = actV (i : ZMod 3) Sv Tv (cd y) := fun y hy => by
    rw [hS, hT]
    exact hφ.cd_cj_v1 h hW hcd hX1' hX2' hy
  have A : ∀ y ∈ c.MG, cd (cj y (c.a2 a₁)) = act2 (cd y) := fun y hy =>
    hφ.cd_cj_a2 h hW hcd hy
  have hy0 : cj φ₁ v₁ ∈ c.MG := c.cj_mem_MG hKg hM1
  have hy1 : cj (cj φ₁ v₁) (c.a2 a₁) ∈ c.MG := c.cj_mem_MG h.a2_mem_Kg hy0
  have hy2 : cj (cj (cj φ₁ v₁) (c.a2 a₁)) v₁ ∈ c.MG := c.cj_mem_MG hKg hy1
  have hz0 : cj (cj φ₁ v) v₁ ∈ c.MG := c.cj_mem_MG hKg hM2
  have hz1 : cj (cj (cj φ₁ v) v₁) (c.a2 a₁) ∈ c.MG := c.cj_mem_MG h.a2_mem_Kg hz0
  have hz2 : cj (cj (cj (cj φ₁ v) v₁) (c.a2 a₁)) v₁ ∈ c.MG := c.cj_mem_MG hKg hz1
  have m3eq : cj (phi3 c a₁ φ₁) v₁ = cj (cj (cj (cj φ₁ v₁) (c.a2 a₁)) v₁) (c.a2 a₁) := by
    rw [← h.cj_braid φ₁, cj_mul_right]
  have m4eq : cj (phi4 c a₁ v φ₁) v₁ =
      cj (cj (cj (cj (cj φ₁ v) v₁) (c.a2 a₁)) v₁) (c.a2 a₁) := by
    rw [← h.cj_braid (cj φ₁ v), cj_mul_right]
  have E1 : Sv = act2 (actV (i : ZMod 3) Sv Tv (act2 ![(i : ZMod 3), (i : ZMod 3), 0, 0])) := by
    refine hS.trans ?_
    rw [m3eq, A _ hy2, V _ hy1, A _ hy0, hX1']
  have E2 : Tv = act2 (actV (i : ZMod 3) Sv Tv (act2 ![(i : ZMod 3), -(i : ZMod 3), 0, 0])) := by
    refine hT.trans ?_
    rw [m4eq, A _ hz2, V _ hz1, A _ hz0, hX2']
  have hz3 : cj (cj (phi3 c a₁ φ₁) v₁) v₁ = (phi3 c a₁ φ₁)⁻¹ := by
    rw [← cj_mul_right, ← pow_two, h.v1_sq, hφ.phi3_by_z h]
  have hz4 : cj (cj (phi4 c a₁ v φ₁) v₁) v₁ = (phi4 c a₁ v φ₁)⁻¹ := by
    rw [← cj_mul_right, ← pow_two, h.v1_sq, hφ.phi4_by_z h]
  have E3 : actV (i : ZMod 3) Sv Tv Sv = ![0, 0, -1, 0] := by
    have h1 : cd (cj (cj (phi3 c a₁ φ₁) v₁) v₁) = actV (i : ZMod 3) Sv Tv Sv := by
      rw [V _ hm3, ← hS]
    rw [← h1, hz3, hcd.inv hM3, hcd.phi3]
    exact neg_single2
  have E4 : actV (i : ZMod 3) Sv Tv Tv = ![0, 0, 0, -1] := by
    have h1 : cd (cj (cj (phi4 c a₁ v φ₁) v₁) v₁) = actV (i : ZMod 3) Sv Tv Tv := by
      rw [V _ hm4, ← hT]
    rw [← h1, hz4, hcd.inv hM4, hcd.phi4]
    exact neg_single3
  obtain ⟨hs, ht⟩ := solveY' (i : ZMod 3) hii Sv Tv E1 E2 E3 E4
  rw [hS] at hs
  rw [hT] at ht
  exact ⟨hs, ht⟩

include hφ h hW in
theorem phi3_by_v1 {i : ℤ} (hi : i = 1 ∨ i = -1) (hX1 : cj φ₁ v₁ = φ₁ ^ i * (cj φ₁ v) ^ i)
    (hX2 : cj (cj φ₁ v) v₁ = φ₁ ^ i * (cj φ₁ v) ^ (-i))
    (h19 : cj φ₁ (phi3 c a₁ φ₁) = φ₁ * (c.a : G)⁻¹) :
    cj (phi3 c a₁ φ₁) v₁ = (c.a : G) ^ (-i) * φ₁⁻¹ * phi3 c a₁ φ₁ ^ (-i) *
      phi4 c a₁ v φ₁ ^ (-i) := by
  obtain ⟨cd, hcd⟩ := hφ.exists_cd h hW
  obtain ⟨hs, -⟩ := hφ.exists_cd_v1 h hW hcd hi hX1 hX2
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hm3 : cj (phi3 c a₁ φ₁) v₁ ∈ c.MG := c.cj_mem_MG h.v1_mem_Kg hM3
  obtain ⟨k, p₁, p₂, p₃, p₄, hnf⟩ := hφ.normal_form h hW hm3
  have hcw : cd (cj (phi3 c a₁ φ₁) v₁) = ![(p₁ : ZMod 3), (p₂ : ZMod 3), (p₃ : ZMod 3),
      (p₄ : ZMod 3)] := by
    rw [hnf, hcd.cd_five hM1 hM2 hM3 hM4, hcd.phi1, hcd.phi2, hcd.phi3, hcd.phi4, coord_vec]
  have hq := hcw.symm.trans hs
  have q1 : (p₁ : ZMod 3) = -1 := congrFun hq 0
  have q2 : (p₂ : ZMod 3) = 0 := congrFun hq 1
  have q3 : (p₃ : ZMod 3) = -(i : ZMod 3) := congrFun hq 2
  have q4 : (p₄ : ZMod 3) = -(i : ZMod 3) := congrFun hq 3
  have d1 : (3 : ℤ) ∣ p₁ - (-1) := three_dvd_sub_of_cast_eq (by rw [q1]; decide)
  have d2 : (3 : ℤ) ∣ p₂ - 0 := three_dvd_sub_of_cast_eq (by rw [q2]; simp)
  have d3 : (3 : ℤ) ∣ p₃ - (-i) := three_dvd_sub_of_cast_eq (by rw [q3, Int.cast_neg]; rfl)
  have d4 : (3 : ℤ) ∣ p₄ - (-i) := three_dvd_sub_of_cast_eq (by rw [q4, Int.cast_neg]; rfl)
  have hm : cj (phi3 c a₁ φ₁) v₁ = (c.a : G) ^ k * φ₁⁻¹ * phi3 c a₁ φ₁ ^ (-i) *
      phi4 c a₁ v φ₁ ^ (-i) := by
    rw [hnf, zpow_eq_of_cube hφ.cube d1, zpow_eq_of_cube (hφ.phi2_cube h) d2,
      zpow_eq_of_cube hφ.phi3_cube d3, zpow_eq_of_cube (hφ.phi4_cube h) d4, zpow_neg_one,
      zpow_zero, mul_one]
  have hAx : (c.a : G) * φ₁ = φ₁ * (c.a : G) := Ctx.a_comm_MG hM1
  have hAy : (c.a : G) * phi3 c a₁ φ₁ ^ (-i) = phi3 c a₁ φ₁ ^ (-i) * (c.a : G) :=
    ((show Commute (c.a : G) (phi3 c a₁ φ₁) from Ctx.a_comm_MG hM3).zpow_right (-i)).eq
  have hAw : (c.a : G) * phi4 c a₁ v φ₁ ^ (-i) = phi4 c a₁ v φ₁ ^ (-i) * (c.a : G) :=
    ((show Commute (c.a : G) (phi4 c a₁ v φ₁) from Ctx.a_comm_MG hM4).zpow_right (-i)).eq
  have hc14 : φ₁ * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * φ₁ :=
    cmt_eq_one_iff'.mp (hφ.cmt14_eq_one h hW).1
  have hxw : φ₁ * phi4 c a₁ v φ₁ ^ (-i) = phi4 c a₁ v φ₁ ^ (-i) * φ₁ :=
    ((show Commute φ₁ (phi4 c a₁ v φ₁) from hc14).zpow_right (-i)).eq
  have hyw : phi3 c a₁ φ₁ ^ (-i) * phi4 c a₁ v φ₁ ^ (-i) =
      phi4 c a₁ v φ₁ ^ (-i) * phi3 c a₁ φ₁ ^ (-i) :=
    ((show Commute (phi3 c a₁ φ₁) (phi4 c a₁ v φ₁) from hφ.phi34_comm h).zpow_zpow (-i) (-i)).eq
  have hxy : φ₁ * phi3 c a₁ φ₁ ^ (-i) = phi3 c a₁ φ₁ ^ (-i) * φ₁ * (c.a : G) ^ i :=
    heis_rel (Ctx.a_comm_MG hM3) h19 hi
  have hdvd := heis_core c.aG_cube c.aG_ne_one hAx hAy hAw hxy hxw hyw
    (cj_eq_self_of_comm (Ctx.zc c.a.2)) hφ.by_z
    (by rw [cj_zpow_left, hφ.phi3_by_z h, inv_zpow])
    (by rw [cj_zpow_left, hφ.phi4_by_z h, inv_zpow])
    hm (by rw [cj_cj, h.v1_comm_z, cj_mul_right, hφ.phi3_by_z h, cj_inv_left])
  have hak : (c.a : G) ^ k = (c.a : G) ^ (-i) := zpow_eq_of_cube c.aG_cube (by omega)
  rw [hm, hak]

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
