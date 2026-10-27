module

public import CFSG.Sporadic.Recognition.JankoWongSec4Cubes

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

omit [Finite G] in
theorem zpow_eq_self_of_cube {x : G} (hx : x ^ 3 = 1) {p : ℤ} (hp : 3 ∣ p - 1) : x ^ p = x := by
  have h1 : x ^ (p - 1) = 1 := zpow_eq_one_of_cube hx hp
  rw [zpow_sub_one] at h1
  exact mul_inv_eq_one.mp h1

omit [Finite G] in
theorem exists_cj_proj_hom {N : Subgroup G} (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {z : G}
    (hz : ∀ x ∈ N, cj x z ∈ N) :
    ∃ π : ↥N →* G, ∀ y : ↥N, π y = cj (y : G) z * (y : G)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun y : ↥N => cj (y : G) z * (y : G)⁻¹) ?_, fun y => rfl⟩
  intro y₁ y₂
  have hc : cj (y₂ : G) z * (y₂ : G)⁻¹ * (y₁ : G)⁻¹ =
      (y₁ : G)⁻¹ * (cj (y₂ : G) z * (y₂ : G)⁻¹) :=
    hN _ (N.mul_mem (hz _ y₂.2) (N.inv_mem y₂.2)) _ (N.inv_mem y₁.2)
  calc cj ((y₁ * y₂ : ↥N) : G) z * ((y₁ * y₂ : ↥N) : G)⁻¹
      = cj (y₁ : G) z * (cj (y₂ : G) z * (y₂ : G)⁻¹ * (y₁ : G)⁻¹) := by
        simp only [Subgroup.coe_mul, cj_mul_left, mul_inv_rev]
        group
    _ = cj (y₁ : G) z * ((y₁ : G)⁻¹ * (cj (y₂ : G) z * (y₂ : G)⁻¹)) := by rw [hc]
    _ = (cj (y₁ : G) z * (y₁ : G)⁻¹) * (cj (y₂ : G) z * (y₂ : G)⁻¹) := by group

omit [Finite G] in
theorem three_dvd_add_one_of_relation {N : Subgroup G} (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    {z a b φ : G} (hz : ∀ x ∈ N, cj x z ∈ N) (ha : a ∈ N) (hb : b ∈ N) (hφ : φ ∈ N)
    (haz : cj a z = a) (hbz : cj b z = b) (hφz : cj φ z = φ⁻¹) (hφ3 : orderOf φ = 3) {k : ℤ}
    (e : a * ((φ * a ^ k)⁻¹ * (b * (φ * a ^ (-k))) ^ (-k)) = b) : 3 ∣ k + 1 := by
  obtain ⟨π, hπ⟩ := exists_cj_proj_hom hN hz
  have πa : π ⟨a, ha⟩ = 1 := by
    rw [hπ]
    show cj a z * a⁻¹ = 1
    rw [haz, mul_inv_cancel]
  have πb : π ⟨b, hb⟩ = 1 := by
    rw [hπ]
    show cj b z * b⁻¹ = 1
    rw [hbz, mul_inv_cancel]
  have πφ : π ⟨φ, hφ⟩ = φ ^ (-2 : ℤ) := by
    rw [hπ]
    show cj φ z * φ⁻¹ = _
    rw [hφz]
    group
  have eN : (⟨a, ha⟩ : ↥N) * ((⟨φ, hφ⟩ * ⟨a, ha⟩ ^ k)⁻¹ *
      (⟨b, hb⟩ * (⟨φ, hφ⟩ * ⟨a, ha⟩ ^ (-k))) ^ (-k)) = ⟨b, hb⟩ := Subtype.ext e
  have h1 := congrArg π eN
  simp only [map_mul, map_inv, map_zpow, πa, πb, πφ, one_zpow, mul_one, one_mul] at h1
  have h2 : φ ^ ((-2 : ℤ) * (-1 - k)) = 1 := by
    rw [zpow_mul, sub_eq_add_neg, zpow_add, zpow_neg_one]
    exact h1
  have h3 := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := φ) (i := (-2 : ℤ) * (-1 - k))).mpr h2
  rw [hφ3] at h3
  have h4 : (3 : ℤ) ∣ (-2 : ℤ) * (-1 - k) := by exact_mod_cast h3
  omega

omit [Finite G] in
theorem x_cube_relation {t z φ₃ a b φ : G} {k : ℤ} (hx : (t * z * φ₃) ^ 3 = 1)
    (hat : cj a t = b) (hbt : cj b t = a) (haz : cj a z = a) (hbz : cj b z = b)
    (haφ : cj a φ₃ = a) (hφt : cj φ t = φ) (hφz : cj φ z = φ⁻¹)
    (h19 : cj φ φ₃ = φ * a ^ k) (h19b : cj b φ₃ = b * (φ * a ^ (-k))) :
    a * ((φ * a ^ k)⁻¹ * (b * (φ * a ^ (-k))) ^ (-k)) = b := by
  have s1 : cj b (t * z * φ₃) = a := by
    rw [cj_mul_right, cj_mul_right, hbt, haz, haφ]
  have s2 : cj a (t * z * φ₃) = b * (φ * a ^ (-k)) := by
    rw [cj_mul_right, cj_mul_right, hat, hbz, h19b]
  have s3t : cj (b * (φ * a ^ (-k))) t = a * (φ * b ^ (-k)) := by
    rw [cj_mul_left, cj_mul_left, cj_zpow_left, hbt, hφt, hat]
  have s3z : cj (a * (φ * b ^ (-k))) z = a * (φ⁻¹ * b ^ (-k)) := by
    rw [cj_mul_left, cj_mul_left, cj_zpow_left, haz, hφz, hbz]
  have s3φ : cj (a * (φ⁻¹ * b ^ (-k))) φ₃ =
      a * ((φ * a ^ k)⁻¹ * (b * (φ * a ^ (-k))) ^ (-k)) := by
    rw [cj_mul_left, cj_mul_left, cj_zpow_left, cj_inv_left, haφ, h19, h19b]
  have s3 : cj (b * (φ * a ^ (-k))) (t * z * φ₃) =
      a * ((φ * a ^ k)⁻¹ * (b * (φ * a ^ (-k))) ^ (-k)) := by
    rw [cj_mul_right, cj_mul_right, s3t, s3z, s3φ]
  have h3 : cj (cj (cj b (t * z * φ₃)) (t * z * φ₃)) (t * z * φ₃) = b := by
    rw [← cj_mul_right, ← cj_mul_right, ← pow_three, hx, cj_one_right]
  rwa [s1, s2, s3] at h3

section Certs


namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} {W : Subgroup G} (hφ : Phi1 c φ₁)
  (h : Sec4Hyp c a₁ v v₁) (hW : c.IsW W)

include hφ h hW in
theorem rel_7_8 : cj (phi3 c a₁ φ₁) (c.b : G) = φ₁⁻¹ * phi3 c a₁ φ₁ * (c.a : G) ∧
    cj φ₁ (phi3 c a₁ φ₁) = φ₁ * (c.a : G)⁻¹ := by
  obtain ⟨k, h18, h19, h19b⟩ := hφ.exists_k h hW
  have hM3 := hφ.phi3_mem_MG h
  have haN : (c.a : G) ∈ c.OG := c.aG_mem_OG
  have hbN : (c.b : G) ∈ c.OG := c.PG_le_OG c.card_OG_eq_81 c.bG_mem_PG
  have haz : cj (c.a : G) S.z = (c.a : G) := cj_eq_self_of_comm (Ctx.zc c.a.2)
  have hbz : cj (c.b : G) S.z = (c.b : G) := cj_eq_self_of_comm (Ctx.zc c.b.2)
  have haφ : cj (c.a : G) (phi3 c a₁ φ₁) = (c.a : G) :=
    cj_eq_self_of_comm (Ctx.a_comm_MG hM3)
  have e := x_cube_relation (hφ.u_z_phi3_cube h hW) c.cj_a_t c.cj_b_t haz hbz haφ hφ.by_t
    hφ.by_z h19 h19b
  have hk : 3 ∣ k + 1 :=
    three_dvd_add_one_of_relation c.OG_comm (fun x hx => c.cj_mem_OG_of_mem_NG' c.z_mem_NG hx)
      haN hbN hφ.mem haz hbz hφ.by_z hφ.orderOf_eq e
  have hak : (c.a : G) ^ k = (c.a : G)⁻¹ := zpow_eq_inv_of_cube c.aG_cube hk
  have hak' : (c.a : G) ^ (-k) = (c.a : G) := zpow_eq_self_of_cube c.aG_cube (by omega)
  rw [hak'] at h18
  rw [hak] at h19
  exact ⟨h18, h19⟩

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
