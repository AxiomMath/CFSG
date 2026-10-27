module

public import CFSG.Sporadic.Recognition.JankoWongSec4Elements
public import CFSG.Sporadic.Recognition.JankoWongSec4Eigen

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

namespace Ctx

variable (c : Ctx S)

theorem cj_mem_OG_of_mem_NG {g y : G} (hg : g ∈ c.NG) (hy : y ∈ c.OG) : cj y g⁻¹ ∈ c.OG := by
  have := c.conj_mem_OG_of_mem_NG hg hy
  simpa [cj] using this

theorem cj_mem_OG_of_mem_NG' {g y : G} (hg : g ∈ c.NG) (hy : y ∈ c.OG) : cj y g ∈ c.OG := by
  have := c.conj_mem_OG_of_mem_NG (c.NG.inv_mem hg) hy
  simpa [cj] using this

theorem z_conj_eq {y : G} (hy : y ∈ S.H) : S.z * y * S.z⁻¹ = y := by
  have h1 : y * S.z = S.z * y := Ctx.zc hy
  calc S.z * y * S.z⁻¹ = (y * S.z) * S.z⁻¹ := by rw [h1]
    _ = y := by group

theorem conj_swap_of_sq {g x : G} (hg : g ∈ S.H) (hg2 : g ^ 2 = S.z) (hx : x ∈ S.H) :
    g * x * g⁻¹ = g⁻¹ * x * g := by
  have h1 : g * g = S.z := by rwa [← pow_two]
  have hy : g⁻¹ * x * g ∈ S.H := S.H.mul_mem (S.H.mul_mem (S.H.inv_mem hg) hx) hg
  calc g * x * g⁻¹ = (g * g) * (g⁻¹ * x * g) * (g * g)⁻¹ := by group
    _ = S.z * (g⁻¹ * x * g) * S.z⁻¹ := by rw [h1]
    _ = g⁻¹ * x * g := z_conj_eq hy

theorem bG_mem_PG : (c.b : G) ∈ c.PG := ⟨c.b, c.hbP, rfl⟩

end Ctx

structure Phi1 (c : Ctx S) (φ₁ : G) : Prop where
  mem : φ₁ ∈ c.OG
  ne_one : φ₁ ≠ 1
  by_z : cj φ₁ S.z = φ₁⁻¹
  by_t : cj φ₁ (c.t : G) = φ₁

theorem Sec4Hyp.v_mul_t {c : Ctx S} {a₁ v v₁ : G} (h : Sec4Hyp c a₁ v v₁) :
    v * (c.t : G) = (c.t : G) * v⁻¹ := by
  calc v * (c.t : G) = (c.t : G) * ((c.t : G)⁻¹ * v * (c.t : G)) := by group
    _ = (c.t : G) * v⁻¹ := by rw [h.rel.v_by_u]

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)

include hφ in
theorem phi2_ne_one : cj φ₁ v ≠ 1 := fun e =>
  hφ.ne_one (cj_injective_left v (by show cj φ₁ v = cj 1 v; rw [e, cj_one_left]))

include hφ h in
theorem phi2_by_z : cj (cj φ₁ v) S.z = (cj φ₁ v)⁻¹ := by
  rw [cj_cj, h.v_comm_z, cj_mul_right, hφ.by_z, cj_inv_left]

include hφ h in
theorem phi2_by_v : cj (cj φ₁ v) v = φ₁⁻¹ := by
  rw [cj_cj, ← pow_two, h.v_sq, hφ.by_z]

include hφ h in
theorem phi2_by_t : cj (cj φ₁ v) (c.t : G) = (cj φ₁ v)⁻¹ := by
  rw [cj_cj, h.v_mul_t, cj_mul_right, hφ.by_t, h.v_inv, cj_mul_right, hφ.phi2_by_z h]

end Phi1

section Certs


namespace Sec4Hyp

variable {c : Ctx S} {a₁ v v₁ : G} (h : Sec4Hyp c a₁ v v₁)
include h

theorem v_mem_NG : v ∈ c.NG := by
  have hva : v⁻¹ * (c.a : G) * v = (c.a : G)⁻¹ := h.rel.sigma1_by_v
  have hvb : v⁻¹ * (c.b : G) * v = (c.b : G)⁻¹ := by
    have := h.rel.sigma2_by_v
    rwa [show (c.t : G)⁻¹ * (c.a : G) * (c.t : G) = (c.b : G) from c.cj_a_t] at this
  have hsw : ∀ x ∈ S.H, v * x * v⁻¹ = v⁻¹ * x * v := fun x hx =>
    Ctx.conj_swap_of_sq h.v_mem h.v_sq hx
  have ha1 : v * (c.a : G) * v⁻¹ = (c.a : G)⁻¹ := by rw [hsw _ c.a.2, hva]
  have hb1 : v * (c.b : G) * v⁻¹ = (c.b : G)⁻¹ := by rw [hsw _ c.b.2, hvb]
  have hvn : v ∈ normalizer (c.PG : Set G) := c.mem_normalizer_PG_of_gens
    (by rw [ha1]; exact c.PG.inv_mem c.a_mem_PG) (by rw [hb1]; exact c.PG.inv_mem c.bG_mem_PG)
    (by rw [hva]; exact c.PG.inv_mem c.a_mem_PG) (by rw [hvb]; exact c.PG.inv_mem c.bG_mem_PG)
  exact c.NH_le_NG ⟨hvn, h.v_mem⟩

theorem v1_mem_NG : v₁ ∈ c.NG := by
  have hva : v₁⁻¹ * (c.a : G) * v₁ = (c.a : G) := h.rel.sigma1_by_v1
  have hvb : v₁⁻¹ * (c.b : G) * v₁ = (c.b : G)⁻¹ := by
    have := h.rel.sigma2_by_v1
    rwa [show (c.t : G)⁻¹ * (c.a : G) * (c.t : G) = (c.b : G) from c.cj_a_t] at this
  have hsw : ∀ x ∈ S.H, v₁ * x * v₁⁻¹ = v₁⁻¹ * x * v₁ := fun x hx =>
    Ctx.conj_swap_of_sq h.v1_mem h.v1_sq hx
  have ha1 : v₁ * (c.a : G) * v₁⁻¹ = (c.a : G) := by rw [hsw _ c.a.2, hva]
  have hb1 : v₁ * (c.b : G) * v₁⁻¹ = (c.b : G)⁻¹ := by rw [hsw _ c.b.2, hvb]
  have hvn : v₁ ∈ normalizer (c.PG : Set G) := c.mem_normalizer_PG_of_gens
    (by rw [ha1]; exact c.a_mem_PG) (by rw [hb1]; exact c.PG.inv_mem c.bG_mem_PG)
    (by rw [hva]; exact c.a_mem_PG) (by rw [hvb]; exact c.PG.inv_mem c.bG_mem_PG)
  exact c.NH_le_NG ⟨hvn, h.v1_mem⟩

end Sec4Hyp

namespace Ctx

variable (c : Ctx S)

theorem exists_phi₁ :
    ∃ φ₁ : G, φ₁ ∈ c.OG ∧ φ₁ ≠ 1 ∧ cj φ₁ S.z = φ₁⁻¹ ∧ cj φ₁ (c.t : G) = φ₁ := by
  have h81 := c.card_OG_eq_81
  have hN := c.OG_comm
  have hz2 : S.z ^ 2 = 1 := z_sq (S := S)
  set X : Subgroup G := c.CO (c.t : G) with hX
  have hXN : X ≤ c.OG := inf_le_left
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => hN x (hXN hx) y (hXN hy)
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := fun x hx => c.OG_pow_three x (hXN hx)
  have hXt : ∀ x ∈ X, x * (c.t : G) = (c.t : G) * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hzX : ∀ x ∈ X, S.z * x * S.z⁻¹ ∈ X := by
    intro x hx
    refine ⟨c.conj_mem_OG_of_mem_NG c.z_mem_NG (hXN hx),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hzt : Commute S.z (c.t : G) := c.t_comm_z.symm
    have hxt : Commute x (c.t : G) := hXt x hx
    exact ((hzt.mul_left hxt).mul_left hzt.inv_left).eq
  have hcard := card_eq X S.z hXc hX3 hz2 hzX
  have hX9 : Nat.card X = 9 := (c.card_CO_z_t h81).2
  have hPt : Nat.card ↥(X ⊓ centralizer ({S.z} : Set G)) = 3 := by
    have heq : X ⊓ centralizer ({S.z} : Set G) = c.PG ⊓ centralizer ({(c.t : G)} : Set G) := by
      have h1 := c.CO_z_eq_PG h81
      calc X ⊓ centralizer ({S.z} : Set G)
          = (c.OG ⊓ centralizer ({S.z} : Set G)) ⊓ centralizer ({(c.t : G)} : Set G) :=
            inf_right_comm _ _ _
        _ = c.CO S.z ⊓ centralizer ({(c.t : G)} : Set G) := rfl
        _ = c.PG ⊓ centralizer ({(c.t : G)} : Set G) := by rw [h1]
    rw [heq]
    have hle : c.PG ⊓ centralizer ({(c.t : G)} : Set G) ≤ c.PG := inf_le_left
    have hdvd : Nat.card ↥(c.PG ⊓ centralizer ({(c.t : G)} : Set G)) ∣ 9 := by
      rw [← c.card_PG]; exact Subgroup.card_dvd_of_le hle
    have hsmem : c.s ∈ c.PG ⊓ centralizer ({(c.t : G)} : Set G) :=
      ⟨c.s_mem_PG, Subgroup.mem_centralizer_singleton_iff.mpr c.t_comm_s.symm⟩
    have hne1 : Nat.card ↥(c.PG ⊓ centralizer ({(c.t : G)} : Set G)) ≠ 1 := by
      intro h1
      have hbot := Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at hsmem
      exact c.s_ne_one hsmem
    have hne9 : Nat.card ↥(c.PG ⊓ centralizer ({(c.t : G)} : Set G)) ≠ 9 := by
      intro h9
      have heq' := Subgroup.eq_of_le_of_card_ge hle (by rw [h9, c.card_PG])
      have ha : (c.a : G) ∈ c.PG ⊓ centralizer ({(c.t : G)} : Set G) := by
        rw [heq']; exact c.a_mem_PG
      exact c.t_not_comm_a (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
    have h39 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h39] at hdvd
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i <;> simp_all
  have hneg : Nat.card ↥(negSub X S.z hXc) = 3 := by
    rw [hX9, hPt] at hcard; omega
  have hnb : negSub X S.z hXc ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hneg]; norm_num
  obtain ⟨⟨φ₁, hφ₁⟩, hφ₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnb
  have hφ₁1' : φ₁ ≠ 1 := fun e => hφ₁1 (Subtype.ext e)
  obtain ⟨hφX, hφz⟩ := hφ₁
  refine ⟨φ₁, hXN hφX, hφ₁1', ?_, cj_eq_self_of_comm (hXt φ₁ hφX)⟩
  rw [Ctx.zG_inv (S := S)] at hφz
  rw [cj, Ctx.zG_inv (S := S)]
  exact hφz

end Ctx

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)

include hφ in
theorem cube : φ₁ ^ 3 = 1 := c.OG_pow_three φ₁ hφ.mem

include hφ in
theorem orderOf_eq : orderOf φ₁ = 3 := orderOf_eq_prime hφ.cube hφ.ne_one

include hφ h in
theorem phi2_mem : cj φ₁ v ∈ c.OG := c.cj_mem_OG_of_mem_NG' h.v_mem_NG hφ.mem

include hφ h in
theorem phi2_cube : (cj φ₁ v) ^ 3 = 1 := c.OG_pow_three _ (hφ.phi2_mem h)

include hφ h in
theorem phi2_orderOf : orderOf (cj φ₁ v) = 3 :=
  orderOf_eq_prime (hφ.phi2_cube h) (hφ.phi2_ne_one)

include hφ h in
theorem indep12 (i j : ℤ) (e : φ₁ ^ i * (cj φ₁ v) ^ j = 1) : 3 ∣ i ∧ 3 ∣ j := by
  have e2 : φ₁ ^ i * ((cj φ₁ v)⁻¹) ^ j = 1 := by
    have := congrArg (fun x => cj x (c.t : G)) e
    simpa [cj_mul_left, cj_zpow_left, hφ.by_t, hφ.phi2_by_t h] using this
  have e1' : (cj φ₁ v) ^ j = (φ₁ ^ i)⁻¹ := eq_inv_of_mul_eq_one_right e
  have e2' : ((cj φ₁ v)⁻¹) ^ j = (φ₁ ^ i)⁻¹ := eq_inv_of_mul_eq_one_right e2
  have e3 : (cj φ₁ v) ^ (2 * j) = 1 := by
    have : (cj φ₁ v) ^ (2 * j) = (cj φ₁ v) ^ j * (cj φ₁ v) ^ j := by rw [two_mul, zpow_add]
    rw [this]
    nth_rewrite 2 [e1']
    rw [← e2', inv_zpow', zpow_neg, mul_inv_cancel]
  have h3 : (3 : ℤ) ∣ 2 * j := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := cj φ₁ v) (i := 2 * j)).mpr e3
    rw [hφ.phi2_orderOf h] at this
    exact_mod_cast this
  have hj : (3 : ℤ) ∣ j := by omega
  have hj1 : (cj φ₁ v) ^ j = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := cj φ₁ v) (i := j)).mp
      (by rw [hφ.phi2_orderOf h]; exact_mod_cast hj)
    exact this
  have hi1 : φ₁ ^ i = 1 := by
    rw [hj1, mul_one] at e; exact e
  have hi : (3 : ℤ) ∣ i := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := φ₁) (i := i)).mpr hi1
    rw [hφ.orderOf_eq] at this
    exact_mod_cast this
  exact ⟨hi, hj⟩

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
