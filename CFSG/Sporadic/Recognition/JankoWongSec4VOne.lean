module

public import CFSG.Sporadic.Recognition.JankoWongSec4Struct

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem zmod3_relation_solve : ∀ a b c d : ZMod 3, a * a + c * (-b) = 0 →
    -(b * a + d * (-b)) = 1 → a * c + c * (-d) = -1 → -(b * c + d * (-d)) = 0 →
    b = a ∧ c = a ∧ d = -a ∧ (a = 1 ∨ a = -1) := by
  decide

section Generic

variable {G : Type*} [Group G]

theorem zpow_pair_mul {x y : G} (hxy : x * y = y * x) (p q p' q' : ℤ) :
    (x ^ p * y ^ q) * (x ^ p' * y ^ q') = x ^ (p + p') * y ^ (q + q') := by
  have hc : y ^ q * x ^ p' = x ^ p' * y ^ q :=
    ((show Commute x y from hxy).zpow_zpow p' q).eq.symm
  calc x ^ p * y ^ q * (x ^ p' * y ^ q') = x ^ p * (y ^ q * x ^ p') * y ^ q' := by
        simp only [mul_assoc]
    _ = x ^ p * (x ^ p' * y ^ q) * y ^ q' := by rw [hc]
    _ = x ^ p * x ^ p' * (y ^ q * y ^ q') := by simp only [mul_assoc]
    _ = x ^ (p + p') * y ^ (q + q') := by rw [← zpow_add, ← zpow_add]

theorem zpow_pair_zpow {x y : G} (hxy : x * y = y * x) (p q n : ℤ) :
    (x ^ p * y ^ q) ^ n = x ^ (p * n) * y ^ (q * n) := by
  rw [((show Commute x y from hxy).zpow_zpow p q).mul_zpow, ← zpow_mul, ← zpow_mul]

theorem zpow_pair_eq {x y : G} (hxy : x * y = y * x)
    (hind : ∀ i j : ℤ, x ^ i * y ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) {p q p' q' : ℤ}
    (e : x ^ p * y ^ q = x ^ p' * y ^ q') : 3 ∣ p - p' ∧ 3 ∣ q - q' := by
  have h1 : x ^ (p + -p') * y ^ (q + -q') = 1 := by
    rw [← zpow_pair_mul hxy, e, zpow_pair_mul hxy]
    simp
  simpa only [← sub_eq_add_neg] using hind _ _ h1

theorem zpow_pair_eq_zmod {x y : G} (hxy : x * y = y * x)
    (hind : ∀ i j : ℤ, x ^ i * y ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) {p q p' q' : ℤ}
    (e : x ^ p * y ^ q = x ^ p' * y ^ q') : (p : ZMod 3) = p' ∧ (q : ZMod 3) = q' := by
  obtain ⟨h1, h2⟩ := zpow_pair_eq hxy hind e
  exact ⟨((ZMod.intCast_eq_intCast_iff_dvd_sub p' p 3).mpr (by exact_mod_cast h1)).symm,
    ((ZMod.intCast_eq_intCast_iff_dvd_sub q' q 3).mpr (by exact_mod_cast h2)).symm⟩

theorem zpow_eq_of_cube {x : G} (hx : x ^ 3 = 1) {p p' : ℤ} (hp : 3 ∣ p - p') :
    x ^ p = x ^ p' := by
  obtain ⟨m, hm⟩ := hp
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  have e : p = p' + 3 * m := by omega
  rw [e, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem zpow_pair_congr {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) {p q p' q' : ℤ}
    (hp : 3 ∣ p - p') (hq : 3 ∣ q - q') : x ^ p * y ^ q = x ^ p' * y ^ q' := by
  rw [zpow_eq_of_cube hx3 hp, zpow_eq_of_cube hy3 hq]

theorem exists_zpow_pair_of_card_nine {Q : Subgroup G} {x y : G} (hxy : x * y = y * x)
    (hx : x ∈ Q) (hy : y ∈ Q) (hcard : Nat.card Q = 9)
    (hind : ∀ i j : ℤ, x ^ i * y ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    ∀ w ∈ Q, ∃ p q : ℤ, w = x ^ p * y ^ q := by
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have hf : Function.Injective (fun pq : Fin 3 × Fin 3 =>
      (⟨x ^ (pq.1 : ℕ) * y ^ (pq.2 : ℕ), Q.mul_mem (Q.pow_mem hx _) (Q.pow_mem hy _)⟩ : Q)) := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ e
    have e1 := congrArg Subtype.val e
    simp only [← zpow_natCast] at e1
    obtain ⟨h1, h2⟩ := zpow_pair_eq hxy hind e1
    have hp := p.isLt
    have hq := q.isLt
    have hp' := p'.isLt
    have hq' := q'.isLt
    have hp2 : (p : ℕ) = p' := by omega
    have hq2 : (q : ℕ) = q' := by omega
    exact Prod.ext (Fin.ext hp2) (Fin.ext hq2)
  have hbij := hf.bijective_of_nat_card_le (by simp [hcard])
  intro w hw
  obtain ⟨⟨p, q⟩, hpq⟩ := hbij.2 ⟨w, hw⟩
  refine ⟨(p : ℕ), (q : ℕ), ?_⟩
  have e1 := congrArg Subtype.val hpq
  simp only [zpow_natCast] at e1 ⊢
  exact e1.symm

theorem exists_action_of_relation {x y u v v₁ : G} (hxy : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hind : ∀ i j : ℤ, x ^ i * y ^ j = 1 → 3 ∣ i ∧ 3 ∣ j)
    (hux : cj x u = x) (huy : cj y u = y⁻¹) (hvx : cj x v = y) (hvy : cj y v = x⁻¹)
    (hrel : (v₁ * u) ^ 2 = v) {p₁ q₁ p₂ q₂ : ℤ}
    (h1 : cj x v₁ = x ^ p₁ * y ^ q₁) (h2 : cj y v₁ = x ^ p₂ * y ^ q₂) :
    ∃ i : ℤ, (i = 1 ∨ i = -1) ∧ cj x v₁ = x ^ i * y ^ i ∧ cj y v₁ = x ^ i * y ^ (-i) := by
  have hu : ∀ p q : ℤ, cj (x ^ p * y ^ q) u = x ^ p * y ^ (-q) := by
    intro p q
    rw [cj_mul_left, cj_zpow_left, cj_zpow_left, hux, huy, inv_zpow']
  have hv : ∀ p q : ℤ, cj (x ^ p * y ^ q) v₁ =
      x ^ (p₁ * p + p₂ * q) * y ^ (q₁ * p + q₂ * q) := by
    intro p q
    rw [cj_mul_left, cj_zpow_left, cj_zpow_left, h1, h2, zpow_pair_zpow hxy,
      zpow_pair_zpow hxy, zpow_pair_mul hxy]
  have hrel' : ∀ g : G, cj (cj (cj (cj g v₁) u) v₁) u = cj g v := by
    intro g
    rw [← hrel]
    simp only [pow_two, cj_mul_right]
  have e1 : x ^ (p₁ * p₁ + p₂ * (-q₁)) * y ^ (-(q₁ * p₁ + q₂ * (-q₁))) =
      x ^ (0 : ℤ) * y ^ (1 : ℤ) := by
    have := hrel' x
    rw [h1, hu, hv, hu, hvx] at this
    rw [zpow_zero, zpow_one, one_mul]
    exact this
  have e2 : x ^ (p₁ * p₂ + p₂ * (-q₂)) * y ^ (-(q₁ * p₂ + q₂ * (-q₂))) =
      x ^ (-1 : ℤ) * y ^ (0 : ℤ) := by
    have := hrel' y
    rw [h2, hu, hv, hu, hvy] at this
    rw [zpow_zero, mul_one, zpow_neg_one]
    exact this
  obtain ⟨E1, E2⟩ := zpow_pair_eq_zmod hxy hind e1
  obtain ⟨E3, E4⟩ := zpow_pair_eq_zmod hxy hind e2
  push_cast at E1 E2 E3 E4
  obtain ⟨hb, hc, hd, ha⟩ := zmod3_relation_solve _ _ _ _ E1 E2 E3 E4
  obtain ⟨i, hi, hai⟩ : ∃ i : ℤ, (i = 1 ∨ i = -1) ∧ (p₁ : ZMod 3) = i := by
    rcases ha with ha | ha
    · exact ⟨1, Or.inl rfl, by push_cast; exact ha⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; exact ha⟩
  have key : ∀ {m n : ℤ}, (m : ZMod 3) = n → 3 ∣ n - m := fun {m n} hmn => by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub m n 3).mp hmn
  refine ⟨i, hi, ?_, ?_⟩
  · rw [h1]
    exact zpow_pair_congr hx3 hy3 (key hai.symm) (key (hai.symm.trans hb.symm))
  · rw [h2]
    refine zpow_pair_congr hx3 hy3 (key (hai.symm.trans hc.symm)) (key ?_)
    push_cast
    rw [← hai]
    exact hd.symm

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

section Certs


namespace Ctx

theorem cj_mem_negSub (c : Ctx S) {g y : G} (hg : g ∈ c.NG) (hgz : g * S.z = S.z * g)
    (hy : y ∈ negSub c.OG S.z c.OG_comm) : cj y g ∈ negSub c.OG S.z c.OG_comm := by
  refine ⟨c.cj_mem_OG_of_mem_NG' hg hy.1, ?_⟩
  have hz : S.z⁻¹ = S.z := Ctx.zG_inv (S := S)
  have e : cj y S.z = y⁻¹ := by
    have := hy.2
    rw [hz] at this
    rw [cj, hz]
    exact this
  have e' : cj (cj y g) S.z = (cj y g)⁻¹ := by
    rw [cj_cj, hgz, ← cj_cj, e, cj_inv_left]
  rw [cj, hz] at e'
  rw [hz]
  exact e'

end Ctx

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)

include hφ h in
theorem Q_decomp : ∀ y ∈ negSub c.OG S.z c.OG_comm, ∃ p q : ℤ, y = φ₁ ^ p * (cj φ₁ v) ^ q :=
  exists_zpow_pair_of_card_nine (hφ.phi12_comm h) hφ.mem_Q (hφ.phi2_mem_Q h)
    (Ctx.card_negSub_OG c) (hφ.indep12 h)

include hφ h in
theorem exists_v1_action : ∃ i : ℤ, (i = 1 ∨ i = -1) ∧ cj φ₁ v₁ = φ₁ ^ i * (cj φ₁ v) ^ i ∧
    cj (cj φ₁ v) v₁ = φ₁ ^ i * (cj φ₁ v) ^ (-i) := by
  have hNG : v₁ ∈ c.NG := h.v1_mem_NG
  obtain ⟨p₁, q₁, h1⟩ := hφ.Q_decomp h _ (c.cj_mem_negSub hNG h.v1_comm_z hφ.mem_Q)
  obtain ⟨p₂, q₂, h2⟩ := hφ.Q_decomp h _ (c.cj_mem_negSub hNG h.v1_comm_z (hφ.phi2_mem_Q h))
  exact exists_action_of_relation (hφ.phi12_comm h) hφ.cube (hφ.phi2_cube h) (hφ.indep12 h)
    hφ.by_t (hφ.phi2_by_t h) rfl (hφ.phi2_by_v h) h.rel.v1_u_sq h1 h2

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
