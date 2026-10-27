module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6A

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem M_eq : Subgroup.normalizer (L : Set G) = Subgroup.centralizer ({z} : Set G) := c.f.MC

theorem T_le_Cz : T ≤ Subgroup.centralizer ({z} : Set G) :=
  c.f.T_le_centralizer c.cx.hyp.normalizes

theorem conj_z {t : G} (ht : t ∈ T) : t * z * t⁻¹ = z := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 (c.T_le_Cz ht), mul_inv_cancel_right]

theorem z_sq : z * z = 1 := by rw [← pow_two, ← c.f.order, pow_orderOf_eq_one]

theorem v_sq : v * v = 1 := by rw [← pow_two]; exact c.f.sq v (c.EV c.vE)

theorem zv_comm : z * v = v * z :=
  Subgroup.mem_centralizer_iff.1 (c.f.le_centralizer (c.EV c.vE)) z c.f.mem_zV.1

theorem v_ne_one : v ≠ 1 := fun h => c.vL (h ▸ Subgroup.one_mem _)

theorem v_ne_z : v ≠ z := fun h => c.vL (h ▸ c.f.mem_zV.2)

theorem z_ne_one : z ≠ 1 := c.f.ne_one

theorem vz_ne_z : v * z ≠ z := fun h => c.v_ne_one (mul_eq_right.mp h)

theorem vz_ne_v : v * z ≠ v := fun h => c.z_ne_one (mul_eq_left.mp h)

theorem mem_E {x : G} (hx : x ∈ E) : x = 1 ∨ x = z ∨ x = v ∨ x = v * z := by
  obtain ⟨-, hE, -⟩ := c.facts4
  have hv2 : orderOf v = 2 := orderOf_eq_prime (c.f.sq v (c.EV c.vE)) c.v_ne_one
  have hzN : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have haV : a ∈ V := (Subgroup.zpowers_le.2 (c.EV c.vE)) ha
    have hbV : b ∈ V := (Subgroup.zpowers_le.2 c.f.mem_zV.1) hb
    exact Subgroup.mem_centralizer_iff.1 (c.f.le_centralizer haV) b hbV
  rw [hE] at hx
  have h1 : x ∈ (Subgroup.zpowers v : Set G) * (Subgroup.zpowers z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf hv2 ha with ha' | ha' <;>
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf c.f.order hb with hb' | hb' <;>
    rw [ha', hb']
  · left; exact mul_one 1
  · right; left; exact one_mul z
  · right; right; left; exact mul_one v
  · right; right; right; rfl

theorem exists_t0 : ∃ t₀ ∈ T, t₀ * v * t₀⁻¹ = v * z := by
  by_contra h
  push Not at h
  apply c.vL
  apply cx_inf_centralizer_T_le c.cx c.f c.card16 c.nat
  refine ⟨c.EV c.vE, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
  rcases c.facts4.2.2 t ht with h1 | h1
  · calc t * v = t * v * t⁻¹ * t := by group
      _ = v * t := by rw [h1]
  · exact absurd h1 (h t ht)

theorem T_le_NR1 : T ≤ Subgroup.normalizer (c.R1 : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ s ∈ T, ∀ y ∈ c.R1, s * y * s⁻¹ ∈ c.R1 := by
    intro s hs y hy
    refine ⟨T.mul_mem (T.mul_mem hs hy.1) (T.inv_mem hs), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro e he
    have he' : s⁻¹ * e * s ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (c.TE (T.inv_mem hs)) e).1 he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hy.2 _ he'
    calc e * (s * y * s⁻¹) = s * ((s⁻¹ * e * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * e * s)) * s⁻¹ := by rw [h1]
      _ = s * y * s⁻¹ * e := by group
  refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem exists_three_cycle
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ g ∈ Subgroup.normalizer (c.R1 : Set G), g * z * g⁻¹ = v ∧ g * v * g⁻¹ = v * z := by
  obtain ⟨-, -, hNE⟩ := c.partA hN
  obtain ⟨g₀, hg₀R, hg₀M⟩ : ∃ g ∈ Subgroup.normalizer (c.R1 : Set G),
      g ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hN h
  obtain ⟨t₀, ht₀, ht₀v⟩ := c.exists_t0
  have ht₀z := c.conj_z ht₀
  have ht₀R := c.T_le_NR1 ht₀
  have hg₀E := hNE hg₀R
  have hzE : z ∈ E := c.facts4.1
  have hconjE : ∀ x ∈ E, g₀ * x * g₀⁻¹ ∈ E := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hg₀E x).1 hx
  have ha1 : g₀ * z * g₀⁻¹ ≠ 1 := fun h => c.z_ne_one (by
    calc z = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h]; group)
  have haz : g₀ * z * g₀⁻¹ ≠ z := fun h => hg₀M (by
    rw [c.M_eq, Subgroup.mem_centralizer_singleton_iff]
    calc g₀ * z = g₀ * z * g₀⁻¹ * g₀ := by group
      _ = z * g₀ := by rw [h])
  have hb1 : g₀ * v * g₀⁻¹ ≠ 1 := fun h => c.v_ne_one (by
    calc v = g₀⁻¹ * (g₀ * v * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h]; group)
  have hab : g₀ * v * g₀⁻¹ ≠ g₀ * z * g₀⁻¹ := fun h => c.v_ne_z (by
    calc v = g₀⁻¹ * (g₀ * v * g₀⁻¹) * g₀ := by group
      _ = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by rw [h]
      _ = z := by group)
  have hvz : g₀ * (v * z) * g₀⁻¹ = (g₀ * v * g₀⁻¹) * (g₀ * z * g₀⁻¹) := by group
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (c.f.le_centralizer (c.EV hy)) x (c.EV hx)
  have hvE := c.vE
  rcases c.mem_E (hconjE z hzE) with ha | ha | ha | ha
  · exact absurd ha ha1
  · exact absurd ha haz
  ·
    rcases c.mem_E (hconjE v hvE) with hb | hb | hb | hb
    · exact absurd hb hb1
    ·
      refine ⟨g₀ * t₀, Subgroup.mul_mem _ hg₀R ht₀R, ?_, ?_⟩
      · calc g₀ * t₀ * z * (g₀ * t₀)⁻¹ = g₀ * (t₀ * z * t₀⁻¹) * g₀⁻¹ := by group
          _ = v := by rw [ht₀z, ha]
      · calc g₀ * t₀ * v * (g₀ * t₀)⁻¹ = g₀ * (t₀ * v * t₀⁻¹) * g₀⁻¹ := by group
          _ = v * z := by rw [ht₀v, hvz, ha, hb, c.zv_comm]
    · exact absurd (hb.trans ha.symm) hab
    · exact ⟨g₀, hg₀R, ha, hb⟩
  ·
    rcases c.mem_E (hconjE v hvE) with hb | hb | hb | hb
    · exact absurd hb hb1
    ·
      refine ⟨g₀⁻¹, Subgroup.inv_mem _ hg₀R, ?_, ?_⟩
      · calc g₀⁻¹ * z * g₀⁻¹⁻¹ = g₀⁻¹ * (g₀ * v * g₀⁻¹) * g₀ := by rw [hb]; group
          _ = v := by group
      · have h1 : g₀ * (v * z) * g₀⁻¹ = v := by
          rw [hvz, hb, ha, ← mul_assoc, c.zv_comm, mul_assoc, c.z_sq, mul_one]
        calc g₀⁻¹ * v * g₀⁻¹⁻¹ = g₀⁻¹ * (g₀ * (v * z) * g₀⁻¹) * g₀ := by rw [h1]; group
          _ = v * z := by group
    ·
      refine ⟨t₀ * g₀, Subgroup.mul_mem _ ht₀R hg₀R, ?_, ?_⟩
      · calc t₀ * g₀ * z * (t₀ * g₀)⁻¹ = t₀ * (g₀ * z * g₀⁻¹) * t₀⁻¹ := by group
          _ = (t₀ * v * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by rw [ha]; group
          _ = v := by rw [ht₀v, ht₀z, mul_assoc, c.z_sq, mul_one]
      · calc t₀ * g₀ * v * (t₀ * g₀)⁻¹ = t₀ * (g₀ * v * g₀⁻¹) * t₀⁻¹ := by group
          _ = v * z := by rw [hb, ht₀v]
    · exact absurd (hb.trans ha.symm) hab

omit [Finite G] [IsMulCommutative ↥V] c in
theorem pow_conj_eq {h x : G} (hx : h * x * h⁻¹ = x) (q : ℕ) : h ^ q * x * (h ^ q)⁻¹ = x := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc h ^ (q + 1) * x * (h ^ (q + 1))⁻¹ = h ^ q * (h * x * h⁻¹) * (h ^ q)⁻¹ := by
          rw [pow_succ, mul_inv_rev]; group
      _ = x := by rw [hx, ih]

theorem cube_conj {g : G} (hgz : g * z * g⁻¹ = v) (hgv : g * v * g⁻¹ = v * z) :
    g ^ 2 * z * (g ^ 2)⁻¹ = v * z ∧ g ^ 3 * z * (g ^ 3)⁻¹ = z ∧
      g ^ 3 * v * (g ^ 3)⁻¹ = v := by
  have e2 : g ^ 2 = g * g := pow_two g
  have e3 : g ^ 3 = g * (g * g) := by rw [pow_succ', pow_two]
  have hvz : g * (v * z) * g⁻¹ = z := by
    calc g * (v * z) * g⁻¹ = (g * v * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z := by rw [hgv, hgz, mul_assoc, c.zv_comm, ← mul_assoc, c.v_sq, one_mul]
  have h2 : g ^ 2 * z * (g ^ 2)⁻¹ = v * z := by
    calc g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by rw [e2]; group
      _ = v * z := by rw [hgz, hgv]
  have h2v : g ^ 2 * v * (g ^ 2)⁻¹ = z := by
    calc g ^ 2 * v * (g ^ 2)⁻¹ = g * (g * v * g⁻¹) * g⁻¹ := by rw [e2]; group
      _ = z := by rw [hgv, hvz]
  refine ⟨h2, ?_, ?_⟩
  · calc g ^ 3 * z * (g ^ 3)⁻¹ = g * (g ^ 2 * z * (g ^ 2)⁻¹) * g⁻¹ := by rw [e3, e2]; group
      _ = z := by rw [h2, hvz]
  · calc g ^ 3 * v * (g ^ 3)⁻¹ = g * (g ^ 2 * v * (g ^ 2)⁻¹) * g⁻¹ := by rw [e3, e2]; group
      _ = v := by rw [h2v, hgz]

theorem exists_odd (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ y ∈ Subgroup.normalizer (c.R1 : Set G), Odd (orderOf y) ∧
      y ∉ Subgroup.normalizer (L : Set G) := by
  obtain ⟨g, hgR, hgz, hgv⟩ := c.exists_three_cycle hN
  obtain ⟨h2, h3z, h3v⟩ := c.cube_conj hgz hgv
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨g ^ 2 ^ k, Subgroup.pow_mem _ hgR _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) (Dvd.intro r hkr.symm), hkr,
      Nat.mul_div_cancel_left r (pow_pos two_pos k)]
    exact hr
  · intro hyM
    rw [c.M_eq, Subgroup.mem_centralizer_singleton_iff] at hyM
    have hy : g ^ 2 ^ k * z * (g ^ 2 ^ k)⁻¹ = z := by rw [hyM, mul_inv_cancel_right]
    set q := 2 ^ k / 3 with hq
    have hzq : (g ^ 3) ^ q * z * ((g ^ 3) ^ q)⁻¹ = z := pow_conj_eq h3z q
    have hvq : (g ^ 3) ^ q * v * ((g ^ 3) ^ q)⁻¹ = v := pow_conj_eq h3v q
    have hvzq : (g ^ 3) ^ q * (v * z) * ((g ^ 3) ^ q)⁻¹ = v * z := by
      calc (g ^ 3) ^ q * (v * z) * ((g ^ 3) ^ q)⁻¹ =
          ((g ^ 3) ^ q * v * ((g ^ 3) ^ q)⁻¹) * ((g ^ 3) ^ q * z * ((g ^ 3) ^ q)⁻¹) := by group
        _ = v * z := by rw [hvq, hzq]
    have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
      have : 2 ^ k % 3 ≠ 0 := by
        intro h0
        have h3d : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d) (by norm_num)
      omega
    have hdecomp : 2 ^ k = 3 * q + 2 ^ k % 3 := (Nat.div_add_mod (2 ^ k) 3).symm
    rcases hmod with hm | hm
    · have : g ^ 2 ^ k * z * (g ^ 2 ^ k)⁻¹ = v := by
        rw [hdecomp, hm, pow_add, pow_mul, pow_one]
        calc (g ^ 3) ^ q * g * z * ((g ^ 3) ^ q * g)⁻¹ =
            (g ^ 3) ^ q * (g * z * g⁻¹) * ((g ^ 3) ^ q)⁻¹ := by group
          _ = v := by rw [hgz, hvq]
      exact c.v_ne_z (this.symm.trans hy)
    · have : g ^ 2 ^ k * z * (g ^ 2 ^ k)⁻¹ = v * z := by
        rw [hdecomp, hm, pow_add, pow_mul]
        calc (g ^ 3) ^ q * g ^ 2 * z * ((g ^ 3) ^ q * g ^ 2)⁻¹ =
            (g ^ 3) ^ q * (g ^ 2 * z * (g ^ 2)⁻¹) * ((g ^ 3) ^ q)⁻¹ := by group
          _ = v * z := by rw [h2, hvzq]
      exact c.vz_ne_z (this.symm.trans hy)

end Ctx

end N1246

end CFSG.Quasithin.H13
