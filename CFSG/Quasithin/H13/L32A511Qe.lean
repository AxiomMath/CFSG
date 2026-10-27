module

public import CFSG.Quasithin.H13.L32A511Qd
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.H13.L32A511Qb

public section

namespace CFSG.Quasithin.H13.Q511

open CFSG.Quasithin
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_three_mul_add_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ k₀ : ℕ, p ∣ 3 * k₀ + 1 := by
  obtain ⟨k, hk⟩ := exists_mul_mod_eq_one hp (n := 3) (fun h => by
    have := Nat.le_of_dvd (by norm_num) h; omega)
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  refine ⟨p' * k, ?_⟩
  have h1 := Nat.div_add_mod (3 * k) (p' + 1)
  rw [hk] at h1
  obtain ⟨q, hq⟩ : ∃ q, (p' + 1) * q + 1 = 3 * k := ⟨_, h1⟩
  refine ⟨p' * q + 1, ?_⟩
  rw [show 3 * (p' * k) + 1 = p' * (3 * k) + 1 by ring, ← hq]
  ring

theorem false_of_good (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {D₁ Z₁ : Subgroup (MulAut V)} (hZD : Z₁ ≤ D₁) (hZc : ∀ z ∈ Z₁, ∀ d ∈ D₁, z * d = d * z)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b * a⁻¹ * b⁻¹ ∈ Z₁) (hexp : ∀ d ∈ D₁, d ^ p = 1)
    {x s c : MulAut V} (hx3 : x ^ 3 = 1) (hs2 : s ^ 2 = 1) (hsx : s * x * s⁻¹ = x⁻¹)
    (hcx : c * x = x * c) (hxD : ∀ d ∈ D₁, x * d * x⁻¹ ∈ D₁)
    (hZx : ∀ z ∈ Z₁, x * z * x⁻¹ = z)
    (hb : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 2 ∨
      (c ^ 2 = 1 ∧ c ≠ 1 ∧ c * s = s * c ∧
        rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤ 3))
    {r : MulAut V} (hrD : r ∈ D₁) (hrs : s * r * s⁻¹ = r⁻¹)
    (hrc : c * r * c⁻¹ = r ∨ c * r * c⁻¹ = r⁻¹)
    (hz : r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹) ∈ Z₁)
    (hind : ∀ k : ℕ, (x * r * x⁻¹) * (r ^ k)⁻¹ ∉ Z₁) : False := by
  have hxinv : ∀ a : MulAut V, x⁻¹ * a * x = x * (x * a * x⁻¹) * x⁻¹ := fun a => by
    calc x⁻¹ * a * x = x ^ 3 * (x⁻¹ * a * x) * (x ^ 3)⁻¹ := by rw [hx3]; group
      _ = x * (x * a * x⁻¹) * x⁻¹ := by rw [pow_three]; group
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, r₁ = x * r * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = x * r₁ * x⁻¹ := ⟨_, rfl⟩
  rw [← hr₁] at hz hind
  rw [← hr₂] at hz
  have hr₁D : r₁ ∈ D₁ := hr₁ ▸ hxD r hrD
  have hr₂D : r₂ ∈ D₁ := hr₂ ▸ hxD r₁ hr₁D
  have hxr₂ : x * r₂ * x⁻¹ = r := by
    calc x * r₂ * x⁻¹ = x ^ 3 * r * (x ^ 3)⁻¹ := by rw [hr₂, hr₁, pow_three]; group
      _ = r := by rw [hx3]; group
  have hsr₁ : s * r₁ * s⁻¹ = r₂⁻¹ := by
    calc s * r₁ * s⁻¹ = (s * x * s⁻¹) * (s * r * s⁻¹) * (s * x * s⁻¹)⁻¹ := by rw [hr₁]; group
      _ = x⁻¹ * r⁻¹ * x := by rw [hsx, hrs, inv_inv]
      _ = r₂⁻¹ := by rw [hxinv, hr₂, hr₁]; simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hsr₂ : s * r₂ * s⁻¹ = r₁⁻¹ := by
    calc s * r₂ * s⁻¹ = (s * x * s⁻¹) * (s * r₁ * s⁻¹) * (s * x * s⁻¹)⁻¹ := by rw [hr₂]; group
      _ = (x⁻¹ * r₂ * x)⁻¹ := by rw [hsx, hsr₁, inv_inv]; group
      _ = r₁⁻¹ := by rw [hr₂]; group
  set z := r * r₁ * r₂ with hzdef
  have hzD : z ∈ D₁ := hZD hz
  have hzc : ∀ d ∈ D₁, z * d = d * z := hZc z hz
  have hrk3 : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 3 := by
    rcases hb with h | ⟨-, -, -, h⟩
    · omega
    · have h1 := rk_map_add_rk_inf (⊤ : Subgroup V) s
      rw [top_inf_eq, rk_top] at h1
      have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c))
      have h3 : rk ↥(fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤
          rk (fixV (Subgroup.zpowers s)) := rk_mono inf_le_left
      omega
  set w := r * r₁ * r⁻¹ * r₁⁻¹ with hwdef
  have hwZ : w ∈ Z₁ := hcomm r hrD r₁ hr₁D
  by_cases hw : w = 1
  swap
  ·
    have hwr : w * r = r * w := hZc w hwZ r hrD
    have hwr₁ : w * r₁ = r₁ * w := hZc w hwZ r₁ hr₁D
    have hsw : s * w * s⁻¹ = w⁻¹ := by
      have hr₂' : r₂ = r₁⁻¹ * r⁻¹ * z := by rw [hzdef]; group
      have hzr : z * r = r * z := hzc r hrD
      set A := r₁ * r * r₁⁻¹ * r⁻¹ with hA
      have hAD : A ∈ D₁ :=
        D₁.mul_mem (D₁.mul_mem (D₁.mul_mem hr₁D hrD) (D₁.inv_mem hr₁D)) (D₁.inv_mem hrD)
      have hzA : z * A = A * z := hzc A hAD
      calc s * w * s⁻¹ = (s * r * s⁻¹) * (s * r₁ * s⁻¹) * (s * r * s⁻¹)⁻¹ *
            (s * r₁ * s⁻¹)⁻¹ := by rw [hwdef]; group
        _ = r⁻¹ * (z⁻¹ * r * r₁) * r * (r₁⁻¹ * r⁻¹ * z) := by
          rw [hrs, hsr₁, hr₂', inv_inv, inv_inv]; group
        _ = (r⁻¹ * z⁻¹ * r) * A * z := by rw [hA]; group
        _ = z⁻¹ * A * z := by
          rw [show r⁻¹ * z⁻¹ * r = (r⁻¹ * z * r)⁻¹ by group, mul_assoc r⁻¹ z r, hzr]
          group
        _ = A := by rw [mul_assoc, ← hzA]; group
        _ = w⁻¹ := by rw [hA, hwdef]; group
    exact false_of_nonabelian hV hp5 hwdef hw hwr hwr₁ (hexp r hrD) (hexp w (hZD hwZ)) hs2 hrs
      hsw hrk3
  ·
    have hc01 : r * r₁ = r₁ * r := by
      calc r * r₁ = (r * r₁ * r⁻¹ * r₁⁻¹) * (r₁ * r) := by group
        _ = r₁ * r := by rw [← hwdef, hw, one_mul]
    have hc12 : r₁ * r₂ = r₂ * r₁ := by
      calc r₁ * r₂ = x * (r * r₁) * x⁻¹ := by rw [hr₂, hr₁]; group
        _ = x * (r₁ * r) * x⁻¹ := by rw [hc01]
        _ = r₂ * r₁ := by rw [hr₂, hr₁]; group
    have hc20 : r₂ * r = r * r₂ := by
      calc r₂ * r = (x * r₁ * x⁻¹) * (x * r₂ * x⁻¹) := by rw [← hr₂, hxr₂]
        _ = x * (r₁ * r₂) * x⁻¹ := by group
        _ = x * (r₂ * r₁) * x⁻¹ := by rw [hc12]
        _ = (x * r₂ * x⁻¹) * (x * r₁ * x⁻¹) := by group
        _ = r * r₂ := by rw [← hr₂, hxr₂]
    have hzs : s * z * s⁻¹ = z⁻¹ := by
      calc s * z * s⁻¹ = (s * r * s⁻¹) * (s * r₁ * s⁻¹) * (s * r₂ * s⁻¹) := by rw [hzdef]; group
        _ = r⁻¹ * r₂⁻¹ * r₁⁻¹ := by rw [hrs, hsr₁, hsr₂]
        _ = (r₁ * r₂ * r)⁻¹ := by group
        _ = (r * r₁ * r₂)⁻¹ := by rw [mul_assoc, hc20, ← mul_assoc, ← hc01]
    obtain ⟨k₀, t, ht⟩ := exists_three_mul_add_one hp.out hp5
    obtain ⟨u, hu⟩ : ∃ u, u = z ^ k₀ := ⟨_, rfl⟩
    have huZ : u ∈ Z₁ := hu ▸ Z₁.pow_mem hz k₀
    have huD : u ∈ D₁ := hZD huZ
    have huc : ∀ d ∈ D₁, u * d = d * u := hZc u huZ
    have hux : x * u * x⁻¹ = u := hZx u huZ
    have hus : s * u * s⁻¹ = u⁻¹ := by rw [hu, pow_conj, hzs, inv_pow]
    have hzu : z * (u * u * u) = 1 := by
      have : z * (u * u * u) = z ^ (3 * k₀ + 1) := by
        rw [hu, ← pow_add, ← pow_add, ← pow_succ', show k₀ + k₀ + k₀ + 1 = 3 * k₀ + 1 by ring]
      rw [this, ht, pow_mul, hexp z hzD, one_pow]
    obtain ⟨R, hR⟩ : ∃ R, R = r * u := ⟨_, rfl⟩
    obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = r₁ * u := ⟨_, rfl⟩
    have hRD : R ∈ D₁ := hR ▸ D₁.mul_mem hrD huD
    have hR₁D : R₁ ∈ D₁ := hR₁ ▸ D₁.mul_mem hr₁D huD
    have hur : u * r = r * u := huc r hrD
    have hur₁ : u * r₁ = r₁ * u := huc r₁ hr₁D
    have hxR : x * R * x⁻¹ = R₁ := by
      rw [hR, hR₁, show x * (r * u) * x⁻¹ = (x * r * x⁻¹) * (x * u * x⁻¹) by group, hux, ← hr₁]
    have hxR₁ : x * R₁ * x⁻¹ = (R * R₁)⁻¹ := by
      have hr₂' : r₂ = (r * r₁)⁻¹ * z := by rw [hzdef]; group
      have hzu' : z = (u * u * u)⁻¹ := eq_inv_of_mul_eq_one_left hzu
      have hq : u * (r * r₁) = (r * r₁) * u := huc _ (D₁.mul_mem hrD hr₁D)
      have e1 : r * u * (r₁ * u) = r * r₁ * u * u := by
        rw [mul_assoc r u, ← mul_assoc u r₁, hur₁]; group
      have e2 : u * (u * (r * r₁)) = r * r₁ * u * u := by
        rw [hq, ← mul_assoc, hq]
      calc x * R₁ * x⁻¹ = (x * r₁ * x⁻¹) * (x * u * x⁻¹) := by rw [hR₁]; group
        _ = (r * r₁)⁻¹ * (u * u * u)⁻¹ * u := by rw [← hr₂, hux, hr₂', hzu']
        _ = (u * (u * (r * r₁)))⁻¹ := by group
        _ = (R * R₁)⁻¹ := by rw [e2, hR, hR₁, e1]
    have hRR₁ : R * R₁ = R₁ * R := by
      rw [hR, hR₁]
      calc r * u * (r₁ * u) = r * (u * r₁) * u := by group
        _ = r * r₁ * (u * u) := by rw [hur₁]; group
        _ = r₁ * r * (u * u) := by rw [hc01]
        _ = r₁ * (u * r) * u := by rw [hur]; group
        _ = r₁ * u * (r * u) := by group
    have hsR : s * R * s⁻¹ = R⁻¹ := by
      rw [hR, show s * (r * u) * s⁻¹ = (s * r * s⁻¹) * (s * u * s⁻¹) by group, hrs, hus,
        ← hur, mul_inv_rev]
    have hRk : ∀ k : ℕ, R ^ k = r ^ k * u ^ k := fun k => by
      rw [hR]
      exact (Commute.mul_pow (hur.symm : Commute r u) k)
    have hindR : ∀ k : ℕ, R₁ ≠ R ^ k := by
      intro k h
      apply hind k
      have h1 : r₁ = r ^ k * u ^ k * u⁻¹ := by
        rw [← hRk, ← h, hR₁]
        group
      have h2 : r₁ * (r ^ k)⁻¹ = u ^ k * u⁻¹ := by
        rw [h1]
        have h3 : (u ^ k * u⁻¹) * r ^ k = r ^ k * (u ^ k * u⁻¹) :=
          hZc _ (Z₁.mul_mem (Z₁.pow_mem huZ k) (Z₁.inv_mem huZ)) _ (D₁.pow_mem hrD k)
        calc r ^ k * u ^ k * u⁻¹ * (r ^ k)⁻¹ = r ^ k * (u ^ k * u⁻¹) * (r ^ k)⁻¹ := by group
          _ = u ^ k * u⁻¹ := by rw [← h3]; group
      rw [h2]
      exact Z₁.mul_mem (Z₁.pow_mem huZ k) (Z₁.inv_mem huZ)
    have hR1 : R ≠ 1 := by
      intro h
      apply hindR 0
      rw [pow_zero, ← hxR, h]
      group
    refine false_of_abelian hV hp5 (hexp R hRD) (hexp R₁ hR₁D) hR1 hRR₁ hindR hxR hxR₁ hs2 hsR ?_
    rcases hb with h | ⟨hc2, hc1, hcs, hcV⟩
    · exact Or.inl h
    · refine Or.inr ⟨c, hc2, hc1, hcs, ?_, hcV⟩
      have hcr₁ : ∀ e : ℤ, c * r * c⁻¹ = r ^ e → c * r₁ * c⁻¹ = r₁ ^ e := by
        intro e he
        calc c * r₁ * c⁻¹ = x * (c * r * c⁻¹) * x⁻¹ := by
              rw [hr₁, show c * (x * r * x⁻¹) * c⁻¹ = (c * x) * r * (c * x)⁻¹ by group, hcx]
              group
          _ = r₁ ^ e := by rw [he, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hr₁]
      have hcr₂ : ∀ e : ℤ, c * r * c⁻¹ = r ^ e → c * r₂ * c⁻¹ = r₂ ^ e := by
        intro e he
        calc c * r₂ * c⁻¹ = x * (c * r₁ * c⁻¹) * x⁻¹ := by
              rw [hr₂, show c * (x * r₁ * x⁻¹) * c⁻¹ = (c * x) * r₁ * (c * x)⁻¹ by group, hcx]
              group
          _ = r₂ ^ e := by
              rw [hcr₁ e he, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hr₂]
      have hcz : ∀ e : ℤ, c * r * c⁻¹ = r ^ e → c * z * c⁻¹ = z ^ e := by
        intro e he
        calc c * z * c⁻¹ = (c * r * c⁻¹) * (c * r₁ * c⁻¹) * (c * r₂ * c⁻¹) := by
              rw [hzdef]; group
          _ = r ^ e * r₁ ^ e * r₂ ^ e := by rw [he, hcr₁ e he, hcr₂ e he]
          _ = z ^ e := by
              have h01 : Commute r r₁ := hc01
              have h012 : Commute (r * r₁) r₂ :=
                Commute.mul_left (Commute.symm (show Commute r₂ r from hc20)) hc12
              rw [hzdef, h012.mul_zpow, h01.mul_zpow]
      rcases hrc with h1 | h1
      · left
        have h1' : c * r * c⁻¹ = r ^ (1 : ℤ) := by rw [zpow_one]; exact h1
        have hz' := hcz 1 h1'
        rw [zpow_one] at hz'
        have hcu : c * u * c⁻¹ = u := by rw [hu, pow_conj, hz']
        have h2 : c * r₁ * c⁻¹ = r₁ := by
          have := hcr₁ 1 h1'
          rwa [zpow_one] at this
        constructor
        · rw [hR, show c * (r * u) * c⁻¹ = (c * r * c⁻¹) * (c * u * c⁻¹) by group, h1, hcu]
        · rw [hR₁, show c * (r₁ * u) * c⁻¹ = (c * r₁ * c⁻¹) * (c * u * c⁻¹) by group, h2, hcu]
      · right
        have h1' : c * r * c⁻¹ = r ^ (-1 : ℤ) := by rw [zpow_neg_one]; exact h1
        have hz' := hcz (-1) h1'
        rw [zpow_neg_one] at hz'
        have hcu : c * u * c⁻¹ = u⁻¹ := by rw [hu, pow_conj, hz', inv_pow]
        constructor
        · rw [hR, show c * (r * u) * c⁻¹ = (c * r * c⁻¹) * (c * u * c⁻¹) by group, h1, hcu,
            ← hur, mul_inv_rev]
        · have h2 : c * r₁ * c⁻¹ = r₁⁻¹ := by
            have := hcr₁ (-1) h1'
            rwa [zpow_neg_one] at this
          rw [hR₁, show c * (r₁ * u) * c⁻¹ = (c * r₁ * c⁻¹) * (c * u * c⁻¹) by group, h2, hcu,
            ← hur₁, mul_inv_rev]

theorem false_of_pair (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {D₁ Z₁ : Subgroup (MulAut V)} (hZD : Z₁ ≤ D₁) (hZc : ∀ z ∈ Z₁, ∀ d ∈ D₁, z * d = d * z)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b * a⁻¹ * b⁻¹ ∈ Z₁) (hexp : ∀ d ∈ D₁, d ^ p = 1)
    {x s c : MulAut V} (hx3 : x ^ 3 = 1) (hs2 : s ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (hsx : s * x * s⁻¹ = x⁻¹) (hcx : c * x = x * c) (hcs : c * s = s * c)
    (hxD : ∀ d ∈ D₁, x * d * x⁻¹ ∈ D₁) (hsD : ∀ d ∈ D₁, s * d * s⁻¹ ∈ D₁)
    (hcD : ∀ d ∈ D₁, c * d * c⁻¹ ∈ D₁) (hxZ : ∀ z ∈ Z₁, x * z * x⁻¹ = z)
    (hsZ : ∀ z ∈ Z₁, s * z * s⁻¹ ∈ Z₁) (hcZ : ∀ z ∈ Z₁, c * z * c⁻¹ ∈ Z₁)
    (hb : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 2 ∨
      (c ≠ 1 ∧ rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤ 3))
    {d₀ : MulAut V} (hd₀ : d₀ ∈ D₁) (hnt : x * d₀ * x⁻¹ * d₀⁻¹ ∉ Z₁) : False := by
  obtain ⟨r, hrD, hrs, hrc, hz, hind⟩ := exists_good_elt hp.out hp5 hZD hZc hcomm hexp hx3 hs2
    hc2 hsx hcx hcs hxD hsD hcD (fun z hz => by rw [hxZ z hz]; exact hz) hsZ hcZ hd₀ hnt
  exact false_of_good hV hp5 hZD hZc hcomm hexp hx3 hs2 hsx hcx hxD hxZ
    (hb.imp id fun h => ⟨hc2, h.1, hcs, h.2⟩) hrD hrs hrc hz hind

section Conj

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def conjAut (D : Subgroup G) (g : G)
    (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : MulAut ↥D :=
  MulEquiv.ofBijective (conjRes D g h) (Finite.injective_iff_bijective.mp fun a b hab => by
    have h1 := congrArg Subtype.val hab
    simp only [coe_conjRes] at h1
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1)))

theorem conj_mem_map {D : Subgroup G} {D₀ : Subgroup ↥D} [hch : D₀.Characteristic] {g : G}
    (hg : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : ∀ e ∈ D₀.map D.subtype, g * e * g⁻¹ ∈ D₀.map D.subtype := by
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨conjAut D g hg d, Subgroup.characteristic_iff_le_comap.mp hch _ hd, rfl⟩

omit [Finite G] in
theorem conj_mem_center {E : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    ∀ z ∈ E ⊓ Subgroup.centralizer (E : Set G),
      g * z * g⁻¹ ∈ E ⊓ Subgroup.centralizer (E : Set G) := by
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have he' : g⁻¹ * e * g ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) e).mp he
    rwa [inv_inv] at this
  have h1 : (g⁻¹ * e * g) * z = z * (g⁻¹ * e * g) := Subgroup.mem_centralizer_iff.mp hz.2 _ he'
  calc e * (g * z * g⁻¹) = g * ((g⁻¹ * e * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * e := by group

end Conj

theorem commute_of_pgroup (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {D : Subgroup (MulAut V)} (hD : IsPGroup p ↥D) {x s c : MulAut V} (hx3 : x ^ 3 = 1)
    (hs2 : s ^ 2 = 1) (hc2 : c ^ 2 = 1) (hsx : s * x * s⁻¹ = x⁻¹) (hcx : c * x = x * c)
    (hcs : c * s = s * c) (hxD : ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D)
    (hcD : ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hb : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 2 ∨
      (c ≠ 1 ∧ rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤ 3)) :
    ∀ d ∈ D, x * d = d * x := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨d₁, hd₁, hxd₁⟩ := hne
  have hp2 : p ≠ 2 := by omega
  have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega)
  have : Nontrivial ↥D := ⟨⟨⟨d₁, hd₁⟩, 1, fun h => hxd₁ (by
    rw [show d₁ = 1 from congrArg Subtype.val h, mul_one, one_mul])⟩⟩
  obtain ⟨D₀, hch, -, hexp0, hcomm0, -, hker⟩ :=
    CFSG.SectionRank.Ccomm.supercritical_witness hp2 hD
  set α := conjAut D x hxD with hα
  have hαapp : ∀ d : ↥D, ((α d : ↥D) : MulAut V) = x * d * x⁻¹ := fun d => rfl
  have hα1 : α ∉ (CFSG.SectionRank.Ccomm.frattiniAction D₀).ker := by
    intro hmem
    obtain ⟨k, hk⟩ := hker ⟨α, hmem⟩
    have hk' : α ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hα3 : α ^ 3 = 1 := by
      refine MulEquiv.ext fun d => Subtype.ext ?_
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hαapp, hαapp, hαapp]
      calc x * (x * (x * (d : MulAut V) * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * d * (x ^ 3)⁻¹ := by
            rw [pow_three]; group
        _ = d := by rw [hx3]; group
    have h1 : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hα3) (Nat.Coprime.pow_right k h3p))
      (orderOf_dvd_of_pow_eq_one hk')
    rw [orderOf_eq_one_iff] at h1
    apply hxd₁
    have h2 : ((α ⟨d₁, hd₁⟩ : ↥D) : MulAut V) = d₁ := by rw [h1]; rfl
    rw [hαapp] at h2
    calc x * d₁ = (x * d₁ * x⁻¹) * x := by group
      _ = d₁ * x := by rw [h2]
  set E : Subgroup (MulAut V) := D₀.map D.subtype with hE
  set Z : Subgroup (MulAut V) := E ⊓ Subgroup.centralizer (E : Set (MulAut V)) with hZ
  have hN : ∀ g : MulAut V, (∀ d ∈ D, g * d * g⁻¹ ∈ D) →
      g ∈ Subgroup.normalizer (E : Set (MulAut V)) :=
    fun g hg => Subgroup.mem_normalizer_fintype (conj_mem_map hg)
  have hEn : ∀ g : MulAut V, (∀ d ∈ D, g * d * g⁻¹ ∈ D) → ∀ e ∈ E, g * e * g⁻¹ ∈ E :=
    fun g hg => conj_mem_map hg
  have hZn : ∀ g : MulAut V, (∀ d ∈ D, g * d * g⁻¹ ∈ D) → ∀ z ∈ Z, g * z * g⁻¹ ∈ Z :=
    fun g hg => conj_mem_center (hN g hg)
  have hEexp : ∀ e ∈ E, e ^ p = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have := congrArg Subtype.val (hexp0 d hd)
    simpa using this
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ D₀ ⊓ Subgroup.centralizer (D₀ : Set ↥D) :=
      hcomm0 (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
    refine Subgroup.mem_inf.mpr ⟨⟨⁅a, b⁆, h1.1, by simp [commutatorElement_def]⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp h1.2 e he)
    simpa [commutatorElement_def] using h2
  by_cases hA : ∃ z ∈ Z, x * z * x⁻¹ ≠ z
  ·
    obtain ⟨z₀, hz₀, hxz₀⟩ := hA
    refine false_of_pair hV hp5 (D₁ := Z) (Z₁ := ⊥) bot_le
      (fun z hz d _ => by rw [Subgroup.mem_bot.mp hz, one_mul, mul_one])
      (fun a ha b hb => by
        rw [Subgroup.mem_bot]
        have h1 : b * a = a * b := Subgroup.mem_centralizer_iff.mp ha.2 b hb.1
        rw [← h1]
        group)
      (fun d hd => hEexp d hd.1) hx3 hs2 hc2 hsx hcx hcs (hZn x hxD) (hZn s hsD) (hZn c hcD)
      (fun z hz => by rw [Subgroup.mem_bot.mp hz]; group)
      (fun z hz => by rw [Subgroup.mem_bot.mp hz, mul_one, mul_inv_cancel]; exact one_mem _)
      (fun z hz => by rw [Subgroup.mem_bot.mp hz, mul_one, mul_inv_cancel]; exact one_mem _)
      hb hz₀ fun h => hxz₀ ?_
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at h
  ·
    push Not at hA
    have hd₀ : ∃ d₀ ∈ E, x * d₀ * x⁻¹ * d₀⁻¹ ∉ Z := by
      by_contra hcon
      push Not at hcon
      have key : ∀ e ∈ E, x * e * x⁻¹ = e := by
        intro e he
        obtain ⟨z, hz⟩ : ∃ z, z = x * e * x⁻¹ * e⁻¹ := ⟨_, rfl⟩
        have hzZ : z ∈ Z := hz ▸ hcon e he
        have hxz : x * z * x⁻¹ = z := hA z hzZ
        have h1 : x * e * x⁻¹ = z * e := by rw [hz]; group
        have h2 : x ^ 3 * e * (x ^ 3)⁻¹ = z * (z * (z * e)) := by
          calc x ^ 3 * e * (x ^ 3)⁻¹ = x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ := by
                rw [pow_three]; group
            _ = x * (x * (z * e) * x⁻¹) * x⁻¹ := by rw [h1]
            _ = x * ((x * z * x⁻¹) * (x * e * x⁻¹)) * x⁻¹ := by group
            _ = x * (z * (z * e)) * x⁻¹ := by rw [hxz, h1]
            _ = (x * z * x⁻¹) * ((x * z * x⁻¹) * (x * e * x⁻¹)) := by group
            _ = z * (z * (z * e)) := by rw [hxz, h1]
        rw [hx3, one_mul, inv_one, mul_one, ← mul_assoc, ← mul_assoc] at h2
        have h3 : z ^ 3 = 1 := by
          rw [pow_three, ← mul_assoc]
          exact (mul_eq_right.mp h2.symm)
        have h4 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) h3p)
          (orderOf_dvd_of_pow_eq_one (hEexp z hzZ.1))
        rw [h1, orderOf_eq_one_iff.mp h4, one_mul]
      apply hα1
      rw [CFSG.SectionRank.Ccomm.mem_ker_frattiniAction]
      intro d
      have hfix : MulAut.characteristic D₀ α d = d := by
        apply Subtype.ext
        apply Subtype.ext
        show x * ((d : ↥D) : MulAut V) * x⁻¹ = ((d : ↥D) : MulAut V)
        exact key _ ⟨d, d.2, rfl⟩
      rw [hfix, inv_mul_cancel]
      exact one_mem _
    obtain ⟨d₀, hd₀E, hd₀Z⟩ := hd₀
    exact false_of_pair hV hp5 (D₁ := E) (Z₁ := Z) inf_le_left
      (fun z hz d hd => (Subgroup.mem_centralizer_iff.mp hz.2 d hd).symm) hEcomm hEexp hx3 hs2
      hc2 hsx hcx hcs (hEn x hxD) (hEn s hsD) (hEn c hcD) hA (hZn s hsD) (hZn c hcD) hb hd₀E hd₀Z

end CFSG.Quasithin.H13.Q511
