module

public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H13.S8Five

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem three_le_pRank_of_triple [Finite X] {x y z : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1) (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx1 : x ≠ 1)
    (hyx : ∀ n : ℕ, x ^ n ≠ y) (hzxy : ∀ m n : ℕ, x ^ m * y ^ n ≠ z) :
    3 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀ : Subgroup X := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ 3 = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = 3 ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀
    B₀.subtype Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁
    hF₁ (y := y) hy (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hyx n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ m n : ℕ, F₂ a = x ^ m * y ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₂ a
    obtain ⟨m, hm⟩ := hr₁' b
    exact ⟨m, n, by rw [hb, hm]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, -⟩ := CFSG.SectionRank.exists_extend hc₂ hp₂ hcard₂ F₂
    hF₂ (y := z) hz (by
      rintro ⟨a, ha⟩
      obtain ⟨m, n, hmn⟩ := hr₂' a
      exact hzxy m n (hmn ▸ ha))
    (fun a => by
      obtain ⟨m, n, hmn⟩ := hr₂' a
      rw [hmn]
      exact (hxz.pow_left m).mul_left (hyz.pow_left n))
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨F₃.range, le_top, ⟨⟨⟨fun a b => ?_⟩⟩, fun w hw => ?_⟩, ?_⟩
  · rintro r ⟨B, -, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card X := Subgroup.card_le_card_group B
  · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul, hc₃]
  · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hw
    rw [← map_pow, hp₃, map_one]
  · rw [← hcard₃]
    exact Nat.card_congr (MonoidHom.ofInjective hF₃).toEquiv.symm

theorem commutatorElement_mul_central {x y z w : X} (hz : ∀ v, z * v = v * z)
    (hw : ∀ v, w * v = v * w) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have h1 : z * (y * w) * z⁻¹ = y * w := by rw [hz]; group
  have h2 : w * x⁻¹ * w⁻¹ = x⁻¹ := by rw [hw]; group
  calc ⁅x * z, y * w⁆ = x * (z * (y * w) * z⁻¹) * x⁻¹ * (y * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by rw [h1]; group
    _ = ⁅x, y⁆ := by rw [h2, commutatorElement_def]

theorem commutatorElement_inv_left_of_central {x y : X} (hc : ∀ v, ⁅x, y⁆ * v = v * ⁅x, y⁆) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have hc' : ∀ v, ⁅x, y⁆⁻¹ * v = v * ⁅x, y⁆⁻¹ := fun v => by
    have := hc v⁻¹
    rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv] at this
    exact this.symm
  calc ⁅x⁻¹, y⁆ = x⁻¹ * (⁅x, y⁆⁻¹ * x) := by
        rw [commutatorElement_def, commutatorElement_def]; group
    _ = ⁅x, y⁆⁻¹ := by rw [hc' x]; group

theorem comm_of_inverters {Y : Type*} [Group Y] (φ : X →* Y)
    (hker : ∀ c, φ c = 1 → ∀ w, c * w = w * c) (hker3 : ∀ c, φ c = 1 → c ^ 3 = 1)
    {a b n₁ n₂ : X} (hab : φ a * φ b = φ b * φ a) (ha3 : φ a ^ 3 = 1) (hb3 : φ b ^ 3 = 1)
    (h1a : φ n₁ * φ a * (φ n₁)⁻¹ = (φ a)⁻¹) (h1b : φ n₁ * φ b * (φ n₁)⁻¹ = φ b)
    (h2b : φ n₂ * φ b * (φ n₂)⁻¹ = (φ b)⁻¹) :
    a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 := by
  have hconj : ∀ {n x : X}, φ n * φ x * (φ n)⁻¹ = (φ x)⁻¹ →
      ∃ k, φ k = 1 ∧ n * x * n⁻¹ = x⁻¹ * k := fun {n x} h =>
    ⟨x * (n * x * n⁻¹), by rw [map_mul, map_mul, map_mul, map_inv, h, mul_inv_cancel],
      by group⟩
  obtain ⟨k₁, hk₁, e1⟩ := hconj h1a
  have e2 : n₁ * b * n₁⁻¹ = b * (b⁻¹ * (n₁ * b * n₁⁻¹)) := by group
  have hk₂ : φ (b⁻¹ * (n₁ * b * n₁⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, h1b, inv_mul_cancel]
  set c := ⁅a, b⁆ with hcdef
  have hφc : φ c = 1 := by
    rw [hcdef, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have hcc := hker c hφc
  have hconjc : n₁ * c * n₁⁻¹ = c⁻¹ := by
    calc n₁ * c * n₁⁻¹ = ⁅n₁ * a * n₁⁻¹, n₁ * b * n₁⁻¹⁆ := by
          rw [hcdef, commutatorElement_def, commutatorElement_def]; group
      _ = ⁅a⁻¹ * k₁, b * (b⁻¹ * (n₁ * b * n₁⁻¹))⁆ := by rw [e1, ← e2]
      _ = ⁅a⁻¹, b⁆ := commutatorElement_mul_central (hker _ hk₁) (hker _ hk₂)
      _ = c⁻¹ := commutatorElement_inv_left_of_central hcc
  have hc1 : c = 1 := by
    have h1 : n₁ * c * n₁⁻¹ = c := by rw [← hcc n₁]; group
    have hcinv : c = c⁻¹ := h1.symm.trans hconjc
    have hc3 := hker3 c hφc
    have hc2 : c ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hcinv]
      exact mul_inv_cancel c
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  have hab' : a * b = b * a := by
    have : a * b * a⁻¹ * b⁻¹ = 1 := by rw [← commutatorElement_def]; exact hc1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [this, one_mul]
  have hcube : ∀ {n x : X}, φ x ^ 3 = 1 → φ n * φ x * (φ n)⁻¹ = (φ x)⁻¹ → x ^ 3 = 1 := by
    intro n x hx3 h
    obtain ⟨k, hk, e⟩ := hconj h
    have hd : φ (x ^ 3) = 1 := by rw [map_pow, hx3]
    have hdc := hker _ hd
    have hk3 := hker3 k hk
    have hkc : Commute x⁻¹ k := ((hker k hk) x⁻¹).symm
    have h1 : n * x ^ 3 * n⁻¹ = (x ^ 3)⁻¹ := by
      calc n * x ^ 3 * n⁻¹ = (n * x * n⁻¹) ^ 3 := by rw [conj_pow]
        _ = (x⁻¹ * k) ^ 3 := by rw [e]
        _ = x⁻¹ ^ 3 * k ^ 3 := hkc.mul_pow 3
        _ = (x ^ 3)⁻¹ := by rw [hk3, mul_one, inv_pow]
    have h2 : n * x ^ 3 * n⁻¹ = x ^ 3 := by rw [← hdc n]; group
    have hinv : x ^ 3 = (x ^ 3)⁻¹ := h2.symm.trans h1
    have h6 : x ^ 3 * x ^ 3 = 1 :=
      calc x ^ 3 * x ^ 3 = x ^ 3 * (x ^ 3)⁻¹ := congrArg (x ^ 3 * ·) hinv
        _ = 1 := mul_inv_cancel _
    have h9 : x ^ 3 * x ^ 3 * x ^ 3 = 1 := by
      have := hker3 _ hd
      rw [← this]
      group
    calc x ^ 3 = (x ^ 3 * x ^ 3 * x ^ 3) * (x ^ 3 * x ^ 3)⁻¹ := by group
      _ = 1 := by rw [h9, h6]; group
  exact ⟨hab', hcube ha3 h1a, hcube hb3 h2b⟩

theorem exists_lift_nine {N Γ : Type*} [Group N] [Finite N] [Group Γ] (f : N →* Γ)
    {R : Subgroup N} {P : Subgroup Γ} (hRP : R.map f = P) (hP : Nat.card P = 9)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hker : ∀ r ∈ R, f r = 1 → ∃ k : ℕ, r ^ 2 ^ k = 1) :
    ∃ Y : Subgroup N, Y ≤ R ∧ Nat.card Y = 9 ∧ (∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y) ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ∀ y ∈ Y, f y ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 2 ∣ Nat.card R := by
    have h := Subgroup.card_map_dvd (H := R) f
    rw [hRP, hP] at h
    simpa using h
  obtain ⟨Y', hY'⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set Y : Subgroup N := Y'.map R.subtype with hYdef
  have hYc : Nat.card Y = 9 := by
    rw [hYdef, Subgroup.card_map_of_injective R.subtype_injective, hY']
    norm_num
  have hYR : Y ≤ R := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hinj : ∀ y ∈ Y, f y = 1 → y = 1 := by
    intro y hy h1
    obtain ⟨k, hk⟩ := hker y (hYR hy) h1
    have h9 : y ^ 9 = 1 := by
      have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
      rw [hYc] at this
      exact congrArg Subtype.val this
    have hd : orderOf y ∣ Nat.gcd (2 ^ k) 9 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h9)
    have hg : Nat.gcd (2 ^ k) 9 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hfY : ∀ y ∈ Y, f y ∈ P := fun y hy => hRP ▸ ⟨y, hYR hy, rfl⟩
  refine ⟨Y, hYR, hYc, fun y hy z hz => ?_, fun y hy => ?_, hfY⟩
  · have hc := hPc _ (hfY y hy) _ (hfY z hz)
    have h := hinj (y * z * (z * y)⁻¹) (Y.mul_mem (Y.mul_mem hy hz) (Y.inv_mem (Y.mul_mem hz hy)))
      (by rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel])
    exact mul_inv_eq_one.mp h
  · exact hinj (y ^ 3) (Y.pow_mem hy 3) (by rw [map_pow, hP3 _ (hfY y hy)])

end CFSG.Quasithin.H13.S8Five
