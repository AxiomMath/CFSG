module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.MulAut

variable {B : Type*} [Group B]

private theorem eq_one_of_mul_self {Y : Subgroup (MulAut B)} (hY : Odd (Nat.card Y))
    {d : MulAut B} (hd : d ∈ Y) (h : d * d = 1) : d = 1 := by
  have h1 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : orderOf d ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hd
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · rw [h3] at h2
    obtain ⟨k, hk⟩ := h2
    obtain ⟨m, hm⟩ := hY
    omega

private theorem eq_one_of_fix {S : Set B} (hS : Subgroup.closure S = ⊤) {f : MulAut B}
    (h : ∀ x ∈ S, f x = x) : f = 1 := by
  have e : f.toMonoidHom = MonoidHom.id B :=
    MonoidHom.eq_of_eqOn_dense hS fun x hx => h x hx
  ext x
  exact DFunLike.congr_fun e x

private theorem apply_eq_self_of_sq {g : MulAut B} (hg : Odd (orderOf g)) {x : B}
    (h2 : (g * g) x = x) : g x = x := by
  obtain ⟨m, hm⟩ := hg
  have key : ∀ n : ℕ, ((g * g) ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, h2, ih]
  have hg' : (g * g) ^ (m + 1) = g := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [← hg']
  exact key _

theorem apply_eq_self_of_odd {g : MulAut B} (hg : Odd (orderOf g)) {x : B} (hx : x ^ 3 = 1)
    {k : ℤ} (hk : g x = x ^ k) : g x = x := by
  have hx' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [zpow_eq_zpow_emod k hx'] at hk
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with hr | hr | hr <;> rw [hr] at hk
  · rw [zpow_zero] at hk
    have hx1 : x = 1 := g.injective (by rw [hk, map_one])
    rw [hk, hx1]
  · rwa [zpow_one] at hk
  · have hinv : g x = x⁻¹ := by
      rw [hk, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 from rfl]
      exact hx'
    exact apply_eq_self_of_sq hg (by rw [MulAut.mul_apply, hinv, map_inv, hinv, inv_inv])

theorem commute_of_pm {S : Set B} (hS : Subgroup.closure S = ⊤) {Y : Subgroup (MulAut B)}
    (hY : Odd (Nat.card Y)) {t g : MulAut B} (hg : g ∈ Y) (htY : t * g * t⁻¹ ∈ Y)
    (ht : ∀ x ∈ S, t x = x ∨ t x = x⁻¹) (hgt : ∀ x ∈ S, t (g x) = g x ∨ t (g x) = (g x)⁻¹) :
    t * g = g * t := by
  set d := g⁻¹ * (t * g * t⁻¹) with hd
  have hdY : d ∈ Y := mul_mem (inv_mem hg) htY
  have hdx : ∀ x ∈ S, d x = x ∨ d x = x⁻¹ := by
    intro x hx
    have hti : t⁻¹ x = x ∨ t⁻¹ x = x⁻¹ := by
      rcases ht x hx with h | h
      · left
        conv_lhs => rw [← h]
        exact MulAut.inv_apply_self _ t x
      · right
        have h' : t x⁻¹ = x := by rw [map_inv, h, inv_inv]
        conv_lhs => rw [← h']
        exact MulAut.inv_apply_self _ t _
    have happ : d x = g⁻¹ (t (g (t⁻¹ x))) := by
      simp only [hd, MulAut.mul_apply]
    rw [happ]
    rcases hti with h | h <;> rw [h] <;> rcases hgt x hx with h' | h'
    · left; rw [h', MulAut.inv_apply_self]
    · right; rw [h', map_inv, MulAut.inv_apply_self]
    · right; rw [map_inv, map_inv, h', map_inv, MulAut.inv_apply_self]
    · left; rw [map_inv, map_inv, h', inv_inv, MulAut.inv_apply_self]
  have hdd : d * d = 1 := by
    refine eq_one_of_fix hS fun x hx => ?_
    rw [MulAut.mul_apply]
    rcases hdx x hx with h | h
    · rw [h, h]
    · rw [h, map_inv, h, inv_inv]
  have hd1 : d = 1 := eq_one_of_mul_self hY hdY hdd
  have e : t * g * t⁻¹ = g := (inv_mul_eq_one.mp (hd ▸ hd1)).symm
  rwa [mul_inv_eq_iff_eq_mul] at e

private theorem eq_one_of_commute {t g : MulAut B} (h3 : ∀ z : B, z ^ 3 = 1)
    (hc : t * g = g * t) {x y : B} (htx : t x = x⁻¹) (hty : t y = y) {k : ℤ}
    (hy : g x = y ^ k) : x = 1 := by
  have h1 : t (g x) = (g x)⁻¹ := by
    have e := DFunLike.congr_fun hc x
    rw [MulAut.mul_apply, MulAut.mul_apply] at e
    rw [e, htx, map_inv]
  have h2 : t (g x) = g x := by rw [hy, map_zpow, hty]
  have hz : g x * g x = 1 := by
    rw [mul_eq_one_iff_eq_inv]
    exact h2.symm.trans h1
  have hz1 : g x = 1 := by
    have e : g x ^ 3 = g x := by rw [pow_three', hz, one_mul]
    rw [← e, h3]
  exact (MulEquiv.map_eq_one_iff g).mp hz1

private theorem pm_zpow {t : MulAut B} {y : B} (h : t y = y ∨ t y = y⁻¹) (k : ℤ) :
    t (y ^ k) = y ^ k ∨ t (y ^ k) = (y ^ k)⁻¹ := by
  rw [map_zpow]
  rcases h with h | h
  · left; rw [h]
  · right; rw [h, inv_zpow]

variable {b b₁ b₂ b₃ : B}

private theorem pm_of_sign {t g : MulAut B} (htb : t b = b)
    (ht : ∀ y ∈ ({b₁, b₂, b₃} : Set B), t y = y ∨ t y = y⁻¹)
    (hgb : g b = b ∨ g b = b⁻¹)
    (hgl : ∀ x ∈ ({b₁, b₂, b₃} : Set B), ∃ y ∈ ({b₁, b₂, b₃} : Set B), ∃ k : ℤ, g x = y ^ k) :
    (∀ x ∈ ({b, b₁, b₂, b₃} : Set B), t x = x ∨ t x = x⁻¹) ∧
      ∀ x ∈ ({b, b₁, b₂, b₃} : Set B), t (g x) = g x ∨ t (g x) = (g x)⁻¹ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases hx with rfl | hx
    · exact Or.inl htb
    · exact ht x hx
  · rcases hx with rfl | hx
    · left
      rcases hgb with h | h <;> rw [h]
      · exact htb
      · rw [map_inv, htb]
    · obtain ⟨y, hy, k, hk⟩ := hgl x hx
      rw [hk]
      exact pm_zpow (ht y hy) k

theorem eq_one_of_mem_odd_of_lines (h3 : ∀ x : B, x ^ 3 = 1)
    (hgen : Subgroup.closure ({b, b₁, b₂, b₃} : Set B) = ⊤)
    {Y : Subgroup (MulAut B)} (hY : Odd (Nat.card Y)) {t₁ t₂ t₃ : MulAut B}
    (hn₁ : t₁ ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (hn₂ : t₂ ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (hn₃ : t₃ ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (ht₁ : t₁ b = b ∧ t₁ b₁ = b₁⁻¹ ∧ t₁ b₂ = b₂ ∧ t₁ b₃ = b₃)
    (ht₂ : t₂ b = b ∧ t₂ b₁ = b₁ ∧ t₂ b₂ = b₂⁻¹ ∧ t₂ b₃ = b₃)
    (ht₃ : t₃ b = b ∧ t₃ b₁ = b₁ ∧ t₃ b₂ = b₂ ∧ t₃ b₃ = b₃⁻¹)
    {g : MulAut B} (hg : g ∈ Y) (hgb : g b = b ∨ g b = b⁻¹)
    (hgl : ∀ x ∈ ({b₁, b₂, b₃} : Set B), ∃ y ∈ ({b₁, b₂, b₃} : Set B), ∃ k : ℤ, g x = y ^ k) :
    g = 1 := by
  have hodd : Odd (orderOf g) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hg)
  have hcomm : ∀ t : MulAut B, t ∈ Subgroup.normalizer (Y : Set (MulAut B)) → t b = b →
      (∀ y ∈ ({b₁, b₂, b₃} : Set B), t y = y ∨ t y = y⁻¹) → t * g = g * t := by
    intro t hn htb ht
    obtain ⟨hS, hgS⟩ := pm_of_sign htb ht hgb hgl
    exact commute_of_pm hgen hY hg ((Subgroup.mem_normalizer_iff.mp hn g).mp hg) hS hgS
  have hc₁ := hcomm t₁ hn₁ ht₁.1 (by
    rintro y (rfl | rfl | rfl)
    exacts [Or.inr ht₁.2.1, Or.inl ht₁.2.2.1, Or.inl ht₁.2.2.2])
  have hc₂ := hcomm t₂ hn₂ ht₂.1 (by
    rintro y (rfl | rfl | rfl)
    exacts [Or.inl ht₂.2.1, Or.inr ht₂.2.2.1, Or.inl ht₂.2.2.2])
  have hc₃ := hcomm t₃ hn₃ ht₃.1 (by
    rintro y (rfl | rfl | rfl)
    exacts [Or.inl ht₃.2.1, Or.inl ht₃.2.2.1, Or.inr ht₃.2.2.2])
  have hfix : ∀ x ∈ ({b₁, b₂, b₃} : Set B), ∀ t : MulAut B, t * g = g * t → t x = x⁻¹ →
      (∀ y ∈ ({b₁, b₂, b₃} : Set B), y ≠ x → t y = y) → g x = x := by
    intro x hx t hc htx hty
    obtain ⟨y, hy, k, hk⟩ := hgl x hx
    by_cases hxy : y = x
    · rw [hxy] at hk
      exact apply_eq_self_of_odd hodd (h3 x) hk
    · have hx1 := eq_one_of_commute h3 hc htx (hty y hy hxy) hk
      rw [hx1, map_one]
  have hg₁ : g b₁ = b₁ := by
    refine hfix b₁ (by simp) t₁ hc₁ ht₁.2.1 ?_
    rintro y (rfl | rfl | rfl) hne
    exacts [absurd rfl hne, ht₁.2.2.1, ht₁.2.2.2]
  have hg₂ : g b₂ = b₂ := by
    refine hfix b₂ (by simp) t₂ hc₂ ht₂.2.2.1 ?_
    rintro y (rfl | rfl | rfl) hne
    exacts [ht₂.2.1, absurd rfl hne, ht₂.2.2.2]
  have hg₃ : g b₃ = b₃ := by
    refine hfix b₃ (by simp) t₃ hc₃ ht₃.2.2.2 ?_
    rintro y (rfl | rfl | rfl) hne
    exacts [ht₃.2.1, ht₃.2.2.1, absurd rfl hne]
  have hg₀ : g b = b := by
    rcases hgb with h | h
    · exact h
    · exact apply_eq_self_of_odd hodd (h3 b) (k := -1) (by rw [h, zpow_neg_one])
  refine eq_one_of_fix hgen fun x hx => ?_
  rcases hx with rfl | rfl | rfl | rfl
  exacts [hg₀, hg₁, hg₂, hg₃]

private theorem inv_apply_of_apply {f : MulAut B} {x y : B} (h : f x = y) : f⁻¹ y = x := by
  rw [← h, MulAut.inv_apply_self]

theorem eq_one_of_mem_odd_of_lines_H0 (h3 : ∀ x : B, x ^ 3 = 1)
    (hgen : Subgroup.closure ({b, b₁, b₂, b₃} : Set B) = ⊤)
    {Y : Subgroup (MulAut B)} (hY : Odd (Nat.card Y)) {t₁ s c : MulAut B}
    (hn₁ : t₁ ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (hns : s ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (hnc : c ∈ Subgroup.normalizer (Y : Set (MulAut B)))
    (ht₁ : t₁ b = b ∧ t₁ b₁ = b₁⁻¹ ∧ t₁ b₂ = b₂ ∧ t₁ b₃ = b₃)
    (hs : s b = b ∧ s b₁ = b₂ ∧ s b₂ = b₁ ∧ s b₃ = b₃)
    (hc : c b = b ∧ c b₁ = b₂ ∧ c b₂ = b₃ ∧ c b₃ = b₁)
    {g : MulAut B} (hg : g ∈ Y) (hgb : g b = b ∨ g b = b⁻¹)
    (hgl : ∀ x ∈ ({b₁, b₂, b₃} : Set B), ∃ y ∈ ({b₁, b₂, b₃} : Set B), ∃ k : ℤ, g x = y ^ k) :
    g = 1 := by
  obtain ⟨t1b, t11, t12, t13⟩ := ht₁
  obtain ⟨sb, s1, s2, s3⟩ := hs
  obtain ⟨cb, c1, c2, c3⟩ := hc
  have sib := inv_apply_of_apply sb
  have si1 := inv_apply_of_apply s2
  have si2 := inv_apply_of_apply s1
  have si3 := inv_apply_of_apply s3
  have cib := inv_apply_of_apply cb
  have ci1 := inv_apply_of_apply c3
  have ci2 := inv_apply_of_apply c1
  have ci3 := inv_apply_of_apply c2
  set t₂ := s * t₁ * s⁻¹ with ht₂def
  have ht₂ : t₂ b = b ∧ t₂ b₁ = b₁ ∧ t₂ b₂ = b₂⁻¹ ∧ t₂ b₃ = b₃ := by
    simp only [ht₂def, MulAut.mul_apply]
    rw [sib, t1b, sb, si1, t12, s2, si2, t11, map_inv, s1, si3, t13, s3]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨t2b, t21, t22, t23⟩ := ht₂
  refine eq_one_of_mem_odd_of_lines h3 hgen hY (t₁ := t₁) (t₂ := t₂) (t₃ := c * t₂ * c⁻¹)
    hn₁ (mul_mem (mul_mem hns hn₁) (inv_mem hns)) (mul_mem (mul_mem hnc
      (mul_mem (mul_mem hns hn₁) (inv_mem hns))) (inv_mem hnc))
    ⟨t1b, t11, t12, t13⟩ ⟨t2b, t21, t22, t23⟩ ?_ hg hgb hgl
  simp only [MulAut.mul_apply]
  rw [cib, t2b, cb, ci1, t23, c3, ci2, t21, c1, ci3, t22, map_inv, c2]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem eq_one_of_mem_oddNormal_of_lines_H0 (h3 : ∀ x : B, x ^ 3 = 1)
    (hgen : Subgroup.closure ({b, b₁, b₂, b₃} : Set B) = ⊤)
    {X : Subgroup (MulAut B)} {Y : Subgroup X} [Y.Normal] (hY : Odd (Nat.card Y))
    {t₁ s c : MulAut B} (ht₁X : t₁ ∈ X) (hsX : s ∈ X) (hcX : c ∈ X)
    (ht₁ : t₁ b = b ∧ t₁ b₁ = b₁⁻¹ ∧ t₁ b₂ = b₂ ∧ t₁ b₃ = b₃)
    (hs : s b = b ∧ s b₁ = b₂ ∧ s b₂ = b₁ ∧ s b₃ = b₃)
    (hc : c b = b ∧ c b₁ = b₂ ∧ c b₂ = b₃ ∧ c b₃ = b₁)
    {g : X} (hg : g ∈ Y) (hgb : (g : MulAut B) b = b ∨ (g : MulAut B) b = b⁻¹)
    (hgl : ∀ x ∈ ({b₁, b₂, b₃} : Set B), ∃ y ∈ ({b₁, b₂, b₃} : Set B), ∃ k : ℤ,
      (g : MulAut B) x = y ^ k) :
    g = 1 := by
  have hnorm : ∀ {t : MulAut B}, t ∈ X →
      t ∈ Subgroup.normalizer ((Y.map X.subtype : Subgroup (MulAut B)) : Set (MulAut B)) := by
    intro t ht
    have hmem : (⟨t, ht⟩ : X) ∈ Subgroup.normalizer (Y : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    exact Subgroup.le_normalizer_map X.subtype ⟨⟨t, ht⟩, hmem, rfl⟩
  have hY' : Odd (Nat.card (Y.map X.subtype)) := by
    rwa [Subgroup.card_map_of_injective X.subtype_injective]
  have h := eq_one_of_mem_odd_of_lines_H0 h3 hgen hY' (hnorm ht₁X) (hnorm hsX) (hnorm hcX)
    ht₁ hs hc ⟨g, hg, rfl⟩ hgb hgl
  exact Subtype.ext h

end CFSG.MulAut
