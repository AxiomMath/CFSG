module

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1617

theorem mul_eq_mul_of_mem_normalizer_zpowers {G : Type*} [Group G] {c t : G}
    (hc : Nat.card (Subgroup.zpowers c) = 3) (ht3 : t ^ 3 = 1)
    (ht : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : t * c = c * t := by
  have hoc : orderOf c = 3 := by rw [← Nat.card_zpowers]; exact hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp ht c).mp (Subgroup.mem_zpowers c))
  have hconj : ∀ m : ℤ, t * c ^ m * t⁻¹ = c ^ (k * m) := by
    intro m
    have : t * c ^ m * t⁻¹ = (t * c * t⁻¹) ^ m := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [this, ← hk, ← zpow_mul]
  have h3 : t ^ 3 * c * (t ^ 3)⁻¹ = c ^ (k * (k * k)) := by
    have e1 : t ^ 3 * c * (t ^ 3)⁻¹ = t * (t * (t * c ^ (1 : ℤ) * t⁻¹) * t⁻¹) * t⁻¹ := by
      rw [zpow_one, pow_three]; group
    rw [e1, hconj, hconj, hconj, mul_one]
  rw [ht3, one_mul, inv_one, mul_one] at h3
  have hdvd : (3 : ℤ) ∣ k * (k * k) - 1 := by
    have h1 : c ^ (k * (k * k) - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← h3, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hoc] at this
    exact_mod_cast this
  have hk1 : (3 : ℤ) ∣ k - 1 := by
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · exfalso
      have : (k * (k * k) - 1) % 3 = 2 := by
        rw [Int.sub_emod, Int.mul_emod, Int.mul_emod k k, h0]; norm_num
      omega
    · omega
    · exfalso
      have : (k * (k * k) - 1) % 3 = 1 := by
        rw [Int.sub_emod, Int.mul_emod, Int.mul_emod k k, h2]; norm_num
      omega
  have hck : c ^ k = c := by
    obtain ⟨m, hm⟩ := hk1
    have hkm : k = 1 + 3 * m := by omega
    rw [hkm, zpow_add, zpow_one, zpow_mul]
    have : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hoc, pow_orderOf_eq_one]
    rw [this, one_zpow, mul_one]
  calc t * c = t * c * t⁻¹ * t := by group
    _ = c * t := by rw [← hk, hck]

theorem add_sq_eq_zero_of_card_nine {D : Type*} [AddCommGroup D] [Finite D]
    (hD : Nat.card D = 9) (δ : D →+ D) (h3 : ∀ d, δ (δ (δ d)) = 0) (d : D) :
    δ (δ d) = 0 := by
  by_contra hne
  have hns : ¬ Function.Surjective δ := by
    intro hs
    have hinj : Function.Injective δ := Finite.injective_iff_surjective.mpr hs
    have hall : ∀ e : D, e = 0 := fun e =>
      hinj (hinj (hinj (by rw [h3 e, map_zero, map_zero, map_zero])))
    have h1 : Nat.card D = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨0⟩⟩
    omega
  set R := δ.range with hR
  have hRdvd : Nat.card R ∣ 9 := hD ▸ AddSubgroup.card_addSubgroup_dvd_card R
  have hR9 : Nat.card R ≠ 9 := by
    intro h9
    apply hns
    have htop : R = ⊤ := AddSubgroup.eq_top_of_card_eq R (h9.trans hD.symm)
    intro y
    have hy : y ∈ R := htop ▸ AddSubgroup.mem_top y
    exact hy
  have hu : δ (δ d) ∈ R := ⟨δ d, rfl⟩
  have hR1 : Nat.card R ≠ 1 := by
    intro h1
    have hbot : R = ⊥ := AddSubgroup.eq_bot_of_card_eq R h1
    rw [hbot] at hu
    exact hne (AddSubgroup.mem_bot.mp hu)
  have hR3 : Nat.card R = 3 := by
    obtain ⟨i, hi, hiR⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card R ∣ 3 ^ 2 from hRdvd)
    interval_cases i
    · exact absurd hiR hR1
    · exact hiR
    · exact absurd hiR hR9
  have hgen : AddSubgroup.zmultiples (δ (δ d)) = R := by
    have hle : AddSubgroup.zmultiples (δ (δ d)) ≤ R := AddSubgroup.zmultiples_le.mpr hu
    have hcard : Nat.card (AddSubgroup.zmultiples (δ (δ d))) ∣ 3 := by
      rw [← hR3]
      exact AddSubgroup.card_dvd_of_le hle
    have hne1 : Nat.card (AddSubgroup.zmultiples (δ (δ d))) ≠ 1 := by
      intro h1
      have hbot := AddSubgroup.eq_bot_of_card_eq _ h1
      apply hne
      have hmem := AddSubgroup.mem_zmultiples (δ (δ d))
      rw [hbot] at hmem
      exact AddSubgroup.mem_bot.mp hmem
    have h3' : Nat.card (AddSubgroup.zmultiples (δ (δ d))) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h | h
      · exact absurd h hne1
      · exact h
    exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [h3', hR3])
  have hδd : δ d ∈ AddSubgroup.zmultiples (δ (δ d)) := hgen ▸ ⟨d, rfl⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hδd
  apply hne
  rw [← hk, map_zsmul, h3 d, zsmul_zero]

theorem add_norm_eq_zero {D : Type*} [AddCommGroup D] [Finite D] (hD : Nat.card D = 9)
    (hexp : ∀ d : D, 3 • d = 0) (φ : D →+ D) (hφ : ∀ d, φ (φ (φ d)) = d) (d : D) :
    d + φ d + φ (φ d) = 0 := by
  set δ : D →+ D := φ - AddMonoidHom.id D with hδ
  have hδapp : ∀ e, δ e = φ e - e := fun e => rfl
  have h3 : ∀ e, δ (δ (δ e)) = 0 := by
    intro e
    have : δ (δ (δ e)) = φ (φ (φ e)) - 3 • φ (φ e) + 3 • φ e - e := by
      simp only [hδapp, map_sub]
      abel
    rw [this, hφ, hexp, hexp]
    abel
  have h2 := add_sq_eq_zero_of_card_nine hD δ h3 d
  have : d + φ d + φ (φ d) = δ (δ d) + 3 • φ d := by
    simp only [hδapp, map_sub]
    abel
  rw [this, h2, hexp, add_zero]

theorem mul_norm_eq_one {D : Type*} [CommGroup D] [Finite D] (hD : Nat.card D = 9)
    (hexp : ∀ d : D, d ^ 3 = 1) (φ : D →* D) (hφ : ∀ d, φ (φ (φ d)) = d) (d : D) :
    d * φ d * φ (φ d) = 1 := by
  have h := add_norm_eq_zero (D := Additive D) (by rw [Nat.card_congr Additive.ofMul.symm, hD])
    (fun e => by
      change Additive.ofMul ((Additive.toMul e) ^ 3) = Additive.ofMul 1
      rw [hexp])
    (MonoidHom.toAdditive φ) (fun e => hφ (Additive.toMul e)) (Additive.ofMul d)
  exact Additive.ofMul.injective h

theorem mul_conj_mul_conj_eq_one {G : Type*} [Group G] {D : Subgroup G}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDe : ∀ a ∈ D, a ^ 3 = 1) [Finite D]
    (h9 : Nat.card D = 9) {t : G} (htD : t ∈ Subgroup.normalizer (D : Set G)) (ht3 : t ^ 3 = 1)
    {d : G} (hd : d ∈ D) : d * (t * d * t⁻¹) * (t * (t * d * t⁻¹) * t⁻¹) = 1 := by
  let _ : CommGroup D :=
    { (inferInstance : Group D) with
      mul_comm := fun a b => Subtype.ext (hDc a a.2 b b.2) }
  let φ : D →* D :=
    { toFun := fun e => ⟨t * e * t⁻¹, (Subgroup.mem_normalizer_iff.mp htD e).mp e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ e : D, φ (φ (φ e)) = e := by
    intro e
    apply Subtype.ext
    change t * (t * (t * (e : G) * t⁻¹) * t⁻¹) * t⁻¹ = e
    have : t * (t * (t * (e : G) * t⁻¹) * t⁻¹) * t⁻¹ = t ^ 3 * e * (t ^ 3)⁻¹ := by
      rw [pow_three]; group
    rw [this, ht3, one_mul, inv_one, mul_one]
  have h := mul_norm_eq_one h9 (fun e => Subtype.ext (by simpa using hDe e e.2)) φ hφ ⟨d, hd⟩
  exact congrArg Subtype.val h

end CFSG.RankThree.PartTwo.Sec16.Proof1617
