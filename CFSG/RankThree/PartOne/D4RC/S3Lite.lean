module

import CFSG.RankThree.PartOne.D4RC.Burnside
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem rcn_exists_orderOf_eq {p : ℕ} [Fact p.Prime] {B : Subgroup K} (hB : IsPGroup p B)
    (hB1 : B ≠ ⊥) : ∃ b ∈ B, orderOf b = p := by
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hB1 (Subgroup.card_eq_one.1 (by simpa using hn))
  have hdvd : p ∣ Nat.card B := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) p hdvd
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

theorem rcn_exists_normalizer_line {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {S E P Z : Subgroup K}
    (hSp : IsPGroup p S) (hES : E ≤ S) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2)
    (hΩ : ∀ s ∈ S, s ^ p = 1 → s ∈ E) (hPZ : ∀ a ∈ P, ∀ b ∈ Z, a * b = b * a)
    (hperf : ⁅P, P⁆ = P) (hSyl : ¬ p ∣ (S ⊓ P).relIndex P) (hcyc : IsCyclic ↥(S ⊓ P))
    (hP1 : S ⊓ P ≠ ⊥) (hZ1 : S ⊓ Z ≠ ⊥) (hPZ1 : S ⊓ P ⊓ Z = ⊥)
    (hSgen : ∀ s ∈ S, ∃ a ∈ S ⊓ P, ∃ b ∈ S ⊓ Z, s = a * b) :
    ∃ g ∈ P, g ∈ Subgroup.normalizer (S : Set K) ∧
      ∀ ℓ : Subgroup K, ℓ ≤ E → Nat.card ℓ = p → (∀ x ∈ ℓ, g * x * g⁻¹ ∈ ℓ) →
        ℓ = E ⊓ P ∨ ℓ = E ⊓ Z := by
  classical
  have hp : p.Prime := Fact.out
  have hAp : IsPGroup p (S ⊓ P : Subgroup K) := hSp.to_le inf_le_left
  have hBp : IsPGroup p (S ⊓ Z : Subgroup K) := hSp.to_le inf_le_left
  obtain ⟨g, hgP, hgN, a₀, ha₀A, ha₀p, hga₀⟩ :=
    rcb_exists_normalizer_elt hp2 hperf inf_le_right hAp hSyl hcyc hP1
  have hgA : ∀ h ∈ S ⊓ P, g * h * g⁻¹ ∈ S ⊓ P := fun h hh =>
    (Subgroup.mem_normalizer_iff.1 hgN h).1 hh
  have hgA' : ∀ h ∈ S ⊓ P, g⁻¹ * h * g ∈ S ⊓ P := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.1 hgN (g⁻¹ * h * g)).2
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rw [e] at this
    exact this hh
  have hcomm : ∀ c ∈ P, ∀ b ∈ Z, c * b * c⁻¹ = b := fun c hc b hb => by
    rw [hPZ c hc b hb]
    group
  have hgP' : g⁻¹ ∈ P := P.inv_mem hgP
  have hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hSgen s hs
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e, hcomm g hgP b hb.2]
    exact S.mul_mem (hgA a ha).1 hb.1
  have hgS' : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hSgen s hs
    have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    have e2 : g⁻¹ * b * g = b := by
      have := hcomm g⁻¹ hgP' b hb.2
      simpa using this
    rw [e, e2]
    exact S.mul_mem (hgA' a ha).1 hb.1
  have hgNS : g ∈ Subgroup.normalizer (S : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hgS s hs, fun hs => ?_⟩
    have := hgS' _ hs
    have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    rw [e] at this
    exact this
  refine ⟨g, hgP, hgNS, ?_⟩
  have hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun e he => by
    refine hΩ _ (hgS e (hES he)) ?_
    rw [conj_pow, hEp e he]
    group
  have hdec : ∀ e ∈ E, ∃ a ∈ E ⊓ P, ∃ b ∈ E ⊓ Z, e = a * b := fun e he => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hSgen e (hES he)
    have hcab : Commute a b := hPZ a ha.2 b hb.2
    have h1 : a ^ p * b ^ p = 1 := by rw [← hcab.mul_pow]; exact hEp _ he
    have h2 : a ^ p = 1 := by
      have hmem : a ^ p ∈ S ⊓ P ⊓ Z := by
        refine ⟨⟨S.pow_mem ha.1 p, P.pow_mem ha.2 p⟩, ?_⟩
        have : a ^ p = (b ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact Z.inv_mem (Z.pow_mem hb.2 p)
      rw [hPZ1, Subgroup.mem_bot] at hmem
      exact hmem
    have h3 : b ^ p = 1 := by rw [h2, one_mul] at h1; exact h1
    exact ⟨a, ⟨hΩ a ha.1 h2, ha.2⟩, b, ⟨hΩ b hb.1 h3, hb.2⟩, rfl⟩
  have hmz : (E ⊓ P) ⊓ (E ⊓ Z) = ⊥ := by
    rw [eq_bot_iff, ← hPZ1]
    intro x hx
    exact ⟨⟨hES hx.1.1, hx.1.2⟩, hx.2.2⟩
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    exact hga₀ (by group)
  have ha₀E : a₀ ∈ E := hΩ a₀ ha₀A.1 ha₀p
  have hm1 : E ⊓ P ≠ ⊥ := fun h => ha₀1 (by
    have : a₀ ∈ E ⊓ P := ⟨ha₀E, ha₀A.2⟩
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hz1 : E ⊓ Z ≠ ⊥ := by
    obtain ⟨b, hb, hbo⟩ := rcn_exists_orderOf_eq hBp hZ1
    intro h
    have hbp : b ^ p = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
    have : b ∈ E ⊓ Z := ⟨hΩ b hb.1 hbp, hb.2⟩
    rw [h, Subgroup.mem_bot] at this
    have : orderOf b = 1 := by rw [this]; exact orderOf_one
    rw [hbo] at this
    exact hp.one_lt.ne' this
  have hcardE : ∀ H : Subgroup K, H ≤ E → H ≠ ⊥ → H ≠ E → Nat.card H = p := by
    intro H hHE hH1 hHE'
    have hdvd : Nat.card H ∣ p ^ 2 := hEc ▸ Subgroup.card_dvd_of_le hHE
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hH1 (Subgroup.card_eq_one.1 (by simpa using hi'))
    have hi2 : i ≠ 2 := by
      rintro rfl
      exact hHE' (Subgroup.eq_of_le_of_card_ge hHE (by rw [hi', hEc]))
    have : i = 1 := by omega
    rw [hi', this, pow_one]
  have hmE : E ⊓ P ≠ E := fun h => hz1 (by
    rw [eq_bot_iff, ← hmz]
    intro x hx
    refine ⟨?_, hx⟩
    rw [h]
    exact hx.1)
  have hzE : E ⊓ Z ≠ E := fun h => hm1 (by
    rw [eq_bot_iff, ← hmz]
    intro x hx
    refine ⟨hx, ?_⟩
    rw [h]
    exact hx.1)
  have hmcard : Nat.card (E ⊓ P : Subgroup K) = p := hcardE _ inf_le_left hm1 hmE
  have hzcard : Nat.card (E ⊓ Z : Subgroup K) = p := hcardE _ inf_le_left hz1 hzE
  have hgm : ∀ a ∈ E ⊓ P, g * a * g⁻¹ ∈ E ⊓ P := fun a ha =>
    ⟨hgE a ha.1, (hgA a ⟨hES ha.1, ha.2⟩).2⟩
  intro ℓ hℓE hℓc hℓg
  have hℓ1 : ℓ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hℓc
    exact hp.one_lt.ne hℓc
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hℓ1
  have hxℓ : (y : K) ∈ ℓ := y.2
  have hx1 : (y : K) ≠ 1 := fun h => hy (Subtype.ext h)
  generalize (y : K) = x at hxℓ hx1
  have hxE : x ∈ E := hℓE hxℓ
  have hxp : orderOf x = p := by
    refine ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hEp x hxE))).resolve_left ?_
    intro h
    exact hx1 (orderOf_eq_one_iff.1 h)
  have hℓx : ℓ = zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxℓ) ?_).symm
    rw [hℓc, Nat.card_zpowers, hxp]
  obtain ⟨a, ham, b, hbz, rfl⟩ := hdec x hxE
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hℓx ▸ hℓg _ hxℓ)
  have hcab : Commute a b := hPZ a ham.2 b hbz.2
  have hga : g * a * g⁻¹ ∈ E ⊓ P := hgm a ham
  have hgb : g * b * g⁻¹ = b := hcomm g hgP b hbz.2
  have hgx : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * b := by
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e, hgb]
  rw [hgx, hcab.mul_zpow j] at hj
  have huniq : ∀ (a₁ a₂ : K) (b₁ b₂ : K), a₁ ∈ E ⊓ P → a₂ ∈ E ⊓ P → b₁ ∈ E ⊓ Z → b₂ ∈ E ⊓ Z →
      a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h
    have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
        _ = b₂ * b₁⁻¹ := by group
    have h2 : a₂⁻¹ * a₁ ∈ (E ⊓ P) ⊓ (E ⊓ Z) :=
      ⟨(E ⊓ P).mul_mem ((E ⊓ P).inv_mem ha₂) ha₁,
        h1 ▸ (E ⊓ Z).mul_mem hb₂ ((E ⊓ Z).inv_mem hb₁)⟩
    rw [hmz, Subgroup.mem_bot] at h2
    have h3 : a₁ = a₂ := (inv_mul_eq_one.1 h2).symm
    refine ⟨h3, ?_⟩
    rw [h3] at h
    exact mul_left_cancel h
  obtain ⟨hja, hjb⟩ := huniq _ _ _ _ hga (Subgroup.zpow_mem _ ham j) hbz
    (Subgroup.zpow_mem _ hbz j) hj.symm
  have hgen : ∀ H : Subgroup K, Nat.card H = p → ∀ c ∈ H, c ≠ 1 → zpowers c = H := by
    intro H hH c hc hc1
    have hco : orderOf c = p := by
      have hdvd : orderOf c ∣ p := hH ▸ Subgroup.orderOf_dvd_natCard H hc
      exact ((Nat.dvd_prime hp).1 hdvd).resolve_left fun h => hc1 (orderOf_eq_one_iff.1 h)
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc)
      (by rw [hH, Nat.card_zpowers, hco])
  by_cases hb1 : b = 1
  · left
    have hℓa : ℓ = zpowers a := by rw [hℓx, hb1, mul_one]
    rw [hℓa]
    by_cases ha1 : a = 1
    · exfalso
      apply hx1
      rw [ha1, hb1, one_mul]
    · exact hgen _ hmcard a ham ha1
  · right
    have hbE : b ∈ E := hbz.1
    have hbord : orderOf b = p := by
      refine ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hEp b hbE))).resolve_left ?_
      intro h
      exact hb1 (orderOf_eq_one_iff.1 h)
    have hpj : (p : ℤ) ∣ j - 1 := by
      have h1 : b ^ (j - 1) = 1 := by rw [zpow_sub_one, ← hjb, mul_inv_cancel]
      have := (orderOf_dvd_iff_zpow_eq_one (x := b) (i := j - 1)).2 h1
      rwa [hbord] at this
    obtain ⟨t, ht⟩ := hpj
    have haj : a ^ j = a := by
      have : j = 1 + (p : ℤ) * t := by omega
      rw [this, zpow_add, zpow_one, zpow_mul, zpow_natCast, hEp a ham.1, one_zpow, mul_one]
    rw [haj] at hja
    have ha1 : a = 1 := by
      by_contra ha1
      have hma : zpowers a = E ⊓ P := hgen _ hmcard a ham ha1
      have ha₀m : a₀ ∈ zpowers a := hma ▸ (⟨ha₀E, ha₀A.2⟩ : a₀ ∈ E ⊓ P)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha₀m
      apply hga₀
      rw [← hk, ← conj_zpow, hja]
    have hℓb : ℓ = zpowers b := by rw [hℓx, ha1, one_mul]
    rw [hℓb]
    exact hgen _ hzcard b hbz hb1

end CFSG.RankThree.PartOne.D4RC
