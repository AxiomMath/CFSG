module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.StandardType.FrameRoute.UTorus

variable (F : Type) [Field F] (m : ℕ)

@[expose] def scalars : Subgroup (Fin m → Fˣ) := (Pi.constMonoidHom (Fin m) Fˣ).range

abbrev Proj : Type := (Fin m → Fˣ) ⧸ scalars F m

@[expose] def detOne : Subgroup (Fin m → Fˣ) where
  carrier := {t | ∏ i, t i = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Pi.mul_apply, Finset.prod_mul_distrib] at ha hb ⊢
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Pi.inv_apply, Finset.prod_inv_distrib] at ha ⊢
    rw [ha, inv_one]

@[expose] def inner : Subgroup (Proj F m) := (detOne F m).map (QuotientGroup.mk' (scalars F m))

variable {F m}

theorem mem_scalars {t : Fin m → Fˣ} : t ∈ scalars F m ↔ ∃ c : Fˣ, ∀ i, t i = c := by
  rw [scalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun _ => rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun i => (hc i).symm⟩

theorem mem_detOne {t : Fin m → Fˣ} : t ∈ detOne F m ↔ ∏ i, t i = 1 :=
  Iff.rfl

private lemma card_scalars [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) :
    Nat.card (scalars F m) = 3 := by
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hInj : Function.Injective (Pi.constMonoidHom (Fin m) Fˣ) := by
    intro a b hab
    simpa using congrFun hab ⟨0, by omega⟩
  rw [scalars, ← Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv, hunits]

private lemma detOne_card [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) :
    Nat.card (detOne F m) = 3 ^ (m - 1) := by
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hG : Nat.card (Fin m → Fˣ) = 3 ^ m := by
    rw [Nat.card_fun, Nat.card_fin, hunits]
  let π : (Fin m → Fˣ) →* Fˣ :=
    MonoidHom.mk' (fun t => ∏ i, t i) (fun a b => Finset.prod_mul_distrib)
  have hker : detOne F m = π.ker := by ext t; rfl
  have hsurj : Function.Surjective π := by
    intro c
    refine ⟨Pi.mulSingle ⟨0, by omega⟩ c, ?_⟩
    simp [π, Finset.prod_pi_mulSingle']
  rw [hker]
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := π) hsurj
  rw [hunits, hG] at hcard
  have h3m : 3 ^ m = 3 ^ (m - 1) * 3 := by
    rw [← pow_sub_one_mul (by omega : m ≠ 0) (3 : ℕ)]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (hcard.trans h3m)

private lemma card_inner_mul [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) :
    Nat.card (inner F m) * Nat.card ((scalars F m).subgroupOf (detOne F m)) =
      3 ^ (m - 1) := by
  have hdet : Nat.card (detOne F m) = 3 ^ (m - 1) := detOne_card hF hm
  let ρ : ↥(detOne F m) →* Proj F m :=
    (QuotientGroup.mk' (scalars F m)).comp (detOne F m).subtype
  have hρrange : ρ.range = inner F m := by
    dsimp only [ρ]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hρker : ρ.ker = (scalars F m).subgroupOf (detOne F m) := by
    ext x
    change (QuotientGroup.mk' (scalars F m) (x : Fin m → Fˣ) = 1) ↔
      x ∈ (scalars F m).subgroupOf (detOne F m)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hρrange, hρker, hdet, mul_comm] at hcard
  exact hcard

theorem card_proj [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) :
    Nat.card (Proj F m) = 3 ^ (m - 1) := by
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hG : Nat.card (Fin m → Fˣ) = 3 ^ m := by
    rw [Nat.card_fun, Nat.card_fin, hunits]
  have hH : Nat.card (scalars F m) = 3 := card_scalars hF hm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars F m)
  rw [hG, hH] at h
  have h3m : 3 ^ m = 3 ^ (m - 1) * 3 := by
    rw [← pow_sub_one_mul (by omega : m ≠ 0) (3 : ℕ)]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.symm.trans h3m)

theorem card_inner_of_not_dvd [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) (h3 : ¬ 3 ∣ m) :
    Nat.card (inner F m) = 3 ^ (m - 1) := by
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hker : (scalars F m).subgroupOf (detOne F m) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_subgroupOf, mem_scalars] at hx
    obtain ⟨c, hc⟩ := hx
    have hc3 : c ^ 3 = 1 := by rw [← hunits]; exact pow_card_eq_one'
    have hcm : c ^ m = 1 := by
      let t : Fin m → Fˣ := (x : ↥(detOne F m))
      have hxdet : ∏ i, t i = 1 := (x : ↥(detOne F m)).2
      rw [← Fin.prod_const m c, ← hxdet]
      exact Finset.prod_congr rfl fun i _ => (hc i).symm
    have hcop : Nat.Coprime 3 m :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hc3, hcm⟩
    apply Subtype.ext
    funext i
    rw [hc i, hc1]
    rfl
  have h := card_inner_mul hF hm
  rw [hker, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_inner_of_dvd [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m) (h3 : 3 ∣ m) :
    Nat.card (inner F m) = 3 ^ (m - 2) := by
  have hle : scalars F m ≤ detOne F m := by
    intro t ht
    rw [mem_scalars] at ht
    obtain ⟨c, hc⟩ := ht
    rw [mem_detOne]
    have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    have hc3 : c ^ 3 = 1 := by rw [← hunits]; exact pow_card_eq_one'
    obtain ⟨k, hk⟩ := h3
    have htc : ∏ i, t i = c ^ m := by
      rw [← Fin.prod_const m c]
      exact Finset.prod_congr rfl fun i _ => hc i
    rw [htc, hk, pow_mul, hc3, one_pow]
  have hker3 : Nat.card ((scalars F m).subgroupOf (detOne F m)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_scalars hF hm]
  have h := card_inner_mul hF hm
  rw [hker3] at h
  have h3m : 3 ≤ m := by
    obtain ⟨k, hk⟩ := h3
    omega
  have h3m1 : 3 ^ (m - 1) = 3 ^ (m - 2) * 3 := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans h3m1)

theorem eq_inner_or_eq_top [Finite F] (hF : Nat.card F = 4) (hm : 1 ≤ m)
    {B : Subgroup (Proj F m)} (hB : inner F m ≤ B) : B = inner F m ∨ B = ⊤ := by
  by_cases h3 : 3 ∣ m
  · have hinner : Nat.card (inner F m) = 3 ^ (m - 2) := card_inner_of_dvd hF hm h3
    have hproj : Nat.card (Proj F m) = 3 ^ (m - 1) := card_proj hF hm
    have hdvd1 : Nat.card (inner F m) ∣ Nat.card B := Subgroup.card_dvd_of_le hB
    have hdvd2 : Nat.card B ∣ Nat.card (Proj F m) := Subgroup.card_subgroup_dvd_card B
    rw [hproj] at hdvd2
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
    have hk_ge : m - 2 ≤ k := by
      rw [hinner, hk] at hdvd1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd1
    rcases show k = m - 2 ∨ k = m - 1 by omega with hk' | hk'
    · left
      apply (Subgroup.eq_of_le_of_card_ge hB ?_).symm
      rw [hk, hk', hinner]
    · right
      apply Subgroup.eq_top_of_card_eq B
      rw [hk, hk', hproj]
  · have hinner : Nat.card (inner F m) = 3 ^ (m - 1) := card_inner_of_not_dvd hF hm h3
    have hproj : Nat.card (Proj F m) = 3 ^ (m - 1) := card_proj hF hm
    have htop : inner F m = ⊤ :=
      Subgroup.eq_top_of_card_eq (inner F m) (hinner.trans hproj.symm)
    right
    exact top_le_iff.mp (htop ▸ hB)

end CFSG.StandardType.FrameRoute.UTorus

end
