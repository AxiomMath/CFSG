module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS

open Subgroup
open scoped commutatorElement

variable {S : Type*} [Group S]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup S}
    (hAB : A ≤ normalizer (B : Set S)) :
    Nat.card (A ⊔ B : Subgroup S) * Nat.card (A ⊓ B : Subgroup S) =
      Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup S) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_conj_ne {D R : Subgroup S} (hDR : D ≤ normalizer (R : Set S))
    (hinf : D ⊓ R = ⊥) (hc : ⁅D, R⁆ ≠ ⊥) :
    ∃ r ∈ R, D.map (MulAut.conj r).toMonoidHom ≠ D := by
  by_contra h
  push Not at h
  apply hc
  rw [eq_bot_iff, ← hinf]
  refine le_inf ?_ ?_
  · rw [commutator_le]
    intro d hd r hr
    have hm : (MulAut.conj r) d⁻¹ ∈ D.map (MulAut.conj r).toMonoidHom := ⟨d⁻¹, D.inv_mem hd, rfl⟩
    rw [h r hr] at hm
    have hm' : r * d⁻¹ * r⁻¹ ∈ D := by simpa using hm
    have : ⁅d, r⁆ = d * (r * d⁻¹ * r⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact D.mul_mem hd hm'
  · rw [commutator_le]
    intro d hd r hr
    have hm : d * r * d⁻¹ ∈ R := (mem_normalizer_iff.1 (hDR hd) r).1 hr
    have : ⁅d, r⁆ = (d * r * d⁻¹) * r⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact R.mul_mem hm (R.inv_mem hr)

theorem exists_pair_card_odd [Finite S] {D R : Subgroup S} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hD : Nat.card D = 3) (hR : IsPGroup ℓ R)
    (hDR : D ≤ normalizer (R : Set S)) (hc : ⁅D, R⁆ ≠ ⊥) :
    ∃ g : S, Odd (Nat.card (D ⊔ D.map (MulAut.conj g).toMonoidHom : Subgroup S)) ∧
      Nat.card (D ⊔ D.map (MulAut.conj g).toMonoidHom : Subgroup S) ≠ 3 ∧
      Nat.card (D ⊔ D.map (MulAut.conj g).toMonoidHom : Subgroup S) ≠ 9 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by rw [hD, pow_one])
  have hinf : D ⊓ R = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_coprime hD3 hR
      ((Nat.coprime_primes Nat.prime_three hℓ).2 (Ne.symm hℓ3)))
  obtain ⟨r, hr, hne⟩ := exists_conj_ne hDR hinf hc
  refine ⟨r, ?_⟩
  set Dg := D.map (MulAut.conj r).toMonoidHom with hDg
  have hcardDg : Nat.card Dg = 3 := by
    rw [hDg, Subgroup.card_map_of_injective (MulAut.conj r).injective, hD]
  have hle : D ⊔ Dg ≤ R ⊔ D := by
    refine sup_le le_sup_right ?_
    rintro _ ⟨y, hy, rfl⟩
    change r * y * r⁻¹ ∈ R ⊔ D
    have h1 : y * r⁻¹ * y⁻¹ ∈ R := (mem_normalizer_iff.1 (hDR hy) r⁻¹).1 (R.inv_mem hr)
    have h2 : r * y * r⁻¹ = (r * (y * r⁻¹ * y⁻¹)) * y := by group
    rw [h2]
    exact Subgroup.mul_mem_sup (R.mul_mem hr h1) hy
  have hcardRD : Nat.card (R ⊔ D : Subgroup S) = Nat.card R * 3 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hDR
    rw [hinf, Subgroup.card_bot, mul_one, hD, sup_comm] at h
    rw [h, mul_comm]
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : Nat.card ↥(D ⊔ Dg) ∣ ℓ ^ k * 3 := by
    rw [← hk, ← hcardRD]
    exact Subgroup.card_dvd_of_le hle
  have hodd : Odd (ℓ ^ k * 3) := (hℓ.odd_of_ne_two hℓ2).pow.mul (by decide)
  refine ⟨hodd.of_dvd_nat hdvd, ?_, ?_⟩
  · intro h3
    have hD' : D = D ⊔ Dg :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hD])
    have hDg' : Dg = D ⊔ Dg :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hcardDg])
    exact hne (hDg'.trans hD'.symm)
  · intro h9
    rw [h9] at hdvd
    have h3 : 3 ∣ ℓ ^ k := by
      have : 3 * 3 ∣ ℓ ^ k * 3 := by simpa using hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    exact hℓ3 this.symm

end CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS
