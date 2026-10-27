module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (omegaOne)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

theorem omegaOne_le_center_of_sylow {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (I : Subgroup A) [I.Normal] (S : Sylow p A)
    (hS : omegaOne p ((S : Subgroup A) ⊓ I) ≤ (Subgroup.center S).map (S : Subgroup A).subtype)
    (R : Subgroup A) (hR : IsPGroup p R) :
    omegaOne p (R ⊓ I) ≤ (Subgroup.center R).map R.subtype := by
  obtain ⟨S', hRS'⟩ := hR.exists_le_sylow
  have : MulAction.IsPretransitive A (Sylow p A) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S' S
  have hSg : (S : Subgroup A) = MulAut.conj g • (S' : Subgroup A) := by
    conv_lhs => rw [← hg]
    rfl
  have hmem : ∀ y : A, y ∈ (S' : Subgroup A) → g * y * g⁻¹ ∈ (S : Subgroup A) := by
    intro y hy
    rw [hSg]
    have := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (S' : Subgroup A) hy
    simpa using this
  have key : ∀ x ∈ (S' : Subgroup A) ⊓ I, x ^ p = 1 → ∀ z ∈ (S' : Subgroup A), x * z = z * x := by
    intro x hx hxp z hz
    have hxS : g * x * g⁻¹ ∈ (S : Subgroup A) ⊓ I :=
      ⟨hmem x hx.1, by simpa [mul_assoc] using (inferInstance : I.Normal).conj_mem x hx.2 g⟩
    have hxp' : (g * x * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hxp]; simp
    have hmemΩ : g * x * g⁻¹ ∈ omegaOne p ((S : Subgroup A) ⊓ I) :=
      Subgroup.subset_closure ⟨hxS, hxp'⟩
    obtain ⟨c, hc, hcx⟩ := hS hmemΩ
    have hgz : g * z * g⁻¹ ∈ (S : Subgroup A) := hmem z hz
    have h1 := Subgroup.mem_center_iff.mp hc ⟨g * z * g⁻¹, hgz⟩
    have h2 : (g * z * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * z * g⁻¹) := by
      have hcx' : (c : A) = g * x * g⁻¹ := hcx
      have := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, hcx'] at this
      exact this
    have h3 : g * (z * x) * g⁻¹ = g * (x * z) * g⁻¹ := by
      simpa [mul_assoc] using h2
    exact (mul_left_cancel (mul_right_cancel h3)).symm
  intro y hy
  have hy' : ∀ x ∈ ({x : A | x ∈ R ⊓ I ∧ x ^ p = 1}), x ∈ (Subgroup.center R).map R.subtype := by
    rintro x ⟨⟨hxR, hxI⟩, hxp⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro z
    apply Subtype.ext
    exact (key x ⟨hRS' hxR, hxI⟩ hxp z (hRS' z.2)).symm
  exact (Subgroup.closure_le _ |>.mpr hy') hy

theorem exists_sylow_omegaOne_le_center {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (I : Subgroup A) [I.Normal] (Q : Subgroup A) (hQ : IsSylowOf p Q I)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (τ : A) (s : ℕ) (hs : s % p = 1)
    (hτ : ∀ x ∈ Q, τ * x * τ⁻¹ = x ^ s) (hτI : Subgroup.zpowers τ ⊓ I = ⊥)
    (hτp : IsPGroup p (Subgroup.zpowers τ))
    (hcard : (Nat.card A).factorization p = (Nat.card Q * orderOf τ).factorization p) :
    ∃ S : Sylow p A,
      omegaOne p ((S : Subgroup A) ⊓ I) ≤ (Subgroup.center S).map (S : Subgroup A).subtype := by
  obtain ⟨Q', hQ'⟩ := hQ
  have hQI : Q ≤ I := by
    rw [← hQ']
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hQp : IsPGroup p Q := by
    rw [← hQ']
    exact IsPGroup.of_equiv Q'.2 (Subgroup.equivMapOfInjective _ _ I.subtype_injective)
  set H := Subgroup.zpowers τ with hH
  have hτnorm : τ ∈ Subgroup.normalizer (Q : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hτ h hh]
      exact Q.pow_mem hh s
    · intro hh
      let f : Q → Q := fun x => ⟨τ * x * τ⁻¹, by rw [hτ x x.2]; exact Q.pow_mem x.2 s⟩
      have hf : Function.Injective f := by
        intro a b hab
        have := congrArg Subtype.val hab
        simp only [f] at this
        exact Subtype.ext (by simpa using this)
      obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp hf) ⟨τ * h * τ⁻¹, hh⟩
      have := congrArg Subtype.val hc
      simp only [f] at this
      have h2 : (c : A) = h := by simpa using this
      rw [← h2]; exact c.2
  have hHle : H ≤ Subgroup.normalizer (Q : Set A) := by
    rw [hH, Subgroup.zpowers_le]; exact hτnorm
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left Q H hHle
  have hQH : Q ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ H ⊓ I := ⟨hx.2, hQI hx.1⟩
    rw [hτI] at this
    exact this
  have hcardS : Nat.card ↥(Q ⊔ H) = Nat.card Q * orderOf τ := by
    have e : Nat.card ↥(Q ⊔ H) = Nat.card (Q × H) := by
      have : Nat.card ↥(Q ⊔ H) = Nat.card (↑(Q ⊔ H) : Set A) := rfl
      rw [this, hmul]
      symm
      refine Nat.card_congr (Equiv.ofBijective (fun a : Q × H => (⟨a.1 * a.2, a.1, a.1.2, a.2, a.2.2, rfl⟩ : ((Q : Set A) * (H : Set A) : Set A))) ⟨?_, ?_⟩)
      · intro a b hab
        have h1 : (a.1 : A) * a.2 = b.1 * b.2 := congrArg Subtype.val hab
        have h2 : ((b.1 : A)⁻¹ * a.1) = b.2 * (a.2 : A)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← h1]
        have hmQ : ((b.1 : A)⁻¹ * a.1) ∈ Q := mul_mem (inv_mem b.1.2) a.1.2
        have hmH : ((b.1 : A)⁻¹ * a.1) ∈ H := by rw [h2]; exact mul_mem b.2.2 (inv_mem a.2.2)
        have h3 : ((b.1 : A)⁻¹ * a.1) ∈ Q ⊓ H := ⟨hmQ, hmH⟩
        rw [hQH, Subgroup.mem_bot, inv_mul_eq_one] at h3
        have h4 : (a.1 : A) = b.1 := h3.symm
        rw [h4] at h1
        exact Prod.ext (Subtype.ext h4) (Subtype.ext (mul_left_cancel h1))
      · rintro ⟨_, a, ha, b, hb, rfl⟩
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    rw [e, Nat.card_prod, hH, Nat.card_zpowers]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp hQp
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hτp
  rw [hH, Nat.card_zpowers] at hb
  have hcardS' : Nat.card ↥(Q ⊔ H) = p ^ (Nat.card A).factorization p := by
    rw [hcardS, hcard, ha, hb, ← pow_add, Nat.Prime.factorization_pow Fact.out]
    simp
  refine ⟨Sylow.ofCard (Q ⊔ H) hcardS', ?_⟩
  rw [Sylow.coe_ofCard]
  have hSI : (Q ⊔ H) ⊓ I = Q := by
    apply le_antisymm
    · intro x hx
      have hx1 : x ∈ ((Q ⊔ H : Subgroup A) : Set A) := hx.1
      rw [hmul] at hx1
      obtain ⟨q, hq, t, ht, rfl⟩ := hx1
      have htI : t ∈ H ⊓ I := ⟨ht, by
        have := mul_mem (inv_mem (hQI hq)) hx.2
        simpa using this⟩
      rw [hτI, Subgroup.mem_bot] at htI
      simpa [htI] using hq
    · exact le_inf le_sup_left hQI
  rw [hSI]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxQ, hxp⟩
  have hxS : x ∈ Q ⊔ H := (le_sup_left : Q ≤ Q ⊔ H) hxQ
  refine ⟨⟨x, hxS⟩, ?_, rfl⟩
  have hcomτ : Commute τ x := by
    have h1 : τ * x * τ⁻¹ = x := by
      rw [hτ x hxQ]
      have := Nat.div_add_mod s p
      calc x ^ s = x ^ (p * (s / p) + s % p) := by rw [this]
        _ = x := by rw [pow_add, pow_mul, hxp, one_pow, one_mul, hs, pow_one]
    have : τ * x = x * τ := by
      calc τ * x = τ * x * τ⁻¹ * τ := by simp
        _ = x * τ := by rw [h1]
    exact this
  refine Subgroup.mem_center_iff.mpr ?_
  rintro ⟨z, hz⟩
  apply Subtype.ext
  have hz' : z ∈ ((Q ⊔ H : Subgroup A) : Set A) := hz
  rw [hmul] at hz'
  obtain ⟨q, hq, t, ht, rfl⟩ := hz'
  have hxt : Commute x t := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hcomτ.symm.zpow_right k)
  show q * t * x = x * (q * t)
  rw [mul_assoc, ← hxt.eq, ← mul_assoc, ← hQab x hxQ q hq, mul_assoc]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
