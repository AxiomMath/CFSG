module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.SzFix

open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem card_fixed_eq_of_intertwine {G H : Type*} [Group G] [Group H] (v : G ≃* H)
    (α : MulAut G) (β : MulAut H) (hβ : ∀ x, β (v x) = v (α x)) :
    Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup β) := by
  refine Nat.card_congr (Equiv.subtypeEquiv v.toEquiv fun x => ?_)
  show α x = x ↔ β (v x) = v x
  rw [hβ, v.injective.eq_iff]

theorem not_mem_inner_of_orderOf_three {H : Type} [Group H]
    {f : ℕ} (hS : SuzukiModel H 2 f) {σ : MulAut H} (hσ : orderOf σ = 3) : σ ∉ inner H := by
  intro hin
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ, pow_one])
  have hmem : σ ∈ Subgroup.zpowers σ ⊓ inner H := ⟨Subgroup.mem_zpowers σ, hin⟩
  rw [CFSG.RankThree.PartTwo.KFacts.KP7.inf_inner_eq_bot hS hP, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hσ
  omega

theorem card_fixed_of_orderOf_three {S : Type} [Group S] [Finite S]
    {f : ℕ} (hS : SuzukiModel S 2 f) {σ : MulAut S} (hσ : orderOf σ = 3) :
    ∃ b : ℕ, f = 3 * (2 * b + 1) ∧
      Nat.card S = (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) ∧
      Nat.card (fixedSubgroup σ) =
        (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) := by
  have hS' := hS
  obtain ⟨-, a, ha, K, hKF, hKfin, rfl, hK, ⟨e⟩⟩ := hS'
  have hσ'o : orderOf (MulAut.congr e σ) = 3 := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) σ, hσ]
  have hmodel : SuzukiModel (suzukiGroup a K) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨τ, h, b, k, hkF, hkfin, -, hb, hkcard, hconj, ⟨eC⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK 3 Nat.prime_three
      (by norm_num) (MulAut.congr e σ) hσ'o (not_mem_inner_of_orderOf_three hmodel hσ'o)
  refine ⟨b, by omega, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  · have hint : Nat.card (fixedSubgroup σ) = Nat.card (fixedSubgroup (szFieldAut a K τ)) :=
      card_fixed_eq_of_intertwine (e.trans (MulAut.conj h)) σ (szFieldAut a K τ) fun x => by
        have h1 : szFieldAut a K τ (MulAut.conj h (e x)) =
            MulAut.conj h (MulAut.congr e σ (e x)) := by
          rw [← hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
        rw [MulEquiv.trans_apply, h1]
        simp [MulAut.congr_apply]
    rw [hint]
    exact (Nat.card_congr eC.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hkcard)

theorem exists_mem_ne_of_isSylowOf {G : Type*} [Group G] [Finite G] (σ : MulAut G) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hdvd : ℓ ∣ Nat.card G) (hfix : ¬ ℓ ∣ Nat.card (fixedSubgroup σ))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf ℓ P ⊤) : ∃ x ∈ P, σ x ≠ x := by
  by_contra hcon
  push Not at hcon
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hle : P ≤ fixedSubgroup σ := fun x hx => hcon x hx
  have h1 : Nat.card P ∣ Nat.card (fixedSubgroup σ) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card P = ℓ ^ (Nat.card (⊤ : Subgroup G)).factorization ℓ := hP.card_eq
  rw [Subgroup.card_top] at h2
  have h3 : 0 < (Nat.card G).factorization ℓ := hℓ.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
  exact hfix ((dvd_pow_self ℓ h3.ne').trans (h2 ▸ h1))

end CFSG.LocalAnalysis.UniquenessCase.UCK.SzFix
