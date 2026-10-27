module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamImg
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def A5Core (S : Type) [Group S] : Prop :=
  ∃ K V : Subgroup S, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set S) ∧ Nat.card ↥K = 960 ∧
    Nat.card ↥V = 16 ∧ IsElemAbelian 2 V ∧
    ∃ m : ℕ, Nat.card ↥(Subgroup.normalizer (V : Set S)) = 960 * 2 ^ m

theorem mul_comm_of_isElemAbelian {S : Type*} [Group S] {V : Subgroup S}
    (h : IsElemAbelian 2 V) {a b : S} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm h ha hb

theorem exists_orderOf_five_of_card_eq_960 {S : Type} [Group S] {K : Subgroup S}
    (hK : Nat.card ↥K = 960) : ∃ x : S, x ∈ K ∧ orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 (by rw [hK]; norm_num)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem A5Config.core {S : Type} [Group S] [Finite S] (h : A5Config S) : A5Core S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, V, T₁, T₂, hVK, hV16, hel, hΔ, hT1N, hN, hT1S, -, -, -⟩ := h
  obtain ⟨α, hα, hαk, -⟩ := hΔ
  have hnorm : (V.subgroupOf K).Normal := hαk ▸ α.normal_ker
  have hKN : K ≤ Subgroup.normalizer (V : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).1 hnorm
  have hcardV : Nat.card ↥(V.subgroupOf K) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV16]
  have hcardA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hker : Nat.card ↥α.ker = 16 := by
    rw [hαk]
    exact hcardV
  have hK : Nat.card ↥K = 960 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker, hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, hcardA]
  refine ⟨K, V, hVK, hKN, hK, hV16, hel, ?_⟩
  have hnormal : (K.subgroupOf (K ⊔ T₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hT1N)
  let f : ↥T₁ →* ↥(K ⊔ T₁) ⧸ K.subgroupOf (K ⊔ T₁) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : S) ∈ (K : Set S) * (T₁ : Set S) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T₁ hT1N]
      exact y.2
    obtain ⟨k, hk, t, ht, hkt⟩ := hy
    refine ⟨⟨t, ht⟩, ?_⟩
    have hyeq : y = ⟨k, Subgroup.mem_sup_left hk⟩ * ⟨t, Subgroup.mem_sup_right ht⟩ :=
      Subtype.ext hkt.symm
    have hk1 : (QuotientGroup.mk ⟨k, Subgroup.mem_sup_left hk⟩ :
        ↥(K ⊔ T₁) ⧸ K.subgroupOf (K ⊔ T₁)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hk
    show (QuotientGroup.mk (Subgroup.inclusion le_sup_right ⟨t, ht⟩) : _) = _
    rw [hyeq, QuotientGroup.mk_mul, hk1, one_mul]
    rfl
  have hQ : IsPGroup 2 (↥(K ⊔ T₁) ⧸ K.subgroupOf (K ⊔ T₁)) := hT1S.2.1.of_surjective f hf
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  refine ⟨n, ?_⟩
  rw [hN, Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (K ⊔ T₁)), hn,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hK, mul_comm]

theorem ExclA5BlockFor.of_not_core {P : ∀ (S : Type) [Group S], Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → ¬ A5Core S) : ExclA5BlockFor P :=
  ExclA5BlockFor.of_not_config fun S _ _ hS hc => h S hS hc.core

end CFSG.Quasithin.H13.CTK
