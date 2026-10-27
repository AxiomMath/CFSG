module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank

section Suzuki

theorem outThreeBound_sz {a : ℕ} {K : Type} [Field K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : OutThreeBound (suzukiGroup a K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  exact outThreeBound_of_isCyclic
    (isCyclic_outer_of_normal_form _ (exists_conj_mul_szFieldAut ha hK))

theorem outThreeOrElemNine_of_suzukiModel {S : Type} [Group S]
    {f : ℕ} (h : SuzukiModel S 2 f) : OutThreeOrElemNine S := by
  obtain ⟨-, b, hb, K, _, _, hfb, hK, ⟨E⟩⟩ := h
  exact Or.inl ((outThreeBound_sz hb (by rw [hK, hfb])).of_mulEquiv E)

end Suzuki

section Chevalley


theorem outThreeBound_g2 (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) : OutThreeBound (adjointGroup Tag.G2 K) := by
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  exact outThreeBound_of_isCyclic
    (isCyclic_outer_of_normal_form (g2FieldHom K) (g2_automorphism_normal_form hK3 hK4).1)

theorem outThreeBound_largeRee {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    OutThreeBound (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  exact outThreeBound_of_isCyclic
    (isCyclic_outer_of_normal_form (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAutHom K a)
      (largeRee_automorphism_normal_form ha hK).1)

theorem outThreeBound_triality {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    OutThreeBound (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  exact outThreeBound_of_isCyclic
    (isCyclic_outer_of_normal_form (fieldActorHom (t := TwistTag.D4) σ)
      (exists_conj_mul_fieldActor hf hK hσ))

theorem outThreeOrElemNine_of_g2 {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : OutThreeOrElemNine S := by
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  have hK3 : ringChar K ≠ 3 := by
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK])
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact Or.inl ((outThreeBound_g2 K hK3 hK4).of_mulEquiv E)

theorem outThreeOrElemNine_of_triality {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : OutThreeOrElemNine S := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 h
  exact Or.inl ((outThreeBound_triality hf hK hσ).of_mulEquiv E)

theorem outThreeOrElemNine_of_largeRee {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : OutThreeOrElemNine S := by
  obtain ⟨-, b, hb, -, K, _, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_reeGamma h
  exact Or.inl ((outThreeBound_largeRee hb hK).of_mulEquiv E)

end Chevalley

section Tits


theorem outThreeOrElemNine_of_tits {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1) :
    OutThreeOrElemNine S := by
  have hcard := (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound S 2 1 h).2.2.1
  exact Or.inl (outThreeBound_of_card_outer_dvd_two (by simp [hcard]))

end Tits

end CFSG.Quasithin.SBd19F
