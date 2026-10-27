module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoPar
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem levi_hom_sl2_g2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    (i : Fin Tag.G2.rank) :
    ∃ g : ↥(perfectCore (parabolicSubgroup Tag.G2 K {i})) →* SL2 K, Function.Surjective g ∧
      ∀ x, g x = 1 → (x : ModGL Tag.G2 K) ∈ parabolicRadical Tag.G2 K {i} := by
  have h4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4
  obtain ⟨ρ, hρ, hLM, hL, hMinf⟩ := levi_data h4 i
  have hQP : parabolicRadical Tag.G2 K {i} ≤ parabolicSubgroup Tag.G2 K {i} :=
    (parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})
  obtain ⟨g, hg, hk⟩ := exists_levi_hom hQP (parabolicSubgroup_le_normalizer_parabolicRadical {i})
    (parabolicRadical_inf_parabolicLevi {i}) (parabolicRadical_sup_parabolicLevi {i}) hLM hL hMinf
  let ε : ↥ρ.range ≃* SL2 K := (MonoidHom.ofInjective hρ).symm
  refine ⟨ε.toMonoidHom.comp g, ε.surjective.comp hg, fun x hx => hk x ?_⟩
  exact ε.injective (by simpa using hx)

theorem noA5Block_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (i : Fin Tag.G2.rank) :
    NoA5Block ↥(perfectCore (parabolicSubgroup Tag.G2 K {i})) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, hg, hk⟩ := levi_hom_sl2_g2 hK4 i
  rcases G2.fin_two_cases i with rfl | rfl
  · exact noA5Block_of_parabolicFacts_sl2 (G2.parabolicFacts_zero hK hf) hf hK g hg hk
  · exact noA5Block_of_parabolicFacts_sl2 (G2.parabolicFacts_one hK hf) hf hK g hg hk

theorem noA5Block_g2_model {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (j : Fin 2) :
    NoA5Block ↥(perfectCore ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K))) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  refine NoA5Block.of_perfectCore_map (adjointGroup Tag.G2 K).subtype
    (adjointGroup Tag.G2 K).subtype_injective ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup _ _ _)]
  exact noA5Block_g2 hK hf (g2Index j)

theorem exclA5BlockFor_two_g2 :
    ExclA5BlockFor fun S _ =>
      ∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨f, hf, hX⟩ := hS
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hH := CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel_untwisted hX (by decide)
    (by decide)
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  exact A5Config.false_of_residual_equiv e hH hU₀ G2_residualOvergroupsAt
    (fun j => noA5Block_g2_model hK hf j) hc

end CFSG.Quasithin.H13.CTK
