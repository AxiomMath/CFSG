module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoPar
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
public import CFSG.LieType.BorelTits.Ree

public section

namespace CFSG.Quasithin.H13.CTK

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have h3 : Nat.Prime 3 := Nat.prime_three
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · omega
  · have : (q ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, pow_two, Nat.mul_mod, hq]
    omega

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem levi_hom_sl2_f4 {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ g : ↥(perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩)) →* SL2 K,
      Function.Surjective g ∧ ∀ x, g x = 1 → (x : ModGL F4.tag K) ∈
        F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨⟨h0eq, -, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hs := isSimpleGroup_rankOneGroupOne ha hK
  have := hs.1
  obtain ⟨g, hg, hk⟩ := (F4.levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K a) h0eq
    hs.2).1
  let ε : ↥(rankOneGroupOne K a) ≃* SL2 K := (rankOneEquivSL K a hK).symm
  refine ⟨ε.toMonoidHom.comp g, ε.surjective.comp hg, fun x hx => hk x ?_⟩
  have h1 : ε (g x) = 1 := hx
  exact ε.injective (h1.trans (map_one ε).symm)

theorem noA5Block_f4 {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    NoA5Block ↥(perfectCore (F4.reeLocalParabolic K a j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases j with rfl | rfl
  · obtain ⟨g, hg, hk⟩ := levi_hom_sl2_f4 ha hK
    exact noA5Block_of_parabolicFacts_sl2 hF0 (n := 2 * a + 1) (by omega) hK g hg hk
  · obtain ⟨-, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
    have hs := isSimpleGroup_rankOneGroupTwo ha hK
    have := hs.1
    obtain ⟨g, hg, hk⟩ := (F4.levi_hom ha hK ⟨1, by decide⟩ (M := rankOneGroupTwo K a) h1eq
      hs.2).1
    refine noA5Block_of_parabolicFacts_not_three hF1 (T := ↥(rankOneGroupTwo K a)) ?_ g hk
    rw [card_rankOneGroupTwo ha hK]
    exact not_three_dvd_suzuki_order a

theorem noA5Block_f4_model {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin 2) :
    NoA5Block ↥(perfectCore ((F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a))) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  refine NoA5Block.of_perfectCore_map (F4.reeGamma K a).subtype
    (F4.reeGamma K a).subtype_injective ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (reeParabolic_le F4 K a _),
    reeParabolic_singleton (t := F4) (K := K) (a := a)]
  exact noA5Block_f4 ha hK (f4Index j)

theorem exclA5BlockFor_two_f4 :
    ExclA5BlockFor fun S _ =>
      ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel S .twistedF4 2 f := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨f, -, -, hX⟩ := hS
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hH := CFSG.LieType.BorelTits.holds_of_reeTitsModel hX (by decide)
  exact A5Config.false_of_residual_equiv e hH hU₀ (large_Ree_residualOvergroupsAt hK)
    (fun j => noA5Block_f4_model ha hK j) hc

end CFSG.Quasithin.H13.CTK
