module

public import CFSG.Quasithin.Background.A3FactsA134Core
public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.Quasithin.Background.A3FactsSporadic
public import CFSG.Quasithin.Background.A3FactsExceptional
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open CFSG.SectionRank CFSG.LocalCores CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def A134Concl (H : Type) [Group H] [Finite H] : Prop :=
  ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
    Nonempty (↥L₁ ≃* ↥L₂) →
    (∀ L : Subgroup H, CFSG.IsComponent L → Nonempty (↥L ≃* ↥L₁) → L = L₁ ∨ L = L₂) ∧
    (A134TypesCentral ↥L₁ ∨ (IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3))

section Core

variable {H : Type} [Group H] [Finite H]

theorem a134Concl_of_layerQuot
    (hsqt : CFSG.IsStronglyQuasithin (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)))
    (hone : ∀ K : ComponentIndex H,
      (∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r (⊤ : Subgroup (↥K.1 ⧸ Subgroup.center ↥K.1)) ≤ 1) →
        A134Types (↥K.1 ⧸ Subgroup.center ↥K.1)) :
    A134Concl H := by
  intro L₁ L₂ h₁ h₂ hne ⟨e⟩
  let K₁ : ComponentIndex H := ⟨L₁, h₁⟩
  let K₂ : ComponentIndex H := ⟨L₂, h₂⟩
  have hK12 : K₁ ≠ K₂ := fun h => hne (congrArg Subtype.val h)
  have e₂ : (↥K₁.1 ⧸ Subgroup.center ↥K₁.1) ≃* (↥K₂.1 ⧸ Subgroup.center ↥K₂.1) :=
    centerQuotientEquiv e
  refine ⟨fun L hL ⟨eL⟩ => ?_, Or.inl (hone K₁ fun r hr hr2 =>
    pRank_le_one_of_two_iso hsqt hK12 e₂ hr hr2)⟩
  by_contra hcon
  push Not at hcon
  let K₃ : ComponentIndex H := ⟨L, hL⟩
  have hK13 : K₁ ≠ K₃ := fun h => hcon.1 (congrArg Subtype.val h).symm
  have hK23 : K₂ ≠ K₃ := fun h => hcon.2 (congrArg Subtype.val h).symm
  exact not_three_iso hsqt hK12 hK13 hK23 e₂ (centerQuotientEquiv eL.symm)

end Core

@[expose] def RankOneList : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Milestones.SQTKSimpleList S →
    (∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 1) → A134Types S

@[expose] def ExceptionalOddRankTwo : Prop :=
  (∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → ChevalleyExceptionalModel S .G2 2 f →
      OddRankTwo S) ∧
    (∀ (S : Type) [Group S] [Finite S] (f : ℕ), 1 ≤ f →
      ChevalleyExceptionalModel S .trialityD4 2 f → OddRankTwo S) ∧
    (∀ (S : Type) [Group S] [Finite S] (f : ℕ), Odd f → 3 ≤ f →
      ReeTitsModel S .twistedF4 2 f → OddRankTwo S)

theorem exceptionalOddRankTwo_of_triality_two
    (h : TrialityTwoOddRankTwo) :
    ExceptionalOddRankTwo :=
  ⟨fun _ _ _ _ hf hm => oddRankTwo_G2 hf hm,
    fun S _ _ f hf hm => by
      rcases Nat.lt_or_ge f 2 with h1 | h2
      · obtain rfl : f = 1 := by omega
        exact h S hm
      · exact oddRankTwo_trialityD4 h2 hm,
    fun _ _ _ _ _ _ hm => oddRankTwo_twistedF4 hm⟩

theorem statedPSL_two_seven_of_three_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 2 1) : StatedClassicalModel X .PSL 2 7 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two h

theorem statedPSL_two_five_of_alt_five {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : StatedClassicalModel X .PSL 2 5 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (ZMod 5) = 5 := by simp
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr hK)
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by simp, ⟨e.trans e5.symm⟩⟩

theorem two_le_pRank_psl_psu_three {S : Type} [Group S] [Finite S] {p : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSL 3 p 1 ∨ StatedClassicalModel S .PSU 3 p 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  rcases h with h | h
  · obtain ⟨-, -, h⟩ := classical_model_rank hp2 h
    rcases h with ⟨-, ⟨hn, -⟩ | ⟨-, hr⟩ | hr⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
    · exact absurd hn (by norm_num)
    · omega
    · omega
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · omega
  · obtain ⟨-, -, h⟩ := classical_model_rank hp2 h
    rcases h with ⟨ht, -⟩ | ⟨-, ⟨-, hr⟩ | hr⟩ | ⟨ht, -⟩ | hr
    · exact absurd ht (by decide)
    · omega
    · omega
    · exact absurd ht (by decide)
    · omega

theorem a134Types_or_oddRankTwo
    (hexc : ExceptionalOddRankTwo) {S : Type} [Group S] [Finite S]
    (hlist : CFSG.Milestones.SQTKSimpleList S) : A134Types S ∨ OddRankTwo S := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | (⟨f, hf⟩ | htits) |
    ⟨n, hn, hmodel⟩ | ⟨s, hs, ⟨e⟩⟩
  ·
    interval_cases n
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨5, 1, Nat.prime_five, by norm_num, le_rfl,
        by norm_num, statedPSL_two_five_of_alt_five e⟩)))
    all_goals exact Or.inr (OddRankTwo.of_mulEquiv e
      ⟨3, Nat.prime_three, by norm_num, two_le_pRank_alternating (by norm_num)⟩)
  ·
    rcases hodd with ⟨f, hf, hmodel⟩ | hl3 | hu3
    · by_cases hp3 : 3 < p
      · rcases hf with rfl | rfl
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨p, 1, hp, hp3, le_rfl, by norm_num, hmodel⟩)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨p, 2, hp, hp3, by norm_num, le_rfl, hmodel⟩)))
      · have hp3' : p = 3 := by have := hp.two_le; omega
        subst hp3'
        rcases hf with rfl | rfl
        · exact absurd (by norm_num : ((2 : ℕ), 3 ^ 1) = (2, 3)) hmodel.1.2.2.2.2
        · obtain ⟨-, -, h⟩ := classical_model_rank hp2 hmodel
          refine Or.inr ⟨3, Nat.prime_three, by norm_num, ?_⟩
          rcases h with ⟨-, ⟨-, hr⟩ | ⟨hn, -⟩ | hr⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
          · omega
          · exact absurd hn (by norm_num)
          · omega
          · exact absurd ht (by decide)
          · exact absurd ht (by decide)
          · omega
    · exact Or.inr ⟨p, hp, hp2, two_le_pRank_psl_psu_three hp2 (Or.inl hl3)⟩
    · exact Or.inr ⟨p, hp, hp2, two_le_pRank_psl_psu_three hp2 (Or.inr hu3)⟩
  ·
    rcases hf with ⟨hf2, hmodel⟩ | ⟨hf1, hmodel⟩ | ⟨hf2, hmodel⟩ | ⟨hf2, hmodel⟩ | ⟨hf2, hmodel⟩ |
      ⟨hf1, hmodel⟩ | ⟨hodd, hf3, hmodel⟩ | ⟨-, -, hmodel⟩
    · exact Or.inl (Or.inl ⟨f, hmodel⟩)
    · rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | hf3
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨7, 1, by norm_num, by norm_num, le_rfl,
          by norm_num, statedPSL_two_seven_of_three_two hmodel⟩)))
      · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
        exact Or.inr (OddRankTwo.of_mulEquiv eK
          ⟨3, Nat.prime_three, by norm_num, psl_three_four_two_le_pRank hK⟩)
      · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
        obtain ⟨r, hr, hr2, h2⟩ := psl_three_two_le_pRank (K := K) hK hf3
        exact Or.inr (OddRankTwo.of_mulEquiv eK ⟨r, hr, hr2, h2⟩)
    · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
      by_cases hf3 : f = 3
      · subst hf3
        exact Or.inr (OddRankTwo.of_mulEquiv eK
          ⟨3, Nat.prime_three, by norm_num, psu_three_eight_two_le_pRank hK⟩)
      · obtain ⟨r, hr, hr2, h2⟩ := psu_three_two_le_pRank (K := K) hK hf2 hf3
        exact Or.inr (OddRankTwo.of_mulEquiv eK ⟨r, hr, hr2, h2⟩)
    · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
      obtain ⟨r, hr, hr2, h2⟩ := psp_two_two_le_pRank (K := K) hK hf2
      exact Or.inr (OddRankTwo.of_mulEquiv eK ⟨r, hr, hr2, h2⟩)
    · exact Or.inr (hexc.1 S f hf2 hmodel)
    · exact Or.inr (hexc.2.1 S f hf1 hmodel)
    · exact Or.inr (hexc.2.2 S f hodd hf3 hmodel)
    · exact Or.inl (Or.inr (Or.inl ⟨f, hmodel⟩))
  · exact Or.inr (oddRankTwo_tits htits)
  ·
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
    rcases hn with rfl | rfl
    · exact Or.inr (OddRankTwo.of_mulEquiv eK
        ⟨3, Nat.prime_three, by norm_num, psl_two_le_pRank_three (by norm_num)⟩)
    · exact Or.inr (OddRankTwo.of_mulEquiv eK
        ⟨3, Nat.prime_three, by norm_num, psl_two_le_pRank_three (by norm_num)⟩)
  ·
    have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S e.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_M11)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_M12)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_M22)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_M23)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_M24)
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_J2)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_J4)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_HS)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_He)
    · exact Or.inr (OddRankTwo.of_mulEquiv e oddRankTwo_Ru)

theorem rankOneList_of_exceptional
    (hexc : ExceptionalOddRankTwo) : RankOneList := by
  intro S _ _ _ _ hlist hone
  rcases a134Types_or_oddRankTwo hexc hlist with h | ⟨r, hr, hr2, h2⟩
  · exact h
  · exact absurd (hone r hr hr2) (by omega)

theorem rankOneList_of_triality_two
    (h : TrialityTwoOddRankTwo) : RankOneList :=
  rankOneList_of_exceptional (exceptionalOddRankTwo_of_triality_two h)

theorem a134Concl_of_sqtk
    (hRO : RankOneList) {H : Type} [Group H] [Finite H]
    (hH : IsSQTKCat H) : A134Concl H := by
  have hE : CFSG.layer (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)) = ⊤ := by
    have : ∀ K : ComponentIndex H, IsSimpleGroup (↥K.1 ⧸ Subgroup.center ↥K.1) :=
      fun K => ((layer_central_quotient (G := H)).2.1 K).1
    exact layer_eq_top_of_mulEquiv_pi (fun K => ((layer_central_quotient (G := H)).2.1 K).2)
      (layerCentralQuotientEquiv H).symm
  have hsqt := sqtk_semisimple_section_rank_of_catalog oddKernelCentralization catalogStepHyp hH
    (CFSG.layer H) (Subgroup.center ↥(CFSG.layer H)) hE
  refine a134Concl_of_layerQuot hsqt fun K hone => ?_
  obtain ⟨hsimple, hnonab⟩ := (layer_central_quotient (G := H)).2.1 K
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list_section H hH K.1
    (Subgroup.center ↥K.1) hnonab
  exact hRO _ hsimple hnonab hlist hone

end A3Facts

end CFSG.Quasithin
