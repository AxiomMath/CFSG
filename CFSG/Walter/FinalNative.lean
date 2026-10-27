module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Walter.Ree.Thompson3
public import CFSG.Walter.W67.Section4.Prop41
public import CFSG.Walter.W67.Section5.Prop56
public import CFSG.Walter.W67.Section6.Lemma62

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.LieType.Ree CFSG.Assembly.LowTwoRank

@[expose] def WalterNativeModels : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ CFSG.Blueprint.LieModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.LieModel G .twistedG2 0 3 f) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J1

theorem blueprintLieModel_psl_two_of_mulEquiv {G : Type} [Group G] (p f : ℕ) [Fact p.Prime]
    (h4 : 4 ≤ p ^ f) (e : G ≃* PSL(2, GaloisField p f)) :
    CFSG.Blueprint.LieModel G .PSL 2 p f := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := lieModel_psl_two_of_mulEquiv p f h4 e
  · exact Or.inl ⟨by decide, hc⟩
  · exact absurd hn (by decide)

theorem reeTitsModel_of_mulEquiv_reeGamma
    {G : Type} [Group G] (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (e : G ≃* ReeTag.G2.reeGamma K a) :
    CFSG.Blueprint.ReeTitsModel G .twistedG2 3 (2 * a + 1) := by
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 ha hK
  have hadm : StatedLieAdmissible .twistedG2 0 3 (2 * a + 1) :=
    ⟨Nat.prime_three, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩
  refine ⟨hadm, a, rfl, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  have e' : G ≃* CFSG.Blueprint.DerivedCentralQuotient (ReeTag.G2.reeGamma K a) := e.trans E.symm
  rw [ReeTag.reeGamma_eq_reeFixedGroup] at e'
  exact e'

theorem blueprintLieModel_twistedG2_of_mulEquiv
    {G : Type} [Group G] (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (e : G ≃* ReeTag.G2.reeGamma K a) :
    CFSG.Blueprint.LieModel G .twistedG2 0 3 (2 * a + 1) :=
  Or.inr (Or.inr (Or.inl ⟨rfl, by decide, reeTitsModel_of_mulEquiv_reeGamma a ha K hK e⟩))

theorem walter_models_native_of
    (hT : W67.Theorem) (hR : W67.ReeIdentNative) :
    WalterNativeModels := by
  intro G _ _ _ hnonab P hP
  rcases walter_structure (jrStrongHyp_of_open hT j1RecogHyp jtThreeHyp) G hnonab P hP with
    hL2 | hR' | hJ
  · rcases hL2 with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩
    · have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      exact Or.inl ⟨f, hf, blueprintLieModel_psl_two_of_mulEquiv 2 f h4 e⟩
    · refine Or.inr (Or.inl ⟨p, f, hp.out, ?_, hf, h5, h8,
        blueprintLieModel_psl_two_of_mulEquiv p f (by omega) e⟩)
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  · obtain ⟨hR'⟩ := hR'
    obtain ⟨a, K, _, _, _, ha, hK, -, ⟨e⟩⟩ := hR G hR'
    exact Or.inr (Or.inr (Or.inl ⟨2 * a + 1, ⟨a, rfl⟩, by omega,
      blueprintLieModel_twistedG2_of_mulEquiv a ha K hK e⟩))
  · obtain ⟨e⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (isSporadic_J1_of_mulEquiv e)))

theorem walter_models_native_of_base
    (h62 : W67.S_lemma_6_2) (h65 : W67.S_lemma_6_5)
    (hbase : Ree.T2.BaseExists) : WalterNativeModels :=
  have hR := Ree.reeIdentNative hbase
  walter_models_native_of
    (W67.theorem_of_reeIdentNative (W67.prop_6_6_of W67.prop_4_1 W67.prop_5_6 h62 h65) hR) hR

theorem walter_models_native_of_lemma65_base
    (h65 : W67.S_lemma_6_5)
    (hbase : Ree.T2.BaseExists) : WalterNativeModels :=
  walter_models_native_of_base (W67.lemma_6_2_of W67.prop_4_1 W67.prop_5_6) h65 hbase

theorem statedClassicalModel_psl_two_of_mulEquiv {G : Type} [Group G] (p f : ℕ) [Fact p.Prime]
    (h4 : 4 ≤ p ^ f) (e : G ≃* PSL(2, GaloisField p f)) : StatedClassicalModel G .PSL 2 p f := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := lieModel_psl_two_of_mulEquiv p f h4 e
  · exact hc
  · exact absurd hn (by decide)

theorem walter_modelsForm_of
    (hT : W67.Theorem) (hR : W67.ReeIdentNative) :
    WalterModelsForm := by
  intro G _ _ _ hnonab P hP
  rcases walter_structure (jrStrongHyp_of_open hT j1RecogHyp jtThreeHyp) G hnonab P hP with
    hL2 | hR' | hJ
  · rcases hL2 with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩
    · have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      exact Or.inl ⟨f, hf, statedClassicalModel_psl_two_of_mulEquiv 2 f h4 e⟩
    · refine Or.inr (Or.inl ⟨p, f, hp.out, ?_, hf, h5, h8,
        statedClassicalModel_psl_two_of_mulEquiv p f (by omega) e⟩)
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  · obtain ⟨hR'⟩ := hR'
    obtain ⟨a, K, _, _, _, ha, hK, -, ⟨e⟩⟩ := hR G hR'
    exact Or.inr (Or.inr (Or.inl ⟨2 * a + 1, ⟨a, rfl⟩, by omega,
      reeTitsModel_of_mulEquiv_reeGamma a ha K hK e⟩))
  · obtain ⟨e⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (isSporadic_J1_of_mulEquiv e)))

theorem walterNativeModels_of (h : WalterModelsForm) : WalterNativeModels := by
  intro G _ _ _ hnonab P hP
  rcases h G hnonab P hP with ⟨f, hf, hc⟩ | ⟨p, f, hp, hp2, hf, h5, h8, hc⟩ | ⟨f, hfo, hf3, hr⟩ |
    hJ
  · exact Or.inl ⟨f, hf, Or.inl ⟨by decide, hc⟩⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h5, h8, Or.inl ⟨by decide, hc⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hfo, hf3, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hr⟩))⟩))
  · exact Or.inr (Or.inr (Or.inr hJ))

theorem walter_modelsForm_of_base
    (h62 : W67.S_lemma_6_2) (h65 : W67.S_lemma_6_5)
    (hbase : Ree.T2.BaseExists) : WalterModelsForm :=
  have hR := Ree.reeIdentNative hbase
  walter_modelsForm_of
    (W67.theorem_of_reeIdentNative (W67.prop_6_6_of W67.prop_4_1 W67.prop_5_6 h62 h65) hR) hR

theorem walter_modelsForm_of_lemma65_base
    (h65 : W67.S_lemma_6_5)
    (hbase : Ree.T2.BaseExists) : WalterModelsForm :=
  walter_modelsForm_of_base (W67.lemma_6_2_of W67.prop_4_1 W67.prop_5_6) h65 hbase

end CFSG.Walter
