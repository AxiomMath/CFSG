module

public import CFSG.Quasithin.H13.NQTermExcludesTriality
public import CFSG.Quasithin.H13.NQBlockExcludesLargeRee
public import CFSG.Quasithin.H13.NQCatExcludesTits
public import CFSG.Quasithin.H13.NQBlockOriginalRadical

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

@[expose] def OriginalXTNormalComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ →
      CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) →
      ∀ P : Subgroup G, IsSylowOf p P X →
      ∀ Y : Subgroup G, X ⊔ T ≤ Y → pCoreOf 2 Y ≠ ⊥ → ¬ Y ≤ M →
      ∃ K : Subgroup G, K ∈ cComp Y ∧ quasithinIsLocal T K ∧ K ≤ Y ∧ (K.subgroupOf Y).Normal ∧
        X ≤ K ∧ ¬ K ≤ M ∧ quasithinGenFitting K = pCoreOf 2 K ∧ ⁅K, X⁆ = K ∧
        pCoreOf 2 (X ⊔ T) ≤ normalizer (K : Set G) ∧
        CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∧
        (Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
          Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3) ∧
        CFSG.pRank p (K ⧸ CFSG.pCore 2 K) = 2 ∧
        CFSG.Blueprint.Catalog ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ∧
        CFSG.IsStronglyQuasithin ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ∧
        Function.Injective (((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 K))).comp (P.subgroupOf K).subtype) ∧
        IsSylowOf 2 (T ⊓ K) K ∧
        (P : Set G) * ((T ⊓ K : Subgroup G) : Set G) = ((T ⊓ K : Subgroup G) : Set G) * P ∧
        (P : Set G) * ((T ⊓ K : Subgroup G) : Set G) = (P : Set G) * (T : Set G) ∩ (K : Set G) ∧
        ((∃ f : ℕ, 3 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 2 f) ∨
          (∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f) ∨
          (∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f) ∨
          (∃ f : ℕ, 1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f) ∨
          (∃ a : ℕ, 1 ≤ a ∧ CFSG.Blueprint.ReeTitsModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .twistedF4 2 (2 * a + 1)) ∨
          CFSG.Blueprint.ReeTitsModel
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .Tits 2 1 ∨
          (Nonempty ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃*
            CFSG.Blueprint.NativeSporadic.J4) ∧ p = 11))

@[expose] def OriginalWitnessExcludesCrossLinearThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).Characteristic →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      ∀ Y K : Subgroup G, X ⊔ T ≤ Y → K ≤ Y → (K.subgroupOf Y).Normal → X ≤ K →
      CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) →
      ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ f : ℕ, 1 ≤ f →
        ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 ℓ f

@[expose] def OriginalWitnessExcludesEvenSymplecticFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).Characteristic →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      ∀ Y K : Subgroup G, X ⊔ T ≤ Y → K ≤ Y → (K.subgroupOf Y).Normal → X ≤ K →
      CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) →
      ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
      ∀ f : ℕ, 2 ≤ f →
        ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_ne_bot_of_maxTwoLocal {H : Subgroup G} (hH : quasithinIsMaxTwoLocal H) :
    pCoreOf 2 H ≠ ⊥ := by
  obtain ⟨Q, hQ1, hQ2, rfl⟩ := hH.1
  intro h0
  apply hQ1
  have hQN : Q ≤ normalizer (Q : Set G) := le_normalizer
  have h1 := le_pCoreOf_of_subgroupOf_normal hQN
    ((normal_subgroupOf_iff_le_normalizer hQN).mpr le_rfl) hQ2
  rw [h0] at h1
  exact le_bot_iff.mp h1

theorem original_characteristic_witness_singleton_of_inputs
    (hProd : OriginalXTNormalComponent)
    (hL3 : OriginalWitnessExcludesCrossLinearThree)
    (hSp4 : OriginalWitnessExcludesEvenSymplecticFour)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hXL : X ≤ L := hXR.trans (map_subtype_le _)
  refine ⟨h.max_two_local, sup_le (hXL.trans h.l_le) h.t_le, fun M' hM' hXTM' => ?_⟩
  by_contra hne
  have hM'M : ¬ M' ≤ M := fun hle => hne (hM'.2 M h.max_two_local.1 hle).symm
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨K, -, -, hKY, hKn, hXK, -, -, -, -, hJq, hZ, -, -, -, -, -, -, -, halt⟩ :=
    hProd G T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr P hP M' hXTM'
      (pCoreOf_ne_bot_of_maxTwoLocal hM') hM'M
  have hpZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := by
    rcases hZ with hZ | hZ <;> rw [hZ] <;> intro hd
    · exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    · have := Nat.le_of_dvd (by norm_num) hd
      omega
  rcases halt with ⟨f, hf, hmod⟩ | ⟨f, hf, hmod⟩ | ⟨f, hf, hmod⟩ | ⟨f, hf, hmod⟩ |
      ⟨a, ha, hmod⟩ | hmod | ⟨⟨e⟩, -⟩
  · exact hL3 G T L M h p hp hp5 X hXL hXc hXA hexp hW hLW M' K hXTM' hKY hKn hXK hJq hpZ 2
      Nat.prime_two (by omega) f (by omega) hmod
  · exact hSp4 G T L M h p hp hp5 X hXL hXc hXA hW hLW M' K hXTM' hKY hKn hXK hJq hpZ f hf hmod
  · exact NQTerm.original_characteristic_witness_excludes_normal_even_G2_quotient h hp hp5 hXL
      hXc hXA hW hLW hXTM' hKY hKn hXK hpZ f hf hmod
  · exact NQTerm.original_characteristic_witness_excludes_normal_even_triality_quotient h hp hp5
      hXL hXc hXA hW hLW hXTM' hKY hKn hXK hpZ f hf hmod
  · exact original_characteristic_witness_excludes_normal_large_Ree_quotient h hp hp5 hXL hXc hXA
      hW hLW hXTM' hKY hKn hXK hpZ a ha hmod
  · exact NQCat.original_characteristic_witness_excludes_normal_Tits_quotient h hp hp5 hXL hXc hXA
      hW hLW hXTM' hKY hKn hXK hpZ hmod
  · exact (NQCat.original_characteristic_witness_excludes_normal_J4_quotient h hp hp5 hXL hXc hXA
      hW hLW hXTM' hKY hKn hXK hpZ).false e

end CFSG.Quasithin.H13.NQBlock
