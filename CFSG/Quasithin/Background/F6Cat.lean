module

public import CFSG.Quasithin.Background.F6ComponentBound
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F6

theorem f618_trichotomy {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) :
    (IsF618CaseOne G₁ G₂ ∨ IsF618CaseTwo D) ∨
      (IsCyclic ↥(Open.pCore 3 D) ∧ ∃ K : Subgroup D, CFSG.IsComponent K ∧ K.Normal ∧
        ((twoResidual G₁ ≤ K ∧ ¬ twoResidual G₂ ≤ K ∧ K ⊔ G₂ = ⊤) ∨
          (twoResidual G₂ ≤ K ∧ ¬ twoResidual G₁ ≤ K ∧ K ⊔ G₁ = ⊤))) ∨
      (CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D) ∧
        CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) := by
  by_cases hc : IsCyclic ↥(Open.pCore 3 D)
  · obtain ⟨K, hKc⟩ := exists_isComponent_of_isCyclic h hO hc
    obtain ⟨hKn, hcases, -⟩ := f6_10 h hKc (index_normalizer_le_two_of_isComponent hO hm hKc)
    rcases hcases with ⟨h₁, hsup⟩ | ⟨h₂, hsup⟩
    · by_cases h₂ : twoResidual G₂ ≤ K
      · exact Or.inr (Or.inr ⟨generalizedFitting_eq_twoResidual h hO hKc h₁ h₂,
          twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1⟩)
      · exact Or.inr (Or.inl ⟨hc, K, hKc, hKn, Or.inl ⟨h₁, h₂, hsup⟩⟩)
    · by_cases h₁ : twoResidual G₁ ≤ K
      · exact Or.inr (Or.inr ⟨generalizedFitting_eq_twoResidual h hO hKc h₁ h₂,
          twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1⟩)
      · exact Or.inr (Or.inl ⟨hc, K, hKc, hKn, Or.inr ⟨h₂, h₁, hsup⟩⟩)
  · exact Or.inl (isF618CaseOne_or_two_of_noncyclic h hO hm hc)

@[expose] noncomputable def PSigmaL2 (K : Type) [Field K] :
    Subgroup (CFSG.GorensteinWalter.PGammaL2 K) :=
  CFSG.GorensteinWalter.pGammaL2PSLRange K ⊔
    (SemidirectProduct.inr : (K ≃+* K) →* CFSG.GorensteinWalter.PGammaL2 K).range

@[expose] def IsL2FieldExtCat (p : ℕ) (W : Type) [Group W] : Prop :=
  p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
    Nonempty (W ≃* ↥(PSigmaL2 K))

section Cases

variable {D : Type} [Group D]

@[expose] def IsF618CaseEightCat (H₁ H₂ : Subgroup D) : Prop :=
  (IsHatSym 6 D ∨ ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2FieldExtCat p D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) ∧
    Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥H₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))

@[expose] def IsF618CaseNineCat (H₁ H₂ : Subgroup D) : Prop :=
  (Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ IsHatSym 7 D ∨
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 19) ∧ IsL2FieldExtCat p D) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) ∧
    Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4)

@[expose] def IsF618CaseOrientedCat (H₁ H₂ : Subgroup D) : Prop :=
  IsF618CaseOne H₁ H₂ ∨ IsF618CaseTwo D ∨ IsF618CaseThree H₁ H₂ ∨ IsF618CaseFour H₁ H₂ ∨
    IsF618CaseFive H₁ H₂ ∨ IsF618CaseSix H₁ H₂ ∨ IsF618CaseSeven H₁ H₂ ∨
    IsF618CaseEightCat H₁ H₂ ∨ IsF618CaseNineCat H₁ H₂ ∨ IsF618CaseTen H₁ H₂ ∨
    IsF618CaseEleven H₁ H₂ ∨ IsF618CaseTwelve H₁ H₂ ∨ IsF618CaseThirteen H₁ H₂

@[expose] def F618ConclusionCat (H₁ H₂ : Subgroup D) : Prop :=
  IsF618CaseOrientedCat H₁ H₂ ∨ IsF618CaseOrientedCat H₂ H₁

theorem f618ConclusionCat_comm {H₁ H₂ : Subgroup D} :
    F618ConclusionCat H₁ H₂ ↔ F618ConclusionCat H₂ H₁ :=
  or_comm

end Cases

theorem pPrimeCore_eq_bot_and_pRank_le_of_isSQTKCat {D X : Type} [Group D] [Finite D] [Group X]
    [Finite X] (hX : CFSG.SectionRank.IsSQTKCat X) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) :
    CFSG.pPrimeCore 3 D = ⊥ ∧ Open.pRank 3 (⊤ : Subgroup D) ≤ 2 :=
  pPrimeCore_eq_bot_and_pRank_le
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hX.1 3 Nat.prime_three (by norm_num)) e

@[expose] def TheoremF618Cat : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    F618ConclusionCat G₁ G₂

@[expose] def F617NonquasisimpleCaseCat : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    IsCyclic ↥(Open.pCore 3 D) → ∀ K : Subgroup D, CFSG.IsComponent K → K.Normal →
    twoResidual G₁ ≤ K → ¬ twoResidual G₂ ≤ K → K ⊔ G₂ = ⊤ → IsF618CaseThree G₁ G₂

@[expose] def F618QuasisimpleCaseCat : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D) →
    CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D)) → F618ConclusionCat G₁ G₂

theorem theoremF618Cat_of_cases (hNQ : F617NonquasisimpleCaseCat)
    (hQS : F618QuasisimpleCaseCat) : TheoremF618Cat := by
  intro D _ _ G₁ G₂ h hX
  obtain ⟨X, _, _, hsq, ⟨e⟩⟩ := hX
  have hX' : ∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X) := ⟨X, inferInstance, inferInstance, hsq, ⟨e⟩⟩
  obtain ⟨hO, hm⟩ := pPrimeCore_eq_bot_and_pRank_le_of_isSQTKCat hsq e
  rcases f618_trichotomy h hO hm with h12 | ⟨hc, K, hK, hKn, hcase⟩ | ⟨hF, hL⟩
  · rcases h12 with h1 | h2
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h2))
  · rcases hcase with ⟨h₁, h₂, hsup⟩ | ⟨h₂, h₁, hsup⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inl (hNQ D G₁ G₂ h hX' hc K hK hKn h₁ h₂ hsup))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (hNQ D G₂ G₁ h.symm hX' hc K hK hKn h₂ h₁ hsup))))
  · exact hQS D G₁ G₂ h hX' hF hL

end F6

end CFSG.Quasithin
