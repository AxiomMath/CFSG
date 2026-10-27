module

public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.F6CatSetting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace F6

@[expose] def F618RecogE4 : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D →
    (∃ S : Sylow 2 D, Nonempty (↥S ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) →
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2 p 1 D

@[expose] def F618RecogD8 : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D →
    (∃ S : Sylow 2 D, Nonempty (↥S ≃* DihedralGroup 4)) →
    (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ IsL2 p e D) ∨
      IsHatAlt 6 D ∨ (∃ q : ℕ, q.Prime ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ IsPGL2 q D) ∨
      Nonempty (D ≃* ↥(alternatingGroup (Fin 7))) ∨ IsHatAlt 7 D

@[expose] def F618RecogZ2D8 : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D →
    (∃ S : Sylow 2 D, Nonempty (↥S ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) →
    (∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2FieldExtCat p D) ∨ IsHatSym 6 D ∨
      Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ IsHatSym 7 D

@[expose] def F618RecogZ4wrZ2 : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D →
    (∃ S : Sylow 2 D,
      Nonempty (↥S ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2))) →
    ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3 p D

@[expose] def F618RecogG22M12 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), F618RecogSetting D →
    IsGoldschmidtTriple G₁ G₂ → (IsGoldCaseG22 G₁ G₂ ∨ IsGoldCaseM12 G₁ G₂) →
    (∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3GraphExt p D) ∨ IsM12 D

@[expose] def F618RecogAutM12 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), F618RecogSetting D →
    IsGoldschmidtTriple G₁ G₂ → IsGoldCaseAutM12Cat G₁ G₂ → IsAutM12 D

@[expose] def G22PrimeSylowFact : Prop :=
  ∀ (W : Type) [Group W] [Finite W], IsG22Prime W → ∀ S : Sylow 2 W,
    Nonempty (↥S ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def G22AmalgamShapeFact : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (K₁ K₂ : Subgroup W), IsG22 W → IsTwoLocalAmalgam K₁ K₂ →
    QuotientPCoreIsL22 K₁ → QuotientPCoreIsL22 K₂ →
    IsSpecialTwoOnePlusFour ↥(pCoreOf 2 K₁) → Nat.card ↥(pCoreOf 2 K₂) = 2 ^ 5 →
    IsExtensionOf ↥(K₁ ⊓ K₂) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      IsCentralProduct₂ ↥(pCoreOf 2 K₁) (QuaternionGroup 2) (QuaternionGroup 2) ∧
      IsExtensionOf ↥K₂ (DihedralGroup 6) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def M12AmalgamShapeFact : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (K₁ K₂ : Subgroup W), IsM12 W → IsTwoLocalAmalgam K₁ K₂ →
    QuotientPCoreIsL22 K₁ → QuotientPCoreIsL22 K₂ →
    IsCentralProduct₂ ↥(pCoreOf 2 K₁) (QuaternionGroup 2) (QuaternionGroup 2) →
    Nat.card ↥(pCoreOf 2 K₂) = 2 ^ 5 →
    IsExtensionOf ↥(K₁ ⊓ K₂) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      IsExtensionOf ↥K₂ (DihedralGroup 6) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def AutM12AmalgamShapeFact : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (K₁ K₂ : Subgroup W), IsAutM12 W →
    IsTwoLocalAmalgam K₁ K₂ → QuotientPCoreIsL22 K₁ → QuotientPCoreIsL22 K₂ →
    IsExtensionWith ↥K₁ (DihedralGroup 6)
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) →
    Nat.card ↥(pCoreOf 2 K₁) = 2 ^ 6 → Nat.card ↥(centerOf (pCoreOf 2 K₁)) = 2 →
    Nat.card ↥(pCoreOf 2 K₂) = 2 ^ 6 →
    IsExtensionOf ↥(K₁ ⊓ K₂) (DihedralGroup 4)
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      IsExtensionOf₃ ↥K₂ (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def PGL2InspectionFact : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (Nat.card K).Prime →
    (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) →
    ∀ G₁ G₂ : Subgroup (GL (Fin 2) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K),
      IsGoldschmidtTriple G₁ G₂ →
      (IsGoldCaseIII G₁ G₂ → (Nat.card K % 24 = 11 ∨ Nat.card K % 24 = 13)) ∧
      ¬ IsGoldCaseIV G₁ G₂ ∧
      ¬ (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4)))

@[expose] def A7InspectionFact : Prop :=
  ∀ G₁ G₂ : Subgroup ↥(alternatingGroup (Fin 7)), IsGoldschmidtTriple G₁ G₂ →
    ¬ (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4)))

@[expose] def S7InspectionFact : Prop :=
  ∀ G₁ G₂ : Subgroup (Equiv.Perm (Fin 7)), IsGoldschmidtTriple G₁ G₂ →
    ¬ (Nonempty (↥G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (↥G₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def PSigmaL2InspectionFact : Prop :=
  ∀ (p : ℕ) (K : Type) [Field K] [Finite K], p.Prime → Nat.card K = p ^ 2 →
    (p % 8 = 3 ∨ p % 8 = 5) → ∀ G₁ G₂ : Subgroup ↥(PSigmaL2 K), IsGoldschmidtTriple G₁ G₂ →
      Nonempty (↥G₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4) → (p % 24 = 5 ∨ p % 24 = 19)

end F6

end CFSG.Quasithin
