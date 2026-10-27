module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

section Defs

variable {G : Type} [Group G]

@[expose] def IsCartanX (T L X : Subgroup G) : Prop :=
  QuasithinUnique.Lin2.IsHallTwoPrimeOf X (L ⊓ Subgroup.normalizer (TL T L : Set G))

@[expose] def List11_1_1Two (X : Type) [Group X] (n : ℕ) : Prop :=
  IsSL3 (2 ^ n) X ∨ IsPSL 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X ∨ Is2F4 n X ∨ Is3D4 2 n X ∨
    (3 ∣ n ∧ Is3D4 2 (n / 3) X)

@[expose] def List11_1_1Three (X : Type) [Group X] : Prop :=
  IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7)) ∨
    (∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
    IsPSL 2 5 2 X ∨ (∃ s : Bool, IsSLEps3 s 5 X ∨ IsPSLEps3 s 5 1 X) ∨
    IsSporadic .M22 X ∨ IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
    IsSporadic .M23 X ∨ IsSporadic .J1 X ∨ IsSporadic .J2 X ∨ IsSporadic .J4 X ∨
    IsSporadic .HS X ∨ IsSporadic .Ru X ∨ A36Case4 X ∨
    ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X) ∧
      NaturalSL2Action p X (CFSG.fittingSubgroup X)

abbrev oTwoTwoPrime (K : Subgroup G) : Subgroup G :=
  preimageModTwoCore K (CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K))

@[expose] def Case11_1_2One (K : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p = 5 ∨ 11 ≤ p) ∧
    ∃ φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
      Function.Surjective φ ∧ φ.ker = (oTwoTwoPrime K).subgroupOf K

@[expose] def Case11_1_2Two (L K : Subgroup G) : Prop :=
  (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
    ¬ IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Case11_1_2Three [Finite G] (T L K X L₁ L₂ : Subgroup G) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(K ⊔ X) ⧸ CFSG.pCore 2 ↥(K ⊔ X) ≃*
      (Matrix.GeneralLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))) ∧
  (∃ K₀ : Subgroup G, quasithinIsLocal T K₀ ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ L₁) ∧
  ∀ K₀ : Subgroup G, quasithinIsLocal T K₀ → K₀ ≤ K → K₀ ≠ K → K₀ ≠ L₁ →
    quasithinIsMaximalLocal T (K₀ ⊔ L₂) ∧ quasithinIsFaithfulLocal T (K₀ ⊔ L₂) ∧
    ¬ K₀ ≤ Subgroup.normalizer (L : Set G) ∧
    (∃ I' U : Subgroup G, FSU G T (K₀ ⊔ L₂) I' ∧ IsVi T (K₀ ⊔ L₂) I' 2 2 U ∧
      LOf (K₀ ⊔ L₂) U = L₂) ∧
    ((IsG2 2 2 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        IsPSp4 2 2 (↥(K₀ ⊔ L₂) ⧸ CFSG.pCore 2 ↥(K₀ ⊔ L₂))) ∨
      (IsG2 2 2 (↥(K₀ ⊔ L₂) ⧸ CFSG.pCore 2 ↥(K₀ ⊔ L₂)) ∧
        IsPSp4 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)))

end Defs

@[expose] def Stmt11_1_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n i : ℕ) (Vi V₀ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n i Vi →
    ((i = 1 ∧ V₀ ≠ ⊥ ∧ V₀ ≤ Vi ∧ QuasithinUnique.IsSylowTwoOf
        (T ⊓ Subgroup.normalizer (V₀ : Set G)) (Subgroup.normalizer (V₀ : Set G))) ∨
      (i = 2 ∧ V₀ = Vi)) →
      ∃ K : Subgroup G, LOf L Vi ≤ K ∧
        quasithinIsCComponent K (Subgroup.normalizer (V₀ : Set G)) ∧
        Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        (LOf L Vi = K ∨ List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
          (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)))

@[expose] def Stmt11_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n i : ℕ) (Vi V₁ V₂ X : Subgroup G),
    Hyp11 G T L I n → (i = 1 ∨ i = 2) → IsVi T L I n i Vi → IsVi T L I n 1 V₁ →
    IsVi T L I n 2 V₂ → IsCartanX T L X →
      ∃ K : Subgroup G, LOf L Vi ≤ K ∧
        quasithinIsCComponent K (Subgroup.normalizer (Vi : Set G)) ∧
        Subgroup.normalizer (Vi : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        QuasithinUnique.CharTwo K ∧
        (LOf L Vi = K ∨ (i = 1 ∧ n = 2 ∧ (Case11_1_2One K ∨ Case11_1_2Two L K ∨
          Case11_1_2Three T L K X (LOf L V₁) (LOf L V₂))))

@[expose] def Stmt11_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₂ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 2 V₂ →
      quasithinIsCComponent (LOf L V₂) (Subgroup.normalizer (V₂ : Set G)) ∧
      ¬ LOf L V₂ ≤ Subgroup.centralizer (V₂ : Set G) ∧
      ∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.normalizer (V₂ : Set G)) →
        ¬ K ≤ Subgroup.centralizer (V₂ : Set G) → K = LOf L V₂

@[expose] def Stmt11_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ →
      sectionCentralizer V₃ V₁ ≤ Subgroup.normalizer (L : Set G) ∧
      Subgroup.normalizer (V₃ : Set G) ⊓ Subgroup.normalizer (LOf L V₁ : Set G) ≤
        Subgroup.normalizer (L : Set G)

@[expose] def Stmt11_1_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) ∨
      (fsuV T I = VM T L I ∧ (IsSL3Block L ∨ IsSp4Block L) ∧
        T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ V₁ = omegaOneCenterOf (ROf T L V₁))

end CFSG.Quasithin.Vol2.Ch11
