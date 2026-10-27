module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def FFModel.ofSec {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (I Z : Subgroup V) :
    FFModel where
  Gam := ↥L
  Amb := V
  act l v := (l : MulAut V) v
  sec := I
  ker := Z

section Vocabulary

variable {V : Type} [CommGroup V]

@[expose] def SecIsoL (L : Subgroup (MulAut V)) (I Z I' Z' : Subgroup V) : Prop :=
  (FFModel.ofSec L I' Z').RealizesVia L I Z (MonoidHom.id ↥L)

@[expose] def DirectSumOfCopies (L : Subgroup (MulAut V)) (U Z : Subgroup V) (D : FFModel) (k : ℕ) :
    Prop :=
  ∃ (I : Fin k → Subgroup V) (π : D.Gam →* ↥L),
    (∀ i, Z ≤ I i) ∧ (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = Z) ∧
    (Z ⊔ ⨆ i, I i) = U ∧ ∀ i, D.RealizesVia L (I i) Z π

@[expose] def HomogeneousSec (L : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (U ≤ Z ⊔ ⨆ (I : Subgroup V) (_ : Z ≤ I ∧ I ≤ U ∧ XMod.IsInv ↥L I ∧ XMod.IsIrrSec ↥L Z I), I) ∧
    ∀ I I' : Subgroup V,
      (Z ≤ I ∧ I ≤ U ∧ XMod.IsInv ↥L I ∧ XMod.IsIrrSec ↥L Z I) →
      (Z ≤ I' ∧ I' ≤ U ∧ XMod.IsInv ↥L I' ∧ XMod.IsIrrSec ↥L Z I') → SecIsoL L I Z I' Z

@[expose] def IsFFStarOffenderOn (G A : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  A ≤ G ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    ∀ B : Subgroup (MulAut V), B ≤ A →
      Nat.card B * Nat.card ↥(fixV B ⊓ U) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U)

@[expose] def IsIntDirect (X Y U : Subgroup V) : Prop := X ⊔ Y = U ∧ X ⊓ Y = ⊥

@[expose] def B42ModulePair (L : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSL L U Z 3 n) ∨
  (∃ n, BinaryNaturalSp4 L U Z n) ∨ (∃ n, G2Natural L U Z n) ∨ G2NaturalDerived L U Z 1 ∨
  AlternatingNatural L U Z 5 ∨ AlternatingNatural L U Z 6 ∨ AlternatingNatural L U Z 7 ∨
  A7Four L U Z ∨ TripleA6Six L U Z ∨ BinaryNaturalSL L U Z 4 1 ∨ BinaryNaturalSL L U Z 5 1 ∨
  SLExteriorTwo L U Z 4 ∨ SLExteriorTwo L U Z 5

@[expose] def B51NaturalList2 (L : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSp4 L U Z n) ∨ (∃ n, G2Natural L U Z n) ∨
  AlternatingNatural L U Z 6 ∨ AlternatingNatural L U Z 8 ∨ G2NaturalDerived L U Z 1 ∨
  BinaryNaturalSL L U Z 3 1

@[expose] def B51NaturalList5 (L : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (∃ n, BinaryNaturalSp4 L U Z n) ∨ AlternatingNatural L U Z 6 ∨ AlternatingNatural L U Z 8 ∨
  BinaryNaturalSL L U Z 3 1

end Vocabulary

section B51

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B51Hyp (G L : Subgroup (MulAut V)) : Prop :=
  quasithinGenFitting G = L ⊔ centerOf G ∧ CFSG.IsQuasisimple ↥L ∧ SQTKGroup ↥L ∧ L ≤ G ∧
    pCoreOf 2 G = ⊥ ∧ G = ffJ G

variable (G L : Subgroup (MulAut V))

@[expose] def B51Case1i : Prop :=
  commV L ∈ IrrPlus L ⊤ ∧ B42ModulePair L (commV L) (fixV L ⊓ commV L) ∧
    ∀ T, IsSylowTwoOf T G →
      (G = L ∨ (G = L ⊔ T ∧
        ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural G (commV L) (fixV L ⊓ commV L) n) ∨
          G2Natural G (commV L) (fixV L ⊓ commV L) 1)))

@[expose] def B51Case1ii : Prop :=
  G = L ∧ ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    ∃ (I : Fin 2 → Subgroup V) (π : ↥(StatedSL 3 K) →* ↥L),
      iSupIndep I ∧ (⨆ i, I i) = commV L ∧
      (∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) ⊥ π) ∧
      (∀ A : Subgroup (MulAut V), IsFFStarOffenderOn G A (commV L) ↔
        A ≤ L ∧ ∃ W : Submodule K (Fin 3 → K), Module.finrank K W = 2 ∧
          ∀ g : ↥(StatedSL 3 K), g ∈ (A.subgroupOf L).comap π ↔
            (∀ w ∈ W, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) ∧
              ∀ v, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ W) ∧
      qOf G = ((1 : ℚ) : WithTop ℚ)

@[expose] def SumNatDual (L : Subgroup (MulAut V)) (U : Subgroup V) (n : ℕ) : Prop :=
  (n = 4 ∨ n = 5) ∧ ∃ (π : ↥(StatedSL n (ZMod 2)) →* ↥L) (U₁ U₂ : Subgroup V),
    IsIntDirect U₁ U₂ U ∧ (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L U₁ ⊥ π ∧
      (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia L U₂ ⊥ π

@[expose] def B51Case1iii (n : ℕ) : Prop :=
  G = L ∧ SumNatDual L (commV L) n

@[expose] def B51Case1iv : Prop :=
  G = L ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 1 ∧
    DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k

@[expose] def B51Part1 : Prop :=
  quasithinGenFitting G = L ∧
    (B51Case1i G L ∨ B51Case1ii G L ∨ (∃ n, B51Case1iii G L n) ∨ B51Case1iv G L)

@[expose] def B51Part2 : Prop :=
  (¬ IsIntDirect (commV L) (fixV L) ⊤ ↔ (fixV L ⊓ commV L ≠ ⊥ ∨ commV L ⊔ fixV L < ⊤)) ∧
    (¬ IsIntDirect (commV L) (fixV L) ⊤ →
      commV L ∈ IrrPlus L ⊤ ∧ B51NaturalList2 L (commV L) (fixV L ⊓ commV L))

@[expose] def B51Part3 : Prop :=
  HomogeneousSec L (commV L) (fixV L ⊓ commV L) ∨ ∃ n, SumNatDual L (commV L) n

@[expose] def B51Part4 : Prop :=
  ¬ IsIntDirect (commV L) (fixV G) ⊤ →
    commV L ∈ IrrPlus L ⊤ ∧
      (¬ IsIntDirect (commV L) (fixV L) ⊤ ∨
        (IsIntDirect (commV L) (fixV L) ⊤ ∧
          (∃ n, (n = 6 ∨ n = 8) ∧ SymmetricNatural G (commV L) ⊥ n) ∧
          (fixV G).relIndex (fixV L) = 2))

@[expose] def B51Part5 : Prop :=
  commV L ⊔ fixV G = ⊤ ∨
    (commV L ∈ IrrPlus L ⊤ ∧ B51NaturalList5 L (commV L) (fixV L ⊓ commV L) ∧
      (BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1 → fixV L ⊓ commV L = ⊥))

@[expose] def B51Part6 : Prop :=
  ∀ n, B51Case1iii G L n → ∀ T, IsSylowTwoOf T G →
    (∃ R : Subgroup (MulAut V), R ≤ L ⊓ centSub (fixV T) ∧ IsPGroup 2 R ∧
        Nat.card R = 2 ^ (1 + 2 * (n - 2)) ∧
        ∃ _ : (R.subgroupOf (L ⊓ centSub (fixV T))).Normal,
          Nonempty (↥(L ⊓ centSub (fixV T)) ⧸
            R.subgroupOf (L ⊓ centSub (fixV T)) ≃*
              Matrix.GeneralLinearGroup (Fin (n - 2)) (ZMod 2))) ∧
      ∀ A, IsFFStarOffender G A → ¬ A ≤ pCoreOf 2 (G ⊓ centSub (fixV T))

end B51

@[expose] def B51Conclusion {V : Type} [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) : Prop :=
  B51Part1 G L ∧ B51Part2 L ∧ B51Part3 L ∧ B51Part4 G L ∧ B51Part5 G L ∧ B51Part6 G L

@[expose] def AsB51 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → B51Conclusion G L

section B56

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B53Hyp (G : Subgroup (MulAut V)) : Prop :=
  pCoreOf 2 G = ⊥ ∧ G = ffJ G ∧
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (N : Subgroup X) (_ : N.Normal),
      SQTKGroup X ∧ Nonempty (↥G ≃* X ⧸ N)

@[expose] def B56QuasisimpleList (X : Type) [Group X] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 2 K))) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 3 K))) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSp 2 K))) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(CFSG.Open.quasithinG2 K))) ∨
  IsAlt 6 X ∨ IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 6)) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆)) ∨
  Nonempty (X ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (X ≃* ↥(StatedSL 5 (ZMod 2)))

@[expose] def B56FactorList (X : Type) [Group X] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 2 K))) ∨
  Nonempty (X ≃* Equiv.Perm (Fin 5)) ∨
  (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ m ∧ Odd m ∧ Nat.card K = 2 ^ m ∧
      Nonempty (X ≃* ↥(StatedSL 3 K)))

@[expose] def B56Piece (Gi : Subgroup (MulAut V)) (Wi C : Subgroup V) : Prop :=
  (Wi = commV Gi ⊔ C ∧
    ((∃ n, BinaryNaturalSL Gi Wi C 2 n) ∨ SymmetricNatural Gi Wi C 5 ∨
      (∃ m, BinaryNaturalSL Gi Wi C 3 m))) ∨
  (Wi = commV Gi ⊔ C ∧ ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      DirectSumOfCopies Gi Wi C (FFModel.nat (StatedSL 3 K)) 2) ∨
  (Nonempty (↥Gi ≃* ↥(StatedSL 3 (ZMod 2))) ∧ commV Gi ≤ Wi ∧ Nat.card ↥Wi = 2 ^ 4 * Nat.card ↥C ∧
    (¬ ∃ A B : Subgroup V, C < A ∧ C < B ∧ XMod.IsInv ↥Gi A ∧ XMod.IsInv ↥Gi B ∧
      A ⊔ B = Wi ∧ A ⊓ B = C) ∧
    BinaryNaturalSL Gi (modComm Gi Wi ⊔ C) C 3 1)

@[expose] def B56Case1 (G : Subgroup (MulAut V)) : Prop :=
  CFSG.IsQuasisimple ↥(quasithinGenFitting G) ∧ B51Conclusion G (quasithinGenFitting G) ∧
    B56QuasisimpleList ↥(quasithinGenFitting G)

@[expose] def B56Case2 (G : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥G ≃* Equiv.Perm (Fin 3)) ∧ IsIntDirect (commV G) (fixV G) ⊤ ∧
    Nat.card ↥(commV G) = 2 ^ 2

@[expose] def B56Case3 (G : Subgroup (MulAut V)) : Prop :=
  ∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = G ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
    B56FactorList ↥G₁ ∧ B56FactorList ↥G₂ ∧
    ∃ W₁ W₂ : Subgroup V, fixV G ≤ W₁ ∧ fixV G ≤ W₂ ∧ XMod.IsInv ↥G W₁ ∧ XMod.IsInv ↥G W₂ ∧
      W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV G ∧ B56Piece G₁ W₁ (fixV G) ∧ B56Piece G₂ W₂ (fixV G)

@[expose] def B56Case4 (G : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (t : MulAut V),
    G = (G₁ ⊔ G₂) ⊔ Subgroup.zpowers t ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
    Nonempty (↥G₁ ≃* ↥(alternatingGroup (Fin 6))) ∧ Nat.card ↥G₂ = 3 ∧
    fixV G ⊔ (commV G₁ ⊔ commV G₂) = ⊤ ∧ fixV G ⊓ (commV G₁ ⊔ commV G₂) = fixV G₁ ⊓ commV G₁ ∧
    IsIntDirect (commV G₁) (commV G₂) (commV G₁ ⊔ commV G₂) ∧
    (Nat.card ↥(commV G₁) = 2 ^ 4 ∨ Nat.card ↥(commV G₁) = 2 ^ 5) ∧ Nat.card ↥(commV G₂) = 2 ^ 2 ∧
    t ∈ Subgroup.normalizer (G₁ : Set (MulAut V)) ∧ t ∈ Subgroup.normalizer (G₂ : Set (MulAut V)) ∧
    (¬ ∃ g ∈ G₁, ∀ x ∈ G₁, t * x * t⁻¹ = g * x * g⁻¹) ∧
    (¬ ∃ g ∈ G₂, ∀ x ∈ G₂, t * x * t⁻¹ = g * x * g⁻¹)

@[expose] def B56Case5 (G : Subgroup (MulAut V)) : Prop :=
  ∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = G ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
    IsIntDirect (commV G₁) (commV G₂) (commV G) ∧ Nonempty (↥G₁ ≃* ↥(StatedSL 3 (ZMod 2))) ∧
    Nat.card ↥(commV G₁) = 2 ^ 3 ∧ (commV G ⊔ fixV G).index = 2 ∧
    ((Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))) ∧ ∃ k : ℕ, k ≤ 2 ∧
        DirectSumOfCopies G₂ (commV G₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) ∨
      ∃ n, BinaryNaturalSL G₂ (commV G₂) (fixV G₂ ⊓ commV G₂) 2 n)

end B56

@[expose] def AsB56 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), G ≠ ⊥ → B53Hyp G →
      B56Case1 G ∨ B56Case2 G ∨ B56Case3 G ∨ B56Case4 G ∨ B56Case5 G

end CFSG.Quasithin
