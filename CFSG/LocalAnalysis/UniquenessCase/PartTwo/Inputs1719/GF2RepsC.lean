module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

@[expose] def centGroupIn (Y L : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  Y ⊓ Subgroup.centralizer (L : Set (MulAut W))

@[expose] def IsZ3xL2_64 (X : Type) [Group X] : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), Nonempty (X ≃* A × B) ∧
    IsCyclicOrd A 3 ∧ IsL2 B 6

@[expose] def IsSubgroupOfAlt (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ H : Subgroup ↥(alternatingGroup (Fin n)), Nonempty (X ≃* ↥H)

@[expose] def SumOfNatVia (D : FFModel) (H : Subgroup (MulAut W)) (U Z : Subgroup W)
    (k : ℕ) (π : D.Gam →* ↥H) : Prop :=
  ∃ I : Fin k → Subgroup W, (∀ i, Z ≤ I i) ∧
    (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ Z) ∧
    (Z ⊔ ⨆ i, I i) = U ∧ ∀ i, D.RealizesVia H (I i) Z π

@[expose] def IsM10 (X : Type) [Group X] : Prop :=
  ∃ φ : X →* Multiplicative (ZMod 2), Function.Surjective φ ∧
    Nonempty (↥φ.ker ≃* ↥(alternatingGroup (Fin 6))) ∧
    ∀ x : X, x ∉ φ.ker → x ^ 2 ≠ 1

@[expose] noncomputable def commPset (Y X : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  ⨆ (A : Subgroup (MulAut W)) (_ : A ∈ Pset Y), ⁅A, X⁆

@[expose] def Is135Context (Y L : Subgroup (MulAut W)) : Prop :=
  IsKGroup ↥Y ∧ O2Trivial Y ∧ L ≤ Y ∧ Fstar Y = L ∧
    IsQuasisimple ↥L ∧ IsIrrOn L ⊤ ⊥

@[expose] def W4Lem13_5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), ∀ t : MulAut W,
      Is135Context Y L →
      t ∈ Y → orderOf t = 2 →
      E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 →
      (∃ n a : ℕ, a ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ∧
        ((IsSLn ↥L n a ∧ BinaryNaturalSL L ⊤ ⊥ n a) ∨
          (IsSpn ↥L n a ∧ NatSpn L ⊤ ⊥ n a) ∨
          ((IsOmegaPlus ↥L n a ∧ NatOmegaPlus L ⊤ ⊥ n a) ∨
            (IsOmegaMinus ↥L n a ∧ NatOmegaMinus L ⊤ ⊥ n a)))) ∨
        (∃ n : ℕ,
          (IsSLn ↥L n 1 ∧ BinaryNaturalSL L ⊤ ⊥ n 1) ∨
          (IsSpn ↥L n 1 ∧ NatSpn L ⊤ ⊥ n 1) ∨
          (IsOmegaPlus ↥L n 1 ∧ NatOmegaPlus L ⊤ ⊥ n 1) ∨
          (IsOmegaMinus ↥L n 1 ∧ NatOmegaMinus L ⊤ ⊥ n 1) ∨
          (IsSUn ↥L n 1 ∧ NatSUn L ⊤ ⊥ n 1) ∨
          (LieModel ↥L .PSU 3 3 1 ∧ G2NaturalDerived L ⊤ ⊥ 1)) ∨
        (IsHat ↥L ↥(alternatingGroup (Fin 6)) ∧ Nat.card W = 2 ^ 6) ∨
        (∃ (S : Type) (_ : Group S), LieModel S .PSU 4 3 1 ∧ IsHat ↥L S ∧
          Nat.card W = 2 ^ 12) ∨
        (∃ n : ℕ, IsAlt ↥L n ∧ AlternatingNatural L ⊤ ⊥ n) ∨
        (IsAlt ↥L 7 ∧ Nat.card W = 2 ^ 4) ∨
        (IsSpn ↥L 6 1 ∧ Nat.card W = 2 ^ 8) ∨
        (IsSLn ↥L 5 1 ∧ Nat.card W = 2 ^ 10) ∨
        (IsSpor ↥L .M22 ∧ Nat.card W = 2 ^ 10) ∨
        (LieModel ↥L .PSL 3 2 2 ∧ Nat.card W = 2 ^ 9) ∨
        (IsL3 ↥L 1 ∧ Nat.card W = 2 ^ 8)

@[expose] def W4Thm13_10 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L K : Subgroup (MulAut W),
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      IsComponentOf L Y → IsComponentOf K Y → L ≠ K →
      (∃ t : MulAut W, t ∈ Y ∧ orderOf t = 2 ∧
        E3.mQuot (⊤ : Subgroup W) (fixV (Subgroup.zpowers t)) ≤ 3) →
      Opp 3 Y = L ⊔ K →
      IsAlt ↥K 5 →
      (IsAlt ↥L 5 ∨ LieModel ↥L .PSU 3 2 2) →
      IsOmegaPlus ↥(L ⊔ K) 4 2 ∧ Opp 5 Y = L ⊔ K ∧
        (∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) ∧
        (commSub (commSub (⊤ : Subgroup W) L) K = ⊥ ∨
          NatOmegaPlus (L ⊔ K) ⊤ ⊥ 4 2)

@[expose] def W4Thm14_3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), ∀ n : ℕ,
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      L ≤ Y → (L.subgroupOf Y).Normal →
      (IsL2 ↥L n ∨ IsSz ↥L n) → 3 ≤ n → n ≠ 4 →
      bParam L Y + 2 ≥ E3.mParam Y →
      IsL2 ↥L n ∧
        (BinaryNaturalSL L ⊤ (fixV L) 2 n ∨
          (Even n ∧ NatOmegaMinus L ⊤ ⊥ 4 (n / 2)))

@[expose] def W4Thm14_4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L₁ L₂ X : Subgroup (MulAut W),
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      IsComponentOf L₁ Y → IsComponentOf L₂ Y → IsAlt ↥L₁ 5 → IsAlt ↥L₂ 5 →
      L₁ ≤ Y → L₂ ≤ Y → L₁ ≠ L₂ → X = L₁ ⊔ L₂ → (X.subgroupOf Y).Normal →
      bParam L₁ Y = 2 → bParam L₂ Y = 2 →
      fixV X = ⊥ → E3.mParam Y = 4 →
      ((L₁.subgroupOf Y).Normal → (L₂.subgroupOf Y).Normal → fixV L₁ = ⊥ ∧ fixV L₂ = ⊥) →
      ((∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∧
          commSub (commSub (⊤ : Subgroup W) L₁) L₂ = ⊥) ∨
        ((∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∧
          IsOmegaPlus ↥X 4 2 ∧
          SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2) ∨
        (IsOmegaPlus ↥X 4 2 ∧ NatOmegaPlus X ⊤ ⊥ 4 2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
