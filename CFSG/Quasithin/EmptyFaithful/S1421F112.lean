module

public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsCommutingGeneration {P : Type*} [Group P] (A B : Subgroup P) : Prop :=
  A ≤ Subgroup.centralizer (B : Set P) ∧ A ⊔ B = ⊤

@[expose] def IsZ4StarQ8 (P : Type*) [Group P] : Prop :=
  Nat.card P = 16 ∧ ∃ A B : Subgroup P, IsCommutingGeneration A B ∧ Nat.card A = 4 ∧ IsCyclic A ∧
    Nonempty (B ≃* QuaternionGroup 2)

@[expose] def IsQ8D8 (P : Type*) [Group P] : Prop :=
  Nat.card P = 32 ∧ ∃ A B : Subgroup P, IsCommutingGeneration A B ∧
    Nonempty (A ≃* QuaternionGroup 2) ∧ Nonempty (B ≃* DihedralGroup 4)

@[expose] def IsQ8Sq (P : Type*) [Group P] : Prop :=
  Nat.card P = 32 ∧ ∃ A B : Subgroup P, IsCommutingGeneration A B ∧
    Nonempty (A ≃* QuaternionGroup 2) ∧ Nonempty (B ≃* QuaternionGroup 2)

@[expose] def IsZ4Sq (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsAutM12Vertex {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  (∃ φ : ↥L →* DihedralGroup 6, Function.Surjective φ ∧ IsQ8Sq ↥φ.ker) ∧
    Nat.card (pCoreOf 2 L) = 2 ^ 6 ∧ Nat.card (centerOf (pCoreOf 2 L)) = 2

@[expose] def IsL2Quot (f : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))

@[expose] def IsQuasithinSub {G : Type*} [Group G] [Finite G] (X : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup G, R ≤ X → R ≠ ⊥ → IsPGroup 2 R →
    CFSG.Open.pRank p (X ⊓ Subgroup.normalizer (R : Set G)) ≤ 2

@[expose] def IsAmalgamOfGroup (α : RankTwoAmalgam.{0}) (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∃ (Y : Type) (_ : Group Y), P Y ∧ ∃ T : Subgroup Y, IsYAmalgam α T

@[expose] def IsParabolicAmalgamOfGroup (α : RankTwoAmalgam.{0})
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∃ (Y : Type) (_ : Group Y), P Y ∧ ∃ T : Subgroup Y, IsParabolicYAmalgam α T

@[expose] def IsLieOverTwo (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ) (Y : Type) [Group Y] : Prop :=
  CFSG.Blueprint.LieModel Y t n 2 f

@[expose] def IsSp4Over (f : ℕ) (Y : Type) [Group Y] : Prop :=
  (f = 1 ∧ Nonempty (Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 2)))) ∨ (2 ≤ f ∧ IsLieOverTwo .PSp 2 f Y)

@[expose] def IsG2Over (f : ℕ) (Y : Type) [Group Y] : Prop :=
  (f = 1 ∧ Nonempty (Y ≃* MulAut (PSU3 3 1))) ∨ (2 ≤ f ∧ IsLieOverTwo .G2 0 f Y)

@[expose] def IsTwistedF4Over (f : ℕ) (Y : Type) [Group Y] : Prop :=
  (f = 1 ∧ Nonempty (Y ≃* MulAut quasithinTits)) ∨ (3 ≤ f ∧ Odd f ∧ IsLieOverTwo .twistedF4 0 f Y)

@[expose] def IsU4ExtTwo (f : ℕ) (α : RankTwoAmalgam.{0}) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (Ŷ : Type) (_ : Group Ŷ) (ι : Y →* Ŷ), IsLieOverTwo .PSU 4 f Y ∧
    Function.Injective ι ∧ ι.range.index = 2 ∧ ∃ T : Subgroup Ŷ, IsYAmalgam α T

@[expose] def IsOmega4MinusType {G : Type*} [Group G] (L : Subgroup G) (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ (2 * f) ∧
    ∃ α : L →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
    ∃ β : blockU L →* Multiplicative (Matrix (Fin 2) (Fin 2) F),
      (∀ X : Matrix (Fin 2) (Fin 2) F,
        (∃ u, Multiplicative.toAdd (β u) = X) ↔ X.map (· ^ 2 ^ f) = X.transpose) ∧
      β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ ℓ : L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (β u) *
            ((α ℓ : Matrix (Fin 2) (Fin 2) F).map (· ^ 2 ^ f)).transpose

section Statement

variable {G : Type} [Group G]

@[expose] def F112ListBare (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥L1 ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥L2 ≃* Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ S)) ∧ Nat.card (pCoreOf 2 (L2 ⊔ S)) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 L1) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∧ Nat.card (pCoreOf 2 L1) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧
      IsOmega4MinusType L2 f ∧ (f = 1 → IsAltType L2 5)) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 L1) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 L2) = 2 ^ 16) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
      IsZ4StarQ8 ↥(pCoreOf 2 (L1 ⊔ S)) ∧ IsZ4Sq ↥(pCoreOf 2 (L2 ⊔ S))) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L1 ≃* ↥(Sz 0))) ∧
      Nat.card (pCoreOf 2 L1) = 2 ^ 9 ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 10) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsQ8Sq ↥(pCoreOf 2 L1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 5) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsAutM12Vertex L1 ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6)

@[expose] def F112List (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧
      IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∨ (a = 0 ∧ Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧
      IsOmega4MinusType L2 f ∧ (f = 1 → IsAltType L2 5)) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 16) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
      IsZ4StarQ8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsZ4Sq ↥(pCoreOf 2 (L2 ⊔ bigB L1 L2 S))) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L1 ≃* ↥(Sz 0))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = 2 ^ 9 ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 10) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧
      IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsQ8Sq ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 5) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsAutM12Vertex (L1 ⊔ bigB L1 L2 S) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6)

@[expose] def F112Second (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2) ∨
  IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 1) ∨ IsAmalgamOfGroup α (IsSp4Over 1) ∨
  IsAmalgamOfGroup α (IsG2Over 1) ∨ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∨
  IsAmalgamOfGroup α (IsTwistedF4Over 1) ∨
  IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∨
  IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 1) ∨
  IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∨
  IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∨
  IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∨
  IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∨
  IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsU4ExtTwo f α)

end Statement

@[expose] def F112LegacyPrintedError : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨ centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112ListBare L1' L2' S ∧ F112Second L1' L2' S

section CanonicalHypotheses

variable {G : Type} [Group G]

@[expose] def F112Hyp [Finite G] (L1 L2 S : Subgroup G) : Prop :=
  Hyp111 L1 L2 S ∧ IsQuasithinSub (L1 ⊔ L2 ⊔ S) ∧
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal)

end CanonicalHypotheses

@[expose] def F112Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨ centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112List L1' L2' S ∧ F112Second L1' L2' S

end CFSG.Quasithin
