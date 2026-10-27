module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def IsQuad417 (L A E : Subgroup G) (c : G) (m : ℕ) : Prop :=
  Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A ∧ Nat.card A = 3 ^ m ∧
    A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c ∧ orderOf c = 3 ∧
    Late.IsE27 E ∧ E ≤ A ∧
    ∃ T ∈ invariantPiSubgroups L E (piOf 2), ¬ T ≤ Subgroup.centralizer (E : Set G)

@[expose] def Table417 (L A : Subgroup G) : Prop :=
  (Nonempty (L ≃* NativeSporadic.M12) ∧ Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
  (Nonempty (L ≃* NativeSporadic.M22) ∧ Nonempty (autIn L A ≃* QuaternionGroup 2)) ∨
  (Nonempty (L ≃* NativeSporadic.M23) ∧
    Nonempty (autIn L A ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  (Nonempty (L ≃* NativeSporadic.M24) ∧
    (Nonempty (autIn L A ≃* DihedralGroup 6) ∨ Nonempty (autIn L A ≃* GL (Fin 2) (ZMod 3)))) ∨
  (Nonempty (L ≃* NativeSporadic.J2) ∧ Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
  (Nonempty (L ≃* NativeSporadic.J4) ∧ Nonempty (autIn L A ≃* GL (Fin 2) (ZMod 3))) ∨
  (Nonempty (L ≃* NativeSporadic.HS) ∧
    Nonempty (autIn L A ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  (Nonempty (L ≃* NativeSporadic.He) ∧
    (Nonempty (autIn L A ≃* DihedralGroup 6) ∨ Nonempty (autIn L A ≃* GL (Fin 2) (ZMod 3)))) ∨
  (Nonempty (L ≃* NativeSporadic.Ru) ∧ Nonempty (autIn L A ≃* GL (Fin 2) (ZMod 3)))

@[expose] def Alt417 (L A : Subgroup G) (m : ℕ) : Prop :=
  (∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∨
  (m = 3 ∧ IsHeisCentral ↥(A ⊔ L) ↥L ∧
    (IsTripleCover ↥L (alternatingGroup (Fin 7)) ∨ IsTripleCover ↥L NativeSporadic.M22)) ∨
  (m = 3 ∧ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    (ChevalleyExceptionalModel ↥L .G2 p 1 ∨ Nonempty (L ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (L ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (L ≃* projSL 4 (GaloisField p 1))) ∨
      ∃ e : ℕ, 1 ≤ e ∧ (IsSLThreePiAt ↥L (p ^ e) ∨ IsoLThreePi ↥L p e))) ∨
  (m = 3 ∧ Nonempty (L ≃* alternatingGroup (Fin 7)) ∧
    Nonempty (autIn L A ≃* Multiplicative (ZMod 4))) ∨
  (m = 4 ∧ Nonempty (L ≃* alternatingGroup (Fin 9)) ∧
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 4))) ∨
  (m = 3 ∧ Table417 L A) ∨
  (m = 4 ∧ (Nonempty (L ≃* NativeSporadic.J3) ∨ IsTripleCover ↥L NativeSporadic.J3) ∧
    IsExtOf ↥(autIn L A) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))) ∨
  (m = 3 ∧ IsTripleCover ↥L NativeSporadic.ON) ∨
  (m = 3 ∧ (∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (L ≃* projSL 3 (GaloisField 2 n)) ∧ IsTypeCOn A L) ∨
        (IsSLThreePiAt ↥L (2 ^ n) ∧ IsTypeCOnSL A L))) ∧
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
  (m = 3 ∧ (∃ n : ℕ, 0 < n ∧ Even n ∧
      (ChevalleyExceptionalModel ↥L .G2 2 n ∨ ChevalleyExceptionalModel ↥L .trialityD4 2 n)) ∧
    Nonempty (autIn L A ≃* DihedralGroup 6)) ∨
  (m = 3 ∧ ((∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (L ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (L ≃* projSU 4 2 n))) ∨
      Nonempty (L ≃* projSU 5 2 2) ∨ Nonempty (L ≃* projSL 4 (GaloisField 2 1)) ∨
      Nonempty (L ≃* projSL 5 (GaloisField 2 1))) ∧
    Nonempty (autIn L A ≃* DihedralGroup 4)) ∨
  (m = 4 ∧ (∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) ∧
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 4))) ∨
  (m = 4 ∧ Nonempty (L ≃* projSp 3 (GaloisField 2 1)) ∧
    Nonempty (autIn L A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Item4_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pCore 2 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L →
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) →
    ∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → Alt417 L A m

end CFSG.RankThree.PartTwo.Sec4
