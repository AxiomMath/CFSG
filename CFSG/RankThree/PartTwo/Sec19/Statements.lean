module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec8.Groups
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)

section Notation

variable {G : Type*} [Group G]

@[expose] def starIm (K X : Subgroup G) : Subgroup (K ⧸ CFSG.pCore 2 K) :=
  (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))

@[expose] def oTwoZ (K : Subgroup G) : Subgroup G :=
  ((Subgroup.center (K ⧸ CFSG.pCore 2 K)).comap (QuotientGroup.mk' (CFSG.pCore 2 K))).map
    K.subtype

@[expose] def oUpperThreePrime {Y : Type*} [Group Y] (X : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {y | y ∈ X ∧ ∃ k : ℕ, y ^ 3 ^ k = 1}

@[expose] def IsProperParabolic {Y : Type*} [Group Y] (P : Subgroup Y) : Prop :=
  P ≠ ⊤ ∧ ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ P

end Notation

@[expose] def IsList194 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Sec8.IsoGTwoEven X n)) ∨
  Nonempty (X ≃* projSU 4 2 1) ∨ Nonempty (X ≃* projSU 4 2 3) ∨
  Nonempty (X ≃* projSL 4 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨
  Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 6 (GaloisField 2 1)) ∨
  Nonempty (X ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨
  (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
    Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
  Nonempty (X ≃* alternatingGroup (Fin 10))

@[expose] def Item194 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) →
      H ∈ scriptM (A : Set G) → H ≠ M →
      (scriptJ M H).Nonempty ∧
      (∀ K ∈ scriptJ M H,
        CFSG.Open.pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) ∧
        IsList194 (K ⧸ CFSG.pCore 2 K) ∧
        ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            IsProperParabolic (starIm K H)) ∨
          (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2)))) ∧
        ((∃ n : ℕ, 1 ≤ n ∧ 2 ^ n % 3 = 1 ∧
            Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) →
          ∀ J ∈ oTwoComponentsIn M, J ≠ K →
            oTwoZ K ⊔ CFSG.Open.pCoreOf 2 M ≠ oTwoZ J ⊔ CFSG.Open.pCoreOf 2 M)) ∧
      ∀ m ∈ M, (∀ K ∈ scriptJ M H, ∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) →
        m ∈ H

@[expose] def Item195 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G → ∀ A ∈ partTwoE G, A ∉ partTwoT G → HypS A

structure Ctx1912 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G) :
    Prop extends Sec19Std G where
  mem_partTwoE : A ∈ partTwoE G
  not_mem_partTwoT : A ∉ partTwoT G
  zpowers_mem_omegaA : Subgroup.zpowers c ∈ omegaA A
  mem_lA : L ∈ lA A c
  mem_partTwoT : E ∈ partTwoT G
  le_centralizer : E ≤ Subgroup.centralizer ({c} : Set G)
  mem_scriptM : M ∈ scriptM (gamma 2 E : Set G)
  isPGroup_sup : IsPGroup 3 (E ⊔ A : Subgroup G)
  hypS : HypS A
  chosen136 : Chosen136 A

@[expose] def Step1913 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M →
      IsLThreePi (L ⧸ CFSG.pCore 2 L) ∨
        Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] def Step1914 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M →
      (L ≤ M ∨
        (Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) ∧
          E = Subgroup.zpowers c ⊔ (E ⊓ L) ∧ Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥) ∨
        Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)) ∧
      (¬ L ≤ M →
        Sec4.IsExtOf
          (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
          (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))

@[expose] def Step1915 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M →
      ∃ K ∈ oTwoComponentsIn M, L ≤ K ∧
        (K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
            Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧
            KFacts.InducesStdKind K c .field) ∨
          (Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) ∧
            CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 2 2 ∧
            KFacts.InducesStdKind K c .graphField))

@[expose] def Step1916D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → Nat.card (A ⊓ E : Subgroup G) = 9

@[expose] def Step1917 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M → gammaOne (A ⊓ E) ≤ M

@[expose] def Step1918 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M

@[expose] def Step1919O2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      2 < Nat.card (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)

@[expose] def Step1919 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        ∃ K ∈ scriptJ M H, E ≤ K

@[expose] def Step1919End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        ∀ K ∈ scriptJ M H, E ≤ K → False

end CFSG.RankThree.PartTwo.Sec19
