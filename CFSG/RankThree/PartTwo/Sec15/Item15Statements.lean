module

public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaOneThree (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ x ^ 3 = 1}

@[expose] noncomputable def kerAO2 (A L : Subgroup G) : Subgroup ↥(A ⊔ L) :=
  (CFSG.Open.pCoreOf 2 L).subgroupOf (A ⊔ L)

omit [Finite G] in
theorem kerAO2_normal {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    (kerAO2 A L).Normal := by
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hAN : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hAL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hle : CFSG.Open.pCoreOf 2 L ≤ A ⊔ L :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_right
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (sup_le hAN hLN)

@[expose] def TransOmegaThree (A : Subgroup G) (c : G) : Prop :=
  (omegaA A).ncard = 3 ∧ ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
    F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom

@[expose] def WStarS4 (A : Subgroup G) : Prop :=
  Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))

@[expose] def MeetsY4 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (L Y : Subgroup G) :
    Prop :=
  ∃ X ∈ scriptY4 A LB, X ≤ L ⊓ Y

@[expose] noncomputable def Item152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M →
    generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∃ X ∈ thetaComponentsIn M, Y ≤ X ∧ X ∈ scriptY0 A LB

@[expose] noncomputable def Item153 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
        {Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)} ∧
      (∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
        S ∈ scriptQPiStar A LB ⊤ (piOf 2) ∧
          Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤
            Subgroup.normalizer
              (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) ∧
      generalizedFitting ↥Y = CFSG.pCore 2 ↥Y ∧
      ((Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
          Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) → ¬ IsShort Y)

@[expose] def Item156 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∧
      ¬ Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∧
      ¬ Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON

@[expose] def Item157 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] noncomputable def Item158 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0Star A LB, MeetsY4 A LB L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
          A = omegaOneThree P) ∨
        (Sec14.IsZ3PGLThreeAt ↥(lBarA c L (omegaOneThree P)) p e ∧
          (Nat.card ↥(omegaOneThree P ⊔ L)).factorization 3 = 4 ∧
          (Nat.card ↥((omegaOneThree P ⊔ L) ⊓ Subgroup.normalizer (Y : Set G))).factorization 3 =
            4 ∧
          ∀ F : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 F (Subgroup.zpowers c ⊔ L) →
              F ∈ partTwoF G ∧
                omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c) ∧
                (omegaA F).ncard = 9)

@[expose] noncomputable def Item159 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) →
    Nat.card ↥(A ⊓ L) = 9 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
        WStarS4 A ∧ TransOmegaThree A c) ∨
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        CFSG.Open.pCoreOf 2 L ≠ ⊥)

@[expose] noncomputable def Item1510 (A : Subgroup G) : Prop :=
  ∃ (c' : G) (L' : Subgroup G) (hL' : L' ∈ lA A c'), Subgroup.zpowers c' ∈ omegaA A ∧
    letI := kerAO2_normal hL'.2.1
    IsEmpty (↥(A ⊔ L') ⧸ kerAO2 A L' ≃*
      Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))

@[expose] noncomputable def Item1511 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A LB, MeetsY4 A LB L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y ∧
        ((∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧ Sec14.IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) ∧
        A = omegaOneThree P

@[expose] noncomputable def Item1512 (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    ∀ Y ∈ scriptY0Star A LB, Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      Y = L ⊔ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Item1513 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  (scriptY0 A LB).Nonempty →
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) →
    Nat.card ↥(A ⊓ L) = 9 →
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
          WStarS4 A ∧ Sec21.IsIrreducibleOn (wStar A) ∧ TransOmegaThree A c) ∨
        omegaA A = {Subgroup.zpowers c}

@[expose] noncomputable def Item1514 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, MeetsY4 A LB L Y →
    (Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L ∧
        omegaA A = {Subgroup.zpowers c} ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) ∨
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
        WStarS4 A ∧ TransOmegaThree A c ∧
        (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)))) ∨
      ((∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
          CFSG.Assembly.RankThreeEven.projSU 3 5 1)) ∧
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∧
        Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ omegaA A = {Subgroup.zpowers c} ∧
        (∀ Y₀ ∈ scriptY0Star A LB, ¬ L ≤ Y₀) ∧ IsSimpleGroup ↥L ∧
        Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
          Subgroup.centralizer (L : Set G))))

@[expose] noncomputable def Item1523 (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A LB,
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L

end CFSG.RankThree.PartTwo.Sec15
