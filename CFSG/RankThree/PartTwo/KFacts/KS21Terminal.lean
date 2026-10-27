module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def IsTerminalGroup (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 5 2 3) ∨ Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨
    Nonempty (X ≃* projSp 3 (GaloisField 2 2))

@[expose] def ElemAbelianFusedIntoJ (X : Type) [Group X] : Prop :=
  ∀ P : Sylow 3 X, ∀ B : Subgroup X, B ≤ P → CFSG.Assembly.IsElemAbelian 3 B →
    ∃ x : X, B.map (MulAut.conj x).toMonoidHom ≤
      (CFSG.elemThompson (P : Subgroup X) 3).map (P : Subgroup X).subtype

@[expose] def TerminalFusion : Prop :=
  ∀ (X : Type) [Group X], IsTerminalGroup X → ElemAbelianFusedIntoJ X

@[expose] def TerminalTwoCentralInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I N : Subgroup G), I ≤ N →
    N ≤ Subgroup.normalizer (I : Set G) → IsTerminalGroup I → ∀ T : Sylow 2 N,
      ∃ z : I, orderOf z = 2 ∧ (z : G) ∈ (T : Subgroup N).map N.subtype ∧
        (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {(z : G)} ∧
        2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set I)) ∧
        ∃ H : Subgroup I, H ≤ Subgroup.centralizer ({z} : Set I) ∧ IsSimpleGroup H ∧
          3 ∣ Nat.card H ∧ Nat.card H ≠ 3

@[expose] def TerminalSylowThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I N A : Subgroup G), I ≤ N →
    N ≤ Subgroup.normalizer (I : Set G) → A ≤ I → CFSG.Assembly.IsElemAbelian 3 A →
    ((Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3)) →
    (∀ x ∈ N, x ∈ Subgroup.centralizer (A : Set G) → orderOf x = 3 → x ∈ A) →
    ∀ P : Sylow 3 I, A ≤ (P : Subgroup I).map I.subtype →
      (Nonempty ((P : Subgroup I) ≃* Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) ∨
        Nonempty ((P : Subgroup I) ≃*
          (Multiplicative (ZMod 9) × Multiplicative (ZMod 9) ≀ᵣ Multiplicative (ZMod 3)))) ∧
      (CFSG.elemThompson ((P : Subgroup I).map I.subtype) 3).map
        ((P : Subgroup I).map I.subtype).subtype = A ∧
      ∃ Q : Sylow 3 N, (Q : Subgroup N).map N.subtype = (P : Subgroup I).map I.subtype

@[expose] def TerminalAutomizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X), CFSG.Assembly.IsElemAbelian 3 A →
    (Nonempty (X ≃* projSU 5 2 3) → Nat.card A = 3 ^ 4 →
      Nat.card (Subgroup.normalizer (A : Set X)) ≤
        120 * Nat.card (Subgroup.centralizer (A : Set X))) ∧
    (Nonempty (X ≃* projSL 4 (GaloisField 2 2)) → Nat.card A = 3 ^ 3 →
      Nat.card (Subgroup.normalizer (A : Set X)) ≤
        24 * Nat.card (Subgroup.centralizer (A : Set X)))

end CFSG.RankThree.PartTwo.KFacts.KS21
