module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BL3PointFacts

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def SigImg148 (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) : Prop :=
  ∀ W Q D : Subgroup (MulAut X), W ≤ (MulAut.conj : X →* MulAut X).range →
    P ≤ Subgroup.normalizer (W : Set (MulAut X)) → IsHyperplane P D →
    Q ≤ W ⊓ Subgroup.centralizer (D : Set (MulAut X)) →
    Q ∈ invariantPiSubgroups ⊤ P (piCompl 3) → Q = ⁅Q, P⁆ →
    (∀ H : Subgroup (MulAut X), IsHyperplane P H → ∀ V : Subgroup (MulAut X),
      V ≤ W ⊓ Subgroup.centralizer (H : Set (MulAut X)) →
      V ∈ invariantPiSubgroups ⊤ P (piCompl 3) → V = ⁅V, P⁆ →
      V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set (MulAut X)))) →
    ¬ Q ≤ pPrimeCoreOf 3 W →
    ∃ T ∈ thetaComponentsIn W, P ≤ Subgroup.normalizer (T : Set (MulAut X)) ∧
      3 ∣ Nat.card T ∧
      T ≤ sSup {V : Subgroup (MulAut X) | V ≤ T ∧ V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧
        V = ⁅V, P⁆}

@[expose] def KF148PointSigImg : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L : Subgroup Γ) (b : Γ),
    Late.IsE27 A → b ∈ A → b ≠ 1 → L ≤ Subgroup.centralizer ({b} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ) →
    (∀ x ∈ Subgroup.centralizer (A : Set Γ), x ^ 3 = 1 → x ∈ A) →
    ((b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × Sec12.lBar b L) ∧
        ((IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
              Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)))) ∨
      (b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        (Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
        Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (b ∉ L ∧ Sec8.IsZ3PGLThreePi (lBarA b L A) ∧
        Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
        ∃ x ∈ A, Sec4.InducesTypeOn L x 3)) →
    (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    (IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → L3PointFacts A L b) →
    SigImg148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L)

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
