module

public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def KS127NotIn423 : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (A K : Subgroup C), K ∈ thetaComponents 3 C →
    (∃ q : TauCeti.PrimePower, IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
      ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) →
    ¬ ((Sec8.IsZ3LThreePi (thetaImage (K ⊔ A)) ∧
          (Nonempty (autIn K A ≃* QuaternionGroup 2) ∨
            Nonempty (autIn K A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
        (Sec8.IsZ3PGLThreePi (thetaImage (K ⊔ A)) ∧
          Nonempty (autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ a ∈ A, a ≠ 1 ∧ InducesTypeOn K a 3) ∨
        (IsHeisCentral (thetaImage (K ⊔ A)) (K ⧸ aschbacherSolvableCore 3 K) ∧
          (IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 7)) ∨
            IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.M22 ∨
            IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K)) ∧
          CFSG.Assembly.IsElemAbelian 3 (autIn K A) ∧ Nat.card (autIn K A) = 9) ∨
        (IsSLThreePiTwo (thetaImage (K ⊔ A)) ∧
          Nonempty (autIn K A ≃* Multiplicative (ZMod 3))) ∨
        (Nonempty (thetaImage (K ⊔ A) ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
          Nonempty (autIn K A ≃* Multiplicative (ZMod 4))) ∨
        (Nonempty (thetaImage (K ⊔ A) ≃*
            Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M22) ∧
          Nonempty (autIn K A ≃* QuaternionGroup 2)) ∨
        ((Nonempty (thetaImage (K ⊔ A) ≃*
              Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
            Nonempty (thetaImage (K ⊔ A) ≃*
              Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
          Nonempty (autIn K A ≃* Equiv.Perm (Fin 3))))

end CFSG.RankThree.PartTwo.KFacts
