module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn
public import CFSG.RankThree.PartTwo.Sec8.Groups

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] noncomputable def thetaImage {G : Type*} [Group G] (X : Subgroup G) :
    Subgroup (G ⧸ aschbacherSolvableCore 3 G) :=
  X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))

@[expose] def Item4_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ c ∈ A, c ∈ Subgroup.center G → c ≠ 1 →
    ∀ L ∈ thetaComponents 3 G, Nat.card (autThetaQuot A L) = 9 →
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ →
        (Sec8.IsZ3LThreePi (thetaImage (L ⊔ A)) ∧
            (Nonempty (autIn L A ≃* QuaternionGroup 2) ∨
              Nonempty (autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
        (Sec8.IsZ3PGLThreePi (thetaImage (L ⊔ A)) ∧
            Nonempty (autIn L A ≃* Multiplicative (ZMod 3)) ∧
            ∃ a ∈ A, a ≠ 1 ∧ InducesTypeOn L a 3) ∨
        (IsHeisCentral (thetaImage (L ⊔ A)) (L ⧸ aschbacherSolvableCore 3 L) ∧
            (IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
              IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 ∨
              IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L)) ∧
            CFSG.Assembly.IsElemAbelian 3 (autIn L A) ∧ Nat.card (autIn L A) = 9) ∨
        (IsSLThreePiTwo (thetaImage (L ⊔ A)) ∧
            Nonempty (autIn L A ≃* Multiplicative (ZMod 3))) ∨
        (Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
            Nonempty (autIn L A ≃* Multiplicative (ZMod 4))) ∨
        (Nonempty (thetaImage (L ⊔ A) ≃*
              Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (autIn L A ≃* QuaternionGroup 2)) ∨
        ((Nonempty (thetaImage (L ⊔ A) ≃*
                Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
              Nonempty (thetaImage (L ⊔ A) ≃*
                Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
            Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
        ∃ a ∈ A, a ≠ 1 ∧
          (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField)

end CFSG.RankThree.PartTwo.Sec4
