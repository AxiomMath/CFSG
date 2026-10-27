module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KN6
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesBase

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] def fixE {X : Type} [Group X] (E : Subgroup (MulAut X)) : Subgroup X where
  carrier := {x | ∀ ε ∈ E, ε x = x}
  mul_mem' := fun {x y} hx hy ε hε => by rw [map_mul, hx ε hε, hy ε hε]
  one_mem' := fun ε _ => map_one ε
  inv_mem' := fun {x} hx ε hε => by rw [map_inv, hx ε hε]

theorem mem_fixE {X : Type} [Group X] {E : Subgroup (MulAut X)} {x : X} :
    x ∈ fixE E ↔ ∀ ε ∈ E, ε x = x :=
  Iff.rfl

@[expose] def LocE (X : Type) [Group X] (E : Subgroup (MulAut X)) : Prop :=
  ∀ Y : Subgroup X, ¬ 3 ∣ Nat.card Y → (∀ ε ∈ E, ∀ y ∈ Y, ε y ∈ Y) →
    ∃ ε ∈ E, ε ≠ 1 ∧ Y ≤ inSubgroup (aschbacherSolvableCore 3) (Sec4.autFix ε)

@[expose] def InspectSig148L3Loc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec13.IsLThreePi X → Sec4.IsList46 X →
    (∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e → Sec4.IsoLThreePi X p e → p = 2 ∨ e ≤ 2) →
    ∀ E : Subgroup (MulAut X), Nat.card E = 9 → (∀ ε ∈ E, ε ^ 3 = 1) → LocE X E →
      IsPGroup 3 (fixE E) →
      ∀ K : Subgroup X, (∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) → Group.IsPerfect K → K ≠ ⊥ →
        IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
        Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) →
        K ≤ (⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1),
          pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) →
        Ronan148K.L3SigType X K

@[expose] def LocA {Γ : Type} [Group Γ] [Finite Γ] (A L : Subgroup Γ) : Prop :=
  ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
    (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
    ∃ (a : Γ) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set Γ)),
      L3PGL.sigmaOf L haN ≠ 1 ∧
        Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (L3PGL.sigmaOf L haN))

@[expose] def KF148SigL3Loc : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    (∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p = 2 ∨ e ≤ 2) →
    LocA A L → IsPGroup 3 (L3PGL.fixA A L) →
    Sec4.IsList46 (↥K ⧸ aschbacherSolvableCore 3 ↥K) →
    KThetaC148 K L

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
