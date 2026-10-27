module

public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Types

variable {G : Type} [Group G] [Finite G]

@[expose] def IsList122 (L : Subgroup G) : Prop :=
  Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22

@[expose] def HJType129 (L K : Subgroup G) : Prop :=
  Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∧
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def GTwoType129 (L K : Subgroup G) : Prop :=
  ∃ q : TauCeti.PrimePower,
    Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card ∧
      (Sec4.IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
        ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
          Nonempty (K ⧸ CFSG.pCore 2 K ≃*
            (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))

@[expose] def PiModNine (q : ℕ) : Prop := q % 9 = 1 ∨ q % 9 = 8

@[expose] def Typ129I (K Y : Subgroup G) : Prop :=
  Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* K ⧸ CFSG.pCore 2 K)

@[expose] def Typ129II (K Y : Subgroup G) : Prop :=
  ∃ q : TauCeti.PrimePower,
    (∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
      Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
    Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y)
      ⟨q.p, 3 * q.exponent, q.prime_p, Nat.mul_pos (by norm_num) q.exponent_pos⟩

@[expose] def Core129 (A : Subgroup G) (c : G) (x : G) (Y : Subgroup G) : Prop :=
  Y ∈ thetaComponentsAt 3 x ∧ A ≤ Subgroup.normalizer (Y : Set G) ∧
    A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x ∧
    ⁅Y, Subgroup.zpowers c⁆ = Y

@[expose] def JData129 (A : Subgroup G) (c : G) (L Y J : Subgroup G) : Prop :=
  J ∈ thetaComponentsAt 3 c ∧ J ≠ L ∧ c ∈ J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
    A ⊓ Sec4.thetaQuotCentralizer J = A ⊓ L ∧
    J = inSubgroup perfectResidual (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) J

@[expose] def D129 (a b : G) : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b

structure Cfg129 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (b a : G) (K S : Subgroup G) : Prop where
  std : Sec12StdBar G A c L
  mem_E : A ∈ partTwoE G
  mem_S : A ∈ partTwoS G
  list : IsList122 L
  hb : b ∈ A ⊓ Sec4.thetaQuotCentralizer L
  hb_not : b ∉ Subgroup.zpowers c
  hK : K ∈ thetaComponentsAt 3 b
  hIK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K
  hlt : ¬ (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
    inSubgroup (aschbacherSolvableCore 3) K = K)
  ha : a ∈ A ⊓ L
  ha_not : a ∉ Subgroup.zpowers c
  hS_le : S ≤ K
  hS2 : IsPGroup 2 S
  hS_ne : S ≠ ⊥
  hS_norm : A ≤ Subgroup.normalizer (S : Set G)
  hS_cent : S ≤ Subgroup.centralizer ((D129 a b : Subgroup G) : Set G)
  hS_comm : ⁅S, Subgroup.zpowers c⁆ = S

@[expose] def Item129BarList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G → IsList122 L → A ∉ partTwoS G

@[expose] def Item122Bar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G → IsList122 L

@[expose] def Gap129SymII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b → x ∈ L →
      ∀ Y : Subgroup G, Core129 A c x Y → ¬ Typ129II K Y

end Types

end CFSG.RankThree.PartTwo.Sec12
