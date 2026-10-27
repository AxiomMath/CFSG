module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14.Native

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Sporadic (rank3II_4_15)

variable {X : Type} [Group X] [Finite X]

theorem center_eq_bot_of_j2 (hX : Nonempty (X ≃* NativeSporadic.J2)) : Subgroup.center X = ⊥ :=
  KS14.center_eq_bot_of_j2 rank3II_4_15 hX

theorem center_nativeJ2_eq_bot : Subgroup.center NativeSporadic.J2 = ⊥ :=
  KS14.center_nativeJ2_eq_bot rank3II_4_15

theorem j2_exists_sylow_of_card_nine (hX : Nonempty (X ≃* NativeSporadic.J2)) {E : Subgroup X}
    (hE9 : Nat.card E = 9) :
    ∃ P : Sylow 3 X, E ≤ P ∧
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) ≤ E ∧
      E ≤ Subgroup.centralizer
        (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
          Set X) :=
  KS14.j2_exists_sylow_of_card_nine rank3II_4_15 hX hE9

theorem j2_exists_conjugate_of_card_nine (hX : Nonempty (X ≃* NativeSporadic.J2))
    {E E' : Subgroup X} (hE : Nat.card E = 9) (hE' : Nat.card E' = 9) :
    ∃ g : X, E' = conjugate E g :=
  KS14.j2_exists_conjugate_of_card_nine rank3II_4_15 hX hE hE'

theorem j2_centralizer_quotient (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) ≤
        Subgroup.center ↥(Subgroup.centralizer ({z} : Set X)) ∧
      Nat.card ↥((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X))) = 3 ∧
      ∃ _ : ((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X))).Normal,
        Nonempty (↥(Subgroup.centralizer ({z} : Set X)) ⧸
          (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) ≃*
            alternatingGroup (Fin 6)) :=
  KS14.j2_centralizer_quotient rank3II_4_15 hX hz1 hz

theorem j2_centralizer_isPerfect (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set X)) :=
  KS14.j2_centralizer_isPerfect rank3II_4_15 hX hz1 hz

theorem j2_center_centralizer (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Subgroup.center ↥(Subgroup.centralizer ({z} : Set X)) =
      (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) :=
  KS14.j2_center_centralizer rank3II_4_15 hX hz1 hz

theorem j2_centralizer_isTripleCover (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X}
    (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Sec4.IsTripleCover ↥(Subgroup.centralizer ({z} : Set X)) (alternatingGroup (Fin 6)) :=
  KS14.j2_centralizer_isTripleCover rank3II_4_15 hX hz1 hz

theorem j2_perfectResidual_centralizer_eq_top (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X}
    (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    perfectResidual ↥(Subgroup.centralizer ({z} : Set X)) = ⊤ :=
  KS14.j2_perfectResidual_centralizer_eq_top rank3II_4_15 hX hz1 hz

theorem j2_pCore_two_centralizer_eq_bot (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X}
    (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ :=
  KS14.j2_pCore_two_centralizer_eq_bot rank3II_4_15 hX hz1 hz

variable {Y : Type} [Group Y] [Finite Y]

theorem j2_exists_conjugate_of_card_twentySeven_of_quot {L : Subgroup Y} {N : Subgroup L}
    [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) (hL : Nonempty (↥L ⧸ N ≃* NativeSporadic.J2)) {z : Y}
    (hzC : z ∈ Subgroup.centralizer (L : Set Y)) (hzL : z ∉ L) (hz3 : z ^ 3 = 1)
    {E E' : Subgroup Y} (hE : E ≤ Subgroup.zpowers z ⊔ L) (hE' : E' ≤ Subgroup.zpowers z ⊔ L)
    (hzE : z ∈ E) (hzE' : z ∈ E') (h27 : Nat.card E = 27) (h27' : Nat.card E' = 27) :
    ∃ g ∈ L, E' = conjugate E g :=
  KS14.j2_exists_conjugate_of_card_twentySeven_of_quot rank3II_4_15 hN3 hL hzC hzL hz3 hE hE'
    hzE hzE' h27 h27'

end CFSG.RankThree.PartTwo.KFacts.KS14.Native
