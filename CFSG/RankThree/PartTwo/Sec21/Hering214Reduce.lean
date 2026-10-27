module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Lift
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RCase
import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projImage)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open Matrix (ProjGenLinGroup)

namespace Hering214

@[expose] def EInvFour (X : Type) [Group X] (Ē : Subgroup (MulAut X)) : Prop :=
  ∃ W : Subgroup X, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ σ ∈ Ē, ∀ w ∈ W, σ w ∈ W) ∧
    ∃ σ ∈ Ē, ∃ w ∈ W, σ w ≠ w

@[expose] def IsBarSporadic (X : Type) [Group X] : Prop :=
  Sec4.IsTripleCover X NativeSporadic.M22 ∨ Nonempty (X ≃* NativeSporadic.M22) ∨
    Nonempty (X ≃* NativeSporadic.M23) ∨ Nonempty (X ≃* NativeSporadic.HS) ∨
    Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He) ∨
    Nonempty (X ≃* NativeSporadic.J2) ∨ Nonempty (X ≃* NativeSporadic.Ru) ∨
    Nonempty (X ≃* NativeSporadic.J4) ∨ Nonempty (X ≃* NativeSporadic.J3) ∨
    Sec4.IsTripleCover X NativeSporadic.J3

@[expose] def IsBarLieNo3D4 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 0 < n ∧ Even n ∧
      (ChevalleyExceptionalModel X .G2 2 n ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSU 4 2 n))) ∨
    Nonempty (X ≃* projSU 5 2 2) ∨ StatedClassicalModel X .PSp 3 2 1

structure BarData (X : Type) [Group X] (Ē Ū : Subgroup (MulAut X)) : Prop where
  elem3 : IsElemAbelian 3 Ē
  card9 : Nat.card Ē = 9
  elem2 : IsElemAbelian 2 Ū
  ne_bot : Ū ≠ ⊥
  card_le : Nat.card Ū ≤ 4
  norm : Ē ≤ Subgroup.normalizer (Ū : Set (MulAut X))

@[expose] def IsTypeCSub (X : Type) [Group X] (Ā : Subgroup (MulAut X)) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : Sec4.PiField π p f K)
    (_ : Sec4.ModThree π (p ^ f))
    (e : X ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (D : Subgroup (GL (Fin 3) K)), Sec4.IsTypeC π (p ^ f) K D ∧
      (∀ τ ∈ Ā, ∃ y ∈ D, ∀ z : X,
        ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) ∧
      ∀ y ∈ D, ∃ τ ∈ Ā, ∀ z : X,
        ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹

@[expose] def IsTypeCSubSL (X : Type) [Group X] (Ā : Subgroup (MulAut X)) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : Sec4.PiField π p f K)
    (_ : Sec4.ModThree π (p ^ f))
    (e : X ≃* Sec4.slPi π 3 (p ^ f) K)
    (D : Subgroup (GL (Fin 3) K)), Sec4.IsTypeC π (p ^ f) K D ∧
      (∀ τ ∈ Ā, ∃ y ∈ D, ∀ z : X,
        ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹) ∧
      ∀ y ∈ D, ∃ τ ∈ Ā, ∀ z : X,
        ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹

@[expose] def Item214BarSporadic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → IsBarSporadic X →
    ∀ Ē Ū : Subgroup (MulAut X), BarData X Ē Ū → EInvFour X Ē

@[expose] def Item214BarLieNo3D4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsBarLieNo3D4 X → ∀ Ē Ū : Subgroup (MulAut X),
    BarData X Ē Ū → EInvFour X Ē

@[expose] def Item214BarLie3D4' : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ n : ℕ, 0 < n ∧ Even n ∧ ChevalleyExceptionalModel X .trialityD4 2 n) →
      ∀ Ē : Subgroup (MulAut X), IsElemAbelian 3 Ē → Nat.card Ē = 9 → ReflectsE X Ē →
        EInvFour X Ē

@[expose] def Item214BarLie : Prop := Item214BarLieNo3D4 ∧ Item214BarLie3D4'

@[expose] def Item214BarL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Ē : Subgroup (MulAut X)), IsElemAbelian 3 Ē →
    Nat.card Ē = 9 →
    ((∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∧
        IsTypeCSub X Ē) ∨
      (∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (X ≃* SL3 n) ∧ IsTypeCSubSL X Ē)) →
    EInvFour X Ē

@[expose] def Item214BarL45 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (StatedClassicalModel X .PSL 4 2 1 ∨
      StatedClassicalModel X .PSL 5 2 1) →
    ∀ Ē Ū : Subgroup (MulAut X), BarData X Ē Ū → EInvFour X Ē

variable {G : Type} [Group G] [Finite G]

open Item211Res2Proof in
theorem barImage_eq_autThetaQuot {X L : Subgroup G} :
    barImage L X = Sec4.autThetaQuot X L := by
  ext τ
  rw [mem_barImage_iff, Sec4.mem_autThetaQuot_iff]
  rfl

theorem isTypeCSub_of_isTypeCOn {E L : Subgroup G} (h : Sec4.IsTypeCOn E L) :
    IsTypeCSub (lBar L) (Sec4.autThetaQuot E L) := h

theorem isTypeCSubSL_of_isTypeCOnBarSL {E L : Subgroup G} (h : IsTypeCOnBarSL E L) :
    IsTypeCSubSL (lBar L) (Sec4.autThetaQuot E L) := h

end Hering214

open Hering214 Item211Res2Proof

theorem exists_fourGroupsMinus_of_pair (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h211 : Item211) (h213 : Item213) (hSpor : Item214BarSporadic) (hLie : Item214BarLie)
    (hL3 : Item214BarL3) (hL45 : Item214BarL45) {G : Type} [Group G] [Finite G]
    {A E U : Subgroup G} {c : G} {L : Subgroup G} (hpair : Sec21Pair G A E U c L)
    (hnotU4 : ¬ ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n))
    (hEvenP : Nat.card A ≠ 3 ^ 4 → Even (Nat.card (aschbacherSolvableCore 3 L)) →
      ∃ U' ∈ fourGroupsMinus E, U' ≤ L) :
    ∃ U' ∈ fourGroupsMinus E, U' ≤ L := by
  have hPF := Item211LieProof.pairFacts h45 h66 hpair
  have hq := h213 G A E U c L hpair
  have hθ81 : Nat.card A = 3 ^ 4 → Odd (Nat.card (aschbacherSolvableCore 3 L)) := by
    intro h81
    obtain ⟨-, hTch, hT3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have hX3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
      rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
      exact hT3
    have hAN : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) :
        Set G) :=
      hPF.AL.trans (SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L
        (aschbacherSolvableCore 3 ↥L))
    have hodd := Sec8.odd_card_of_le_normalizer hpair.standing.toTheoremFourHyp.localRank_three.le
      hpair.mem_S.1.1 h81 hX3 hAN
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective] at hodd
    exact hodd
  by_cases hθ : Odd (Nat.card (aschbacherSolvableCore 3 L))
  swap
  · exact hEvenP (fun h => hθ (hθ81 h)) (Nat.not_odd_iff_even.mp hθ)
  have hθc : aschbacherSolvableCore 3 ↥L ≤ Subgroup.center ↥L := by
    obtain ⟨hTs, hTch, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    haveI : Group.IsPerfect ↥L := hq.1
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
    exact Sec4.Census.le_of_isSolvable_of_normal inferInstance hTs
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := hpair.mem_E.1.1.2
  have hdata : BarData (lBar L) (barImage L E) (barImage L U) := by
    refine ⟨Item211LieProof.isElemAbelian_barImage_E hPF, Item211LieProof.card_barImage_E hPF,
      Item211LieProof.isElemAbelian_barImage_U hPF, Item211LieProof.barImage_U_ne_bot hPF, ?_,
      Item211LieProof.barImage_E_le_normalizer_U hPF⟩
    have h4 := Item211LieProof.card_barImage_U_mul hPF
    exact Nat.le_of_dvd (by norm_num) (Dvd.intro _ h4)
  have hperfBar : Group.IsPerfect (lBar L) := by
    obtain ⟨-, hTch, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    haveI : Group.IsPerfect ↥L := hq.1
    haveI : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    infer_instance
  have hfour : EInvFour (lBar L) (barImage L E) := by
    rcases h211 G A E U c L hpair with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ | ⟨h, -⟩ |
        ⟨h | h, -⟩ | ⟨⟨n, hn, he, ⟨h, hC⟩ | ⟨h, hC⟩⟩, hA, -⟩ | ⟨⟨n, hn, he, h | h⟩, hA8, hD8⟩ |
        ⟨⟨n, hn, he, h | h⟩ | h, -⟩ | ⟨⟨n, hn, hno, h⟩, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ | ⟨h, -⟩
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    ·
      have hEA : E = A := Subgroup.eq_of_le_of_card_ge hpair.mem_E.2
        (by rw [hA, hpair.mem_E.1.2.1]; norm_num)
      refine hL3 _ _ hdata.elem3 hdata.card9 (Or.inl ⟨n, hn, he, h, ?_⟩)
      rw [barImage_eq_autThetaQuot, hEA]
      exact isTypeCSub_of_isTypeCOn hC
    ·
      have hEA : E = A := Subgroup.eq_of_le_of_card_ge hpair.mem_E.2
        (by rw [hA, hpair.mem_E.1.2.1]; norm_num)
      refine hL3 _ _ hdata.elem3 hdata.card9 (Or.inr ⟨n, hn, he, h, ?_⟩)
      rw [barImage_eq_autThetaQuot, hEA]
      exact isTypeCSubSL_of_isTypeCOnBarSL hC
    · exact hLie.1 _ (Or.inl ⟨n, hn, he, Or.inl h⟩) _ _ hdata
    ·
      exact hLie.2 _ ⟨n, hn, he, h⟩ _ hdata.elem3 hdata.card9
        (reflectsE_of_case211_eight hPF hA8 hD8)
    · exact hLie.1 _ (Or.inl ⟨n, hn, he, Or.inr (Or.inl h)⟩) _ _ hdata
    · exact hLie.1 _ (Or.inl ⟨n, hn, he, Or.inr (Or.inr h)⟩) _ _ hdata
    · exact hLie.1 _ (Or.inr (Or.inl h)) _ _ hdata
    · exact absurd ⟨n, hn, hno, h⟩ hnotU4
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hSpor _ hperfBar (by unfold IsBarSporadic; tauto) _ _ hdata
    · exact hL45 _ (Or.inl h) _ _ hdata
    · exact hL45 _ (Or.inr h) _ _ hdata
    · exact hLie.1 _ (Or.inr (Or.inr h)) _ _ hdata
  obtain ⟨W, hW, hW4, hinv, hnt⟩ := hfour
  exact Hering214.exists_fourGroupsMinus_of_bar hPF.EL hE3 hθc hθ hW hW4 hinv hnt

end CFSG.RankThree.PartTwo.Sec21
