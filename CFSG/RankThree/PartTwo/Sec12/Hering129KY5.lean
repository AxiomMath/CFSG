module

import CFSG.Models.PGLSimple
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
public import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

@[expose] def Gap129YSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y →
        ∀ (X' : Type) [Group X'],
          (Nonempty (X' ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
            Nonempty (X' ≃* CFSG.Blueprint.NativeSporadic.He)) →
          ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X')

@[expose] def Gap129YG2Range : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y →
        ∀ r : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) r →
          4 ≤ r.card ∧ r.p ≠ 3

section L3

theorem commutator_eq_top_of_simple {X : Type} [Group X] (hS : IsSimpleGroup X)
    (hn : ∃ a b : X, a * b ≠ b * a) : _root_.commutator X = ⊤ := by
  rcases hS.eq_bot_or_eq_top_of_normal (_root_.commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ _root_.commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact hab (by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
        _ = b * a := by rw [hmem, one_mul])
  · exact h

noncomputable def equivOfCommutatorTop {Y' X' : Type} [Group Y'] [Group X']
    (hS : IsSimpleGroup X') (hn : ∃ a b : X', a * b ≠ b * a)
    (e : Y' ≃* _root_.commutator X') : Y' ≃* X' :=
  e.trans ((MulEquiv.subgroupCongr (commutator_eq_top_of_simple hS hn)).trans Subgroup.topEquiv)

theorem l3_shape_of_commutator {Y' X' : Type} [Group Y'] [Finite Y'] [Group X']
    (hns : ¬ Group.IsSolvable Y') {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hX : (p ^ e % 3 = 1 ∧ Nonempty (X' ≃* projSL 3 (GaloisField p e))) ∨
      (p ^ e % 3 = 2 ∧ Nonempty (X' ≃* projSU 3 p e)))
    (h : Nonempty (Y' ≃* _root_.commutator X')) :
    Sec4.IsoLThreePi Y' p e ∧ Subgroup.center Y' = ⊥ := by
  obtain ⟨eY⟩ := h
  have hnc : ∃ a b : X', a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hbot : _root_.commutator X' = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [Subgroup.mem_bot]
      calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [hcon a b]
        _ = 1 := by group
    exact hns (by
      haveI : Subsingleton ↥(_root_.commutator X') := by
        rw [hbot]; infer_instance
      haveI : Subsingleton Y' := eY.toEquiv.subsingleton
      infer_instance)
  rcases hX with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · have hS : IsSimpleGroup X' := by
      haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
      exact f.isSimpleGroup
    have e' := equivOfCommutatorTop hS hnc eY
    refine ⟨Or.inl ⟨h1, ⟨e'.trans f⟩⟩, ?_⟩
    haveI : IsSimpleGroup Y' := e'.isSimpleGroup
    exact Hering129HLift.center_eq_bot_of_simple this (by
      obtain ⟨a, b, hab⟩ := hnc
      exact ⟨e'.symm a, e'.symm b, fun hc => hab (e'.symm.injective (by simpa using hc))⟩)
  · by_cases hpe : p ^ e = 2
    · exfalso
      obtain ⟨hp2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpe
      subst hp2 he1
      haveI : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
      haveI : Group.IsSolvable X' :=
        solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
      exact hns (solvable_of_solvable_injective (f := eY.toMonoidHom) eY.injective)
    · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 p e := by
        refine ⟨Fact.out, he, le_rfl, ?_⟩
        intro hh
        exact hpe (by simpa using congrArg Prod.snd hh)
      have hS : IsSimpleGroup X' := by
        haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
        exact f.isSimpleGroup
      have e' := equivOfCommutatorTop hS hnc eY
      refine ⟨Or.inr ⟨h2, ⟨e'.trans f⟩⟩, ?_⟩
      haveI : IsSimpleGroup Y' := e'.isSimpleGroup
      exact Hering129HLift.center_eq_bot_of_simple this (by
        obtain ⟨a, b, hab⟩ := hnc
        exact ⟨e'.symm a, e'.symm b, fun hc => hab (e'.symm.injective (by simpa using hc))⟩)

end L3

@[expose] def KS129PGL3Shape : Prop :=
  ∀ (Y' X' : Type) [Group Y'] [Finite Y'] [Group X'], ¬ Group.IsSolvable Y' →
    (∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ Nonempty (X' ≃* projImage (Sec4.glPi π 3 (p ^ f) K))) →
    Nonempty (Y' ≃* _root_.commutator X') →
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi Y' p e) ∧
      Subgroup.center Y' = ⊥

section Field


variable {G : Type} [Group G] [Finite G]

theorem not_stdKind_of_notEight (h1134N : Sec11.Item1134E27N) (h1134ST : Sec21.Item1134E27ST)
    (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAS : A ∈ partTwoS G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    (hL8 : ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 2 3)))
    (hS8 : ¬ Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) 8) {e : G} (heA : e ∈ A) :
    ¬ KFacts.InducesStdKind Y e .field ∧ ¬ KFacts.InducesStdKind Y e .graphField := by
  have hle : A ⊓ Sec4.thetaQuotCentralizer Y ≤ Subgroup.zpowers x := hAC.le
  have hstar : Y ∈ lStarAt A x :=
    ⟨Sec6.mem_lStar_of_inf_le_zpowers hAF.1 hxA hx1 hY hAN hle, hY⟩
  have hsc : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers x : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAN, hAC]
  by_cases hT : A ∈ partTwoT G
  · exact h1134ST G A x Y hst hAS hT h27 hxA hx1 hstar hsc
      (Or.inr (Or.inr ⟨hL8, hS8⟩)) hFE.symm e heA
  · exact h1134N G A x Y hst hAF hT h27 hxA hx1 hstar hsc hL8 hS8 (fun _ => hFE.symm) e heA

end Field

end CFSG.RankThree.PartTwo.Sec12
