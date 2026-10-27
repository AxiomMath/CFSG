module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoLift

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction Subgroup
open scoped Pointwise

local instance fivePrimeTwoPermutation :
    Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

@[expose] noncomputable def permutationSubgroupSupportCount
    {X : Type} [Fintype X] [DecidableEq X]
    (R : Subgroup (Equiv.Perm X))
    (m : ℕ) : ℕ :=
  Nat.card {r : R // r.1.support.card = m}

theorem subgroup_card_twenty_five_support_distribution
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 24)
    (R : Subgroup (Equiv.Perm X))
    (hRcard : Nat.card R = 25) :
    0 < permutationSubgroupSupportCount R 5 ∨
      (Nat.card (MulAction.fixedPoints R X) = 9 ∧
        permutationSubgroupSupportCount R 10 = 12 ∧
        permutationSubgroupSupportCount R 15 = 12) ∨
      (Nat.card (MulAction.fixedPoints R X) = 4 ∧
        ((permutationSubgroupSupportCount R 10 = 8 ∧
            permutationSubgroupSupportCount R 15 = 0) ∨
          (permutationSubgroupSupportCount R 10 = 4 ∧
            permutationSubgroupSupportCount R 15 = 8) ∨
          (permutationSubgroupSupportCount R 10 = 0 ∧
            permutationSubgroupSupportCount R 15 = 16))) := by
  classical
  have hRpGroup : IsPGroup 5 R :=
    IsPGroup.of_card (n := 2)
      (hRcard.trans (by norm_num))
  obtain ⟨Q, hRQ⟩ := hRpGroup.exists_le_sylow
  let e : X ≃ TwentyFourFivePoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_twentyFourFivePoints.symm)
  let standardMap :
      FourFiveBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom
        FourFiveBase TwentyFourFivePoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let R₀ : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hR₀card : Nat.card R₀ = 625 := by
    calc
      Nat.card R₀ = Nat.card FourFiveBase :=
        Nat.card_congr
          (MonoidHom.ofInjective
            hstandardMap).toEquiv.symm
      _ = 625 := Degree20.card_fourFiveBase
  have hR₀cardSylow :
      Nat.card R₀ =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hR₀card, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 24 < 3 by norm_num)]
    rw [Finset.sum_Ico_succ_top
      (by norm_num : 1 ≤ 2)]
    norm_num
  let Q₀ : Sylow 5 (Equiv.Perm X) :=
    Sylow.ofCard R₀ hR₀cardSylow
  obtain ⟨q, hq⟩ :=
    exists_smul_eq (Equiv.Perm X) Q Q₀
  have hqSub :
      MulAut.conj q •
          (Q : Subgroup (Equiv.Perm X)) =
        (Q₀ : Subgroup (Equiv.Perm X)) := by
    exact congrArg
      (fun T : Sylow 5 (Equiv.Perm X) =>
        (T : Subgroup (Equiv.Perm X))) hq
  let conjugation : Equiv.Perm X ≃* Equiv.Perm X :=
    MulAut.conj q
  let R' : Subgroup (Equiv.Perm X) :=
    MulAut.conj q • R
  have hR'le : R' ≤ R₀ := by
    change
      MulAut.conj q • R ≤
        (Q₀ : Subgroup (Equiv.Perm X))
    rw [← hqSub]
    exact
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr
        hRQ
  let A : Subgroup FourFiveBase :=
    R'.comap standardMap
  have hAmap : A.map standardMap = R' :=
    Subgroup.map_comap_eq_self hR'le
  let eAR' : A ≃* R' :=
    (A.equivMapOfInjective standardMap
      hstandardMap).trans
        (MulEquiv.subgroupCongr hAmap)
  let eRR' : R ≃* R' :=
    conjugation.subgroupMap R
  let eAR : A ≃ R :=
    eAR'.toEquiv.trans eRR'.symm.toEquiv
  have hAcard : Nat.card A = 25 := by
    calc
      Nat.card A = Nat.card R :=
        Nat.card_congr eAR
      _ = 25 := hRcard
  have hstandardSupport (a : FourFiveBase) :
      (standardMap a).support.card =
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card := by
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a)).support.card =
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card
    exact Degree20.card_support_permCongr _ _
  have hsupport (a : A) :
      ((eAR a : R) : Equiv.Perm X).support.card =
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            (a : FourFiveBase)).support.card := by
    have hconj :
        conjugation ((eAR a : R) : Equiv.Perm X) =
          standardMap (a : FourFiveBase) := by
      change
        ((eRR' (eRR'.symm (eAR' a)) : R') :
          Equiv.Perm X) =
          standardMap (a : FourFiveBase)
      rw [eRR'.apply_symm_apply]
      rfl
    calc
      ((eAR a : R) : Equiv.Perm X).support.card =
          (conjugation
            ((eAR a : R) : Equiv.Perm X)).support.card := by
        exact Equiv.Perm.card_support_conj.symm
      _ = (standardMap
          (a : FourFiveBase)).support.card := by
        rw [hconj]
      _ = ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            (a : FourFiveBase)).support.card :=
        hstandardSupport _
  have hsupportCount (m : ℕ) :
      permutationSubgroupSupportCount R m =
        fourFiveSubgroupSupportCount A m := by
    let C :=
      {a : A //
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card = m}
    let D :=
      {r : R // r.1.support.card = m}
    let E : C ≃ D := {
      toFun := fun a =>
        ⟨eAR a.1, (hsupport a.1).trans a.prop⟩
      invFun := fun r => ⟨eAR.symm r.1, by
        rw [← hsupport (eAR.symm r.1),
          eAR.apply_symm_apply]
        exact r.prop⟩
      left_inv := fun a => by
        apply Subtype.ext
        exact eAR.symm_apply_apply a.1
      right_inv := fun r => by
        apply Subtype.ext
        exact eAR.apply_symm_apply r.1 }
    calc
      permutationSubgroupSupportCount R m =
          Nat.card D := by
        rfl
      _ = Nat.card C :=
        Nat.card_congr E.symm
      _ = fourFiveSubgroupSupportCount A m := by
        rfl
  let d : X ≃ TwentyFourFivePoints :=
    q.trans e
  have hintertwine (a : A) (x : X) :
      d (((eAR a : R) : Equiv.Perm X) x) =
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            (a : FourFiveBase)) (d x) := by
    have hconj :
        conjugation ((eAR a : R) :
          Equiv.Perm X) =
          standardMap (a : FourFiveBase) := by
      change
        ((eRR' (eRR'.symm (eAR' a)) : R') :
          Equiv.Perm X) =
          standardMap (a : FourFiveBase)
      rw [eRR'.apply_symm_apply]
      rfl
    have happ :=
      congrArg
        (fun w : Equiv.Perm X => w (q x)) hconj
    have heapp := congrArg e happ
    simpa [d, conjugation, standardMap] using heapp
  have hfixedIff (x : X) :
      x ∈ MulAction.fixedPoints R X ↔
        d x ∈ MulAction.fixedPoints A
          TwentyFourFivePoints := by
    rw [MulAction.mem_fixedPoints,
      MulAction.mem_fixedPoints]
    constructor
    · intro hx a
      change
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            (a : FourFiveBase)) (d x) = d x
      rw [← hintertwine]
      have hxa := hx (eAR a)
      change
        (((eAR a : R) : Equiv.Perm X) x) = x at hxa
      rw [hxa]
    · intro hx r
      have ha := hx (eAR.symm r)
      change
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            ((eAR.symm r : A) :
              FourFiveBase)) (d x) = d x at ha
      have hi := hintertwine (eAR.symm r) x
      rw [eAR.apply_symm_apply] at hi
      rw [ha] at hi
      change ((r : Equiv.Perm X) x) = x
      exact d.injective hi
  let Efixed :
      MulAction.fixedPoints R X ≃
        MulAction.fixedPoints A
          TwentyFourFivePoints := {
    toFun := fun x =>
      ⟨d x.1, (hfixedIff x.1).mp x.prop⟩
    invFun := fun y =>
      ⟨d.symm y.1,
        (hfixedIff (d.symm y.1)).mpr (by
          rw [d.apply_symm_apply]
          exact y.prop)⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact d.symm_apply_apply x.1
    right_inv := fun y => by
      apply Subtype.ext
      exact d.apply_symm_apply y.1 }
  have hfixed :
      Nat.card (MulAction.fixedPoints R X) =
        Nat.card
          (MulAction.fixedPoints A
            TwentyFourFivePoints) :=
    Nat.card_congr Efixed
  rcases
      fourFive_subgroup_card_twenty_five_support_distribution
        A hAcard with
    hfive | ⟨hactive, hten, hfifteen⟩ |
      ⟨hactive, hcases⟩
  · left
    rw [hsupportCount 5]
    exact hfive
  · right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hfixed,
        card_fixedPoints_fourFiveSubgroup,
        hactive]
    · rw [hsupportCount 10]
      exact hten
    · rw [hsupportCount 15]
      exact hfifteen
  · right
    right
    refine ⟨?_, ?_⟩
    · rw [hfixed,
        card_fixedPoints_fourFiveSubgroup,
        hactive]
    · rcases hcases with hcase | hcase | hcase
      · left
        constructor
        · rw [hsupportCount 10]
          exact hcase.1
        · rw [hsupportCount 15]
          exact hcase.2
      · right
        left
        constructor
        · rw [hsupportCount 10]
          exact hcase.1
        · rw [hsupportCount 15]
          exact hcase.2
      · right
        right
        constructor
        · rw [hsupportCount 10]
          exact hcase.1
        · rw [hsupportCount 15]
          exact hcase.2

end FiveTransitive.Degree24

end CFSG
