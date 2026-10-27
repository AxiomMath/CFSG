module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCode

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup
open FiveTransitive.Degree24
open scoped Pointwise

private theorem fourFiveBase_support_card_eq_five_mul_weight_twenty
    (a : Degree20.FourFiveBase) :
    ((MulAction.toPermHom
      Degree20.FourFiveBase Degree20.TwentyFivePoints)
        a).support.card =
      5 * fiveWeight a := by
  classical
  let F : Finset (Fin 4) := Finset.univ.filter (fun i => a i ≠ 1)
  have hs : ((MulAction.toPermHom
      Degree20.FourFiveBase Degree20.TwentyFivePoints) a).support =
      F ×ˢ Finset.univ := by
    ext x
    rcases x with ⟨i, z⟩
    simp only [Equiv.Perm.mem_support]
    change (i, a i * z) ≠ (i, z) ↔ _
    simp [F, mul_eq_right]
  rw [hs, Finset.card_product, Finset.card_univ]
  change fiveWeight a * Fintype.card Degree20.FiveCycle = 5 * fiveWeight a
  have hc : Fintype.card Degree20.FiveCycle = 5 := by
    simpa only [Nat.card_eq_fintype_card] using Degree20.card_fiveCycle
  rw [hc, Nat.mul_comm]

theorem exists_fourFive_model_of_subgroup_card_one_hundred_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 20)
    (R : Subgroup (Equiv.Perm X))
    (hRcard : Nat.card R = 125) :
    ∃ A : Subgroup Degree20.FourFiveBase,
      ∃ eAR : A ≃* R,
        ∃ d : X ≃ Degree20.TwentyFivePoints,
          Nat.card A = 125 ∧
          (∀ a : A,
            ((eAR a : R) : Equiv.Perm X).support.card =
              5 * fiveWeight
                ((a : A) : Degree20.FourFiveBase)) ∧
          ∀ (a : A) (x : X),
            d (((eAR a : R) : Equiv.Perm X) x) =
              (MulAction.toPermHom
                Degree20.FourFiveBase
                Degree20.TwentyFivePoints)
                  ((a : A) :
                    Degree20.FourFiveBase) (d x) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hRpGroup : IsPGroup 5 R :=
    IsPGroup.of_card (n := 3)
      (hRcard.trans (by norm_num))
  obtain ⟨Q, hRQ⟩ := hRpGroup.exists_le_sylow
  let e : X ≃ Degree20.TwentyFivePoints :=
    Fintype.equivOfCardEq
      (hcard.trans Degree20.card_twentyFivePoints.symm)
  let standardMap :
      Degree20.FourFiveBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom
        Degree20.FourFiveBase Degree20.TwentyFivePoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let R₀ : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hR₀card : Nat.card R₀ = 625 := by
    calc
      Nat.card R₀ = Nat.card Degree20.FourFiveBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 625 := Degree20.card_fourFiveBase
  have hR₀cardSylow :
      Nat.card R₀ =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hR₀card, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 20 < 3 by norm_num)]
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
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hRQ
  let A : Subgroup Degree20.FourFiveBase :=
    R'.comap standardMap
  have hAmap : A.map standardMap = R' :=
    Subgroup.map_comap_eq_self hR'le
  let eAR' : A ≃* R' :=
    (A.equivMapOfInjective standardMap hstandardMap).trans
      (MulEquiv.subgroupCongr hAmap)
  let eRR' : R ≃* R' :=
    conjugation.subgroupMap R
  let eAR : A ≃* R :=
    eAR'.trans eRR'.symm
  have hAcard : Nat.card A = 125 := by
    calc
      Nat.card A = Nat.card R :=
        Nat.card_congr eAR.toEquiv
      _ = 125 := hRcard
  have hstandardSupport (a : Degree20.FourFiveBase) :
      (standardMap a).support.card =
        ((MulAction.toPermHom
          Degree20.FourFiveBase Degree20.TwentyFivePoints)
            a).support.card := by
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          Degree20.FourFiveBase Degree20.TwentyFivePoints)
            a)).support.card =
        ((MulAction.toPermHom
          Degree20.FourFiveBase Degree20.TwentyFivePoints)
            a).support.card
    exact Degree20.card_support_permCongr _ _
  have hconj (a : A) :
      conjugation ((eAR a : R) : Equiv.Perm X) =
        standardMap
          ((a : A) : Degree20.FourFiveBase) := by
    change
      ((eRR' (eRR'.symm (eAR' a)) : R') :
        Equiv.Perm X) =
        standardMap
          ((a : A) : Degree20.FourFiveBase)
    rw [eRR'.apply_symm_apply]
    rfl
  have hsupport (a : A) :
      ((eAR a : R) : Equiv.Perm X).support.card =
        5 * fiveWeight
          ((a : A) : Degree20.FourFiveBase) := by
    calc
      ((eAR a : R) : Equiv.Perm X).support.card =
          (conjugation
            ((eAR a : R) : Equiv.Perm X)).support.card := by
        exact Equiv.Perm.card_support_conj.symm
      _ = (standardMap
          ((a : A) : Degree20.FourFiveBase)).support.card := by
        rw [hconj a]
      _ = ((MulAction.toPermHom
          Degree20.FourFiveBase Degree20.TwentyFivePoints)
            ((a : A) :
              Degree20.FourFiveBase)).support.card :=
        hstandardSupport _
      _ = 5 * fiveWeight
          ((a : A) : Degree20.FourFiveBase) :=
        fourFiveBase_support_card_eq_five_mul_weight_twenty _
  let d : X ≃ Degree20.TwentyFivePoints :=
    q.trans e
  have hequivariant (a : A) (x : X) :
      d (((eAR a : R) : Equiv.Perm X) x) =
        (MulAction.toPermHom
          Degree20.FourFiveBase
          Degree20.TwentyFivePoints)
            ((a : A) :
              Degree20.FourFiveBase) (d x) := by
    have happ :=
      congrFun
        (congrArg DFunLike.coe (hconj a))
        (q x)
    have happ' := congrArg e happ
    have hqcancel : q⁻¹ (q x) = x :=
      q.symm_apply_apply x
    rw [show
      (conjugation
        ((eAR a : R) : Equiv.Perm X)) (q x) =
          q (((eAR a : R) : Equiv.Perm X)
            (q⁻¹ (q x))) by
        simp only [conjugation, MulAut.conj_apply,
          Equiv.Perm.mul_apply],
      hqcancel] at happ'
    change
      e (q (((eAR a : R) : Equiv.Perm X) x)) =
        e (e.symm
          ((MulAction.toPermHom
            Degree20.FourFiveBase
            Degree20.TwentyFivePoints)
              ((a : A) : Degree20.FourFiveBase)
                (e (q x)))) at happ'
    simpa only [d, Equiv.trans_apply,
      Equiv.apply_symm_apply] using happ'
  exact ⟨A, eAR, d, hAcard, hsupport, hequivariant⟩

end FiveTransitive.Degree25

end CFSG
