module

public import CFSG.Permutation.FiveTransitive.Degree24SylowFiveMax
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

abbrev FiveVector := Fin 4 → ZMod 5

@[expose] def fiveWeight (v : FiveVector) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

@[expose] def fiveDot (c v : FiveVector) : ZMod 5 :=
  ∑ i, c i * v i

private theorem five_standard_hyperplane_weight_two :
    (Finset.univ.filter fun v : FiveVector =>
      (∑ i, v i) = 0 ∧ fiveWeight v = 2).card = 24 := by
  decide

theorem five_hyperplane_weight_one_or_twenty_four_weight_two
    (c : FiveVector) :
    (∃ v : FiveVector,
      fiveDot c v = 0 ∧ fiveWeight v = 1) ∨
    ((Finset.univ.filter fun v : FiveVector =>
      fiveDot c v = 0 ∧ fiveWeight v = 2).card = 24 ∧
      ∀ i, c i ≠ 0) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hall : ∀ i, c i ≠ 0
  · right
    refine ⟨?_, hall⟩
    let e : FiveVector ≃ FiveVector := {
      toFun := fun v i => c i * v i
      invFun := fun v i => (c i)⁻¹ * v i
      left_inv := fun v => by
        funext i
        change (c i)⁻¹ * (c i * v i) = v i
        simp [hall i]
      right_inv := fun v => by
        funext i
        change c i * ((c i)⁻¹ * v i) = v i
        simp [hall i] }
    have hweight (v : FiveVector) :
        fiveWeight (e v) = fiveWeight v := by
      unfold fiveWeight
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change c i * v i ≠ 0 ↔ v i ≠ 0
      constructor
      · intro h hzero
        rw [hzero, mul_zero] at h
        exact h rfl
      · exact mul_ne_zero (hall i)
    let A :=
      {v : FiveVector //
        fiveDot c v = 0 ∧ fiveWeight v = 2}
    let B :=
      {v : FiveVector //
        (∑ i, v i) = 0 ∧ fiveWeight v = 2}
    let E : A ≃ B := {
      toFun := fun v => ⟨e v, by
        refine ⟨?_, ?_⟩
        · change (∑ i, c i * v.1 i) = 0
          exact v.prop.1
        · rw [hweight]
          exact v.prop.2⟩
      invFun := fun v => ⟨e.symm v, by
        refine ⟨?_, ?_⟩
        · change
            (∑ i, c i * ((c i)⁻¹ * v.1 i)) = 0
          calc
            (∑ i, c i * ((c i)⁻¹ * v.1 i)) =
                ∑ i, v.1 i := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hall i]
            _ = 0 := v.prop.1
        · have hw := hweight (e.symm v)
          rw [e.apply_symm_apply] at hw
          exact hw.symm.trans v.prop.2⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v) }
    rw [← Fintype.card_subtype]
    change Fintype.card A = 24
    rw [Fintype.card_congr E]
    rw [Fintype.card_subtype]
    exact five_standard_hyperplane_weight_two
  · left
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    let v : FiveVector :=
      fun j => if j = i then 1 else 0
    refine ⟨v, ?_, ?_⟩
    · simp [fiveDot, v, hi]
    · unfold fiveWeight
      have hfilter :
          Finset.univ.filter (fun j : Fin 4 => v j ≠ 0) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        by_cases hji : j = i
        · subst j
          simp [v]
        · simp [v, hji]
      rw [hfilter, Finset.card_singleton]

private theorem five_submodule_weight_one_or_twenty_four_weight_two
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 125) :
    (∃ w : W, fiveWeight w = 1) ∨
      (Nat.card {w : W // fiveWeight w = 2} = 24 ∧
        ∀ i, ∃ w : W, w.1 i ≠ 0) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hWpow :=
    Module.natCard_eq_pow_finrank
      (K := ZMod 5) (V := W)
  rw [Nat.card_zmod, hWcard] at hWpow
  have hWfinrank :
      Module.finrank (ZMod 5) W = 3 := by
    have hle : Module.finrank (ZMod 5) W ≤ 4 := by
      calc
        Module.finrank (ZMod 5) W ≤
            Module.finrank (ZMod 5) FiveVector :=
          Submodule.finrank_le W
        _ = 4 := by
          rw [Module.finrank_fintype_fun_eq_card,
            Fintype.card_fin]
    interval_cases Module.finrank (ZMod 5) W
    all_goals norm_num at hWpow
    all_goals omega
  obtain ⟨Q, hQ⟩ :=
    Submodule.exists_isCompl W
  have hQfinrank :
      Module.finrank (ZMod 5) Q = 1 := by
    have hsum :=
      Submodule.finrank_add_eq_of_isCompl hQ
    rw [hWfinrank,
      Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hsum
    omega
  let eQ : ZMod 5 ≃ₗ[ZMod 5] Q :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one
      hQfinrank).some
  let proj : FiveVector →ₗ[ZMod 5] Q :=
    Q.projectionOnto W hQ.symm
  let f : FiveVector →ₗ[ZMod 5] ZMod 5 :=
    eQ.symm.toLinearMap.comp proj
  have hfker : LinearMap.ker f = W := by
    ext v
    simp [f, proj]
  let c : FiveVector :=
    fun i => f (Pi.single i 1)
  have hf_eq_dot (v : FiveVector) :
      f v = fiveDot c v := by
    have hv :
        v = ∑ i, (v i) • Pi.single i (1 : ZMod 5) := by
      calc
        v = ∑ i, Pi.single i (v i) :=
          (Finset.univ_sum_single v).symm
        _ = ∑ i, (v i) • Pi.single i (1 : ZMod 5) := by
          apply Finset.sum_congr rfl
          intro i _
          ext j
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
    calc
      f v = f (∑ i, (v i) •
          Pi.single i (1 : ZMod 5)) := by rw [← hv]
      _ = ∑ i, (v i) •
          f (Pi.single i (1 : ZMod 5)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
      _ = fiveDot c v := by
        simp only [fiveDot, c, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hmem (v : FiveVector) :
      fiveDot c v = 0 ↔ v ∈ W := by
    rw [← hf_eq_dot]
    change v ∈ LinearMap.ker f ↔ v ∈ W
    rw [hfker]
  rcases
      five_hyperplane_weight_one_or_twenty_four_weight_two c with
      hone | ⟨htwentyFour, hc⟩
  · left
    obtain ⟨v, hvker, hvweight⟩ := hone
    exact ⟨⟨v, (hmem v).mp hvker⟩, hvweight⟩
  · right
    refine ⟨?_, ?_⟩
    let A :=
      {v : FiveVector //
        fiveDot c v = 0 ∧ fiveWeight v = 2}
    let B :=
      {w : W // fiveWeight w = 2}
    let E : A ≃ B := {
      toFun := fun v =>
        ⟨⟨v, (hmem v).mp v.prop.1⟩, v.prop.2⟩
      invFun := fun w =>
        ⟨w, ⟨(hmem w).mpr w.1.prop, w.prop⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        rfl
      right_inv := fun w => by
        apply Subtype.ext
        rfl }
    have hAcard : Nat.card A = 24 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype]
      exact htwentyFour
    calc
      Nat.card B = Nat.card A :=
        Nat.card_congr E.symm
      _ = 24 := hAcard
    intro i
    let j : Fin 4 :=
      if i = 0 then 1 else 0
    have hji : j ≠ i := by
      dsimp [j]
      split
      · omega
      · omega
    let v : FiveVector :=
      Pi.single i (c j) - Pi.single j (c i)
    have hvdot : fiveDot c v = 0 := by
      have hsingle (k : Fin 4) (z : ZMod 5) :
          (∑ x, c x *
            (Pi.single k z : FiveVector) x) =
            c k * z := by
        rw [Fintype.sum_eq_single k]
        · rw [Pi.single_eq_same]
        · intro x hx
          rw [Pi.single_eq_of_ne hx]
          simp
      unfold fiveDot
      simp only [v, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
      rw [hsingle, hsingle, mul_comm]
      simp
    refine ⟨⟨v, (hmem v).mp hvdot⟩, ?_⟩
    change v i ≠ 0
    simpa [v, hji] using hc j

theorem fourFiveBase_support_card_eq_five_mul_weight
    (a : FourFiveBase) :
    ((MulAction.toPermHom
      FourFiveBase TwentyFourFivePoints) a).support.card =
      5 * fiveWeight a := by
  classical
  let F : Finset (Fin 4) := Finset.univ.filter (fun i => a i ≠ 1)
  let e : Degree20.TwentyFivePoints ↪ TwentyFourFivePoints :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hs : ((MulAction.toPermHom FourFiveBase TwentyFourFivePoints) a).support =
      (F ×ˢ Finset.univ).map e := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨i, z⟩
      simp only [Equiv.Perm.mem_support, Finset.mem_map]
      change (Sum.inl (i, a i * z) : TwentyFourFivePoints) ≠ Sum.inl (i, z) ↔ _
      simp [e, F, mul_eq_right]
    | inr i =>
      simp only [Equiv.Perm.mem_support, Finset.mem_map]
      change (Sum.inr i : TwentyFourFivePoints) ≠ Sum.inr i ↔ _
      simp [e]
  rw [hs, Finset.card_map, Finset.card_product, Finset.card_univ]
  change fiveWeight a * Fintype.card Degree20.FiveCycle = 5 * fiveWeight a
  have hc : Fintype.card Degree20.FiveCycle = 5 := by
    simpa only [Nat.card_eq_fintype_card] using Degree20.card_fiveCycle
  rw [hc, Nat.mul_comm]

private theorem fourFive_subgroup_support_five_or_twenty_four_support_ten
    (A : Subgroup FourFiveBase)
    (hAcard : Nat.card A = 125) :
    (∃ a : A,
      ((MulAction.toPermHom
        FourFiveBase TwentyFourFivePoints) a).support.card = 5) ∨
    (Nat.card {a : A //
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card = 10} = 24 ∧
      ∀ i, ∃ a : A, (a.1 i) ≠ 1) := by
  let B : AddSubgroup FiveVector :=
    A.toAddSubgroup'
  let W : Submodule (ZMod 5) FiveVector :=
    AddSubgroup.toZModSubmodule 5 B
  let eAW : A ≃ W := {
    toFun := fun a => ⟨
      (fun i => Multiplicative.toAdd (a.1 i)), by
        change
          (fun i => Multiplicative.ofAdd
            (Multiplicative.toAdd (a.1 i))) ∈ A
        exact a.prop⟩
    invFun := fun w => ⟨
      (fun i => Multiplicative.ofAdd (w.1 i)), by
        change Multiplicative.ofAdd w.1 ∈ A
        exact w.prop⟩
    left_inv := fun a => by
      apply Subtype.ext
      funext i
      rfl
    right_inv := fun w => by
      apply Subtype.ext
      funext i
      rfl }
  have hWcard : Nat.card W = 125 := by
    calc
      Nat.card W = Nat.card A :=
        Nat.card_congr eAW.symm
      _ = 125 := hAcard
  rcases
      five_submodule_weight_one_or_twenty_four_weight_two
        W hWcard with hone | ⟨htwo, hactive⟩
  · left
    obtain ⟨w, hw⟩ := hone
    let a : A := eAW.symm w
    refine ⟨a, ?_⟩
    rw [fourFiveBase_support_card_eq_five_mul_weight]
    have haweight :
        fiveWeight (a : FourFiveBase) =
          fiveWeight (w : FiveVector) := by
      rfl
    rw [haweight, hw]
  · right
    refine ⟨?_, ?_⟩
    let C :=
      {w : W // fiveWeight w = 2}
    let D :=
      {a : A //
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card = 10}
    let E : C ≃ D := {
      toFun := fun w => ⟨eAW.symm w.1, by
        rw [fourFiveBase_support_card_eq_five_mul_weight,
          show fiveWeight ((eAW.symm w.1 : A) :
              FourFiveBase) =
            fiveWeight (w.1 : FiveVector) by rfl,
          w.prop]⟩
      invFun := fun a => ⟨eAW a.1, by
        have ha := a.prop
        rw [fourFiveBase_support_card_eq_five_mul_weight] at ha
        change fiveWeight (a.1 : FourFiveBase) = 2
        omega⟩
      left_inv := fun w => by
        apply Subtype.ext
        exact eAW.apply_symm_apply w.1
      right_inv := fun a => by
        apply Subtype.ext
        exact eAW.symm_apply_apply a.1 }
    calc
      Nat.card D = Nat.card C :=
        Nat.card_congr E.symm
      _ = 24 := htwo
    intro i
    obtain ⟨w, hw⟩ := hactive i
    refine ⟨eAW.symm w, ?_⟩
    change Multiplicative.ofAdd (w.1 i) ≠ 1
    simpa using hw

theorem subgroup_support_five_or_twenty_four_support_ten
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 24)
    (R : Subgroup (Equiv.Perm X))
    (hRcard : Nat.card R = 125) :
    (∃ r : R, (r.1.support.card = 5)) ∨
      (Nat.card {r : R // r.1.support.card = 10} = 24 ∧
        Nat.card (MulAction.fixedPoints R X) = 4) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hRpGroup : IsPGroup 5 R :=
    IsPGroup.of_card (n := 3)
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
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
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
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hRQ
  let A : Subgroup FourFiveBase :=
    R'.comap standardMap
  have hAmap : A.map standardMap = R' :=
    Subgroup.map_comap_eq_self hR'le
  let eAR' : A ≃* R' :=
    (A.equivMapOfInjective standardMap hstandardMap).trans
      (MulEquiv.subgroupCongr hAmap)
  let eRR' : R ≃* R' :=
    conjugation.subgroupMap R
  let eAR : A ≃ R :=
    eAR'.toEquiv.trans eRR'.symm.toEquiv
  have hAcard : Nat.card A = 125 := by
    calc
      Nat.card A = Nat.card R :=
        Nat.card_congr eAR
      _ = 125 := hRcard
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
  rcases
      fourFive_subgroup_support_five_or_twenty_four_support_ten
        A hAcard with hone | ⟨hten, hactive⟩
  · left
    obtain ⟨a, ha⟩ := hone
    exact ⟨eAR a, (hsupport a).trans ha⟩
  · right
    refine ⟨?_, ?_⟩
    let C :=
      {a : A //
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card = 10}
    let D :=
      {r : R // r.1.support.card = 10}
    let E : C ≃ D := {
      toFun := fun a => ⟨eAR a.1,
        (hsupport a.1).trans a.prop⟩
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
      Nat.card D = Nat.card C :=
        Nat.card_congr E.symm
      _ = 24 := hten
    have hfixedA :
        Nat.card
          (MulAction.fixedPoints A
            TwentyFourFivePoints) = 4 := by
      have hfixed :
          MulAction.fixedPoints A
              TwentyFourFivePoints =
            Set.range (Sum.inr :
              Fin 4 → TwentyFourFivePoints) := by
        ext x
        constructor
        · intro hx
          cases x with
          | inl x =>
              exfalso
              obtain ⟨a, ha⟩ := hactive x.1
              rw [MulAction.mem_fixedPoints] at hx
              have hax := hx a
              injection hax with hax
              have hsecond := congrArg Prod.snd hax
              change a.1 x.1 * x.2 = x.2 at hsecond
              apply ha
              rw [← mul_right_cancel_iff (a := x.2)]
              simpa using hsecond
          | inr i =>
              exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          rw [MulAction.mem_fixedPoints]
          intro a
          rfl
      rw [Nat.card_coe_set_eq, hfixed,
        Set.ncard_range_of_injective Sum.inr_injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
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
        ⟨d.symm y.1, (hfixedIff (d.symm y.1)).mpr (by
          rw [d.apply_symm_apply]
          exact y.prop)⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact d.symm_apply_apply x.1
      right_inv := fun y => by
        apply Subtype.ext
        exact d.apply_symm_apply y.1 }
    calc
      Nat.card (MulAction.fixedPoints R X) =
          Nat.card
            (MulAction.fixedPoints A
              TwentyFourFivePoints) :=
        Nat.card_congr Efixed
      _ = 4 := hfixedA

end FiveTransitive.Degree24

end CFSG
