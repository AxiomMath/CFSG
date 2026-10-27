module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwo

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree24

local instance fivePrimeTwoLift : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private noncomputable def fiveSubmoduleWeightCount
    (W : Submodule (ZMod 5) FiveVector)
    (k : ℕ) : ℕ :=
  Nat.card {w : W // fiveWeight w = k}

private noncomputable def fiveSubmoduleActiveCoordinates
    (W : Submodule (ZMod 5) FiveVector) : ℕ :=
  by
    classical
    exact
      (Finset.univ.filter fun i : Fin 4 =>
        ∃ w : W, w.1 i ≠ 0).card

private theorem five_submodule_card_twenty_five_weight_distribution
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 25) :
    0 < fiveSubmoduleWeightCount W 1 ∨
      (fiveSubmoduleActiveCoordinates W = 3 ∧
        fiveSubmoduleWeightCount W 2 = 12 ∧
        fiveSubmoduleWeightCount W 3 = 12) ∨
      (fiveSubmoduleActiveCoordinates W = 4 ∧
        ((fiveSubmoduleWeightCount W 2 = 8 ∧
            fiveSubmoduleWeightCount W 3 = 0) ∨
          (fiveSubmoduleWeightCount W 2 = 4 ∧
            fiveSubmoduleWeightCount W 3 = 8) ∨
          (fiveSubmoduleWeightCount W 2 = 0 ∧
            fiveSubmoduleWeightCount W 3 = 16))) := by
  classical
  have hWpow :=
    Module.natCard_eq_pow_finrank
      (K := ZMod 5) (V := W)
  rw [Nat.card_zmod, hWcard] at hWpow
  have hWfinrank :
      Module.finrank (ZMod 5) W = 2 := by
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
  let b : Module.Basis (Fin 2) (ZMod 5) W :=
    Module.finBasisOfFinrankEq (ZMod 5) W hWfinrank
  let e : (Fin 2 → ZMod 5) ≃ₗ[ZMod 5] W :=
    b.equivFun.symm
  let e₀ : Fin 2 → ZMod 5 := ![1, 0]
  let e₁ : Fin 2 → ZMod 5 := ![0, 1]
  let u : FiveVector := (e e₀).1
  let v : FiveVector := (e e₁).1
  have hdecompose (x : Fin 2 → ZMod 5) :
      x = x 0 • e₀ + x 1 • e₁ := by
    funext i
    fin_cases i <;> simp [e₀, e₁]
  have hword (x : Fin 2 → ZMod 5) :
      twoFiveWord u v x = (e x).1 := by
    calc
      twoFiveWord u v x =
          x 0 • u + x 1 • v := by
        funext i
        rfl
      _ = (x 0 • e e₀ + x 1 • e e₁ : W).1 := by
        rfl
      _ = (e (x 0 • e₀ + x 1 • e₁)).1 := by
        rw [map_add, map_smul, map_smul]
      _ = (e x).1 := by
        rw [← hdecompose x]
  have hinjective :
      Function.Injective (twoFiveWord u v) := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    rw [← hword x, ← hword y, hxy]
  have hcount (k : ℕ) :
      twoFiveWeightCount u v k =
        fiveSubmoduleWeightCount W k := by
    let C :=
      {x : Fin 2 → ZMod 5 //
        fiveWeight (twoFiveWord u v x) = k}
    let D :=
      {w : W // fiveWeight w.1 = k}
    let E : C ≃ D := {
      toFun := fun x => ⟨e x.1, by
        rw [← hword x.1]
        exact x.prop⟩
      invFun := fun w => ⟨e.symm w.1, by
        rw [hword, e.apply_symm_apply]
        exact w.prop⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := fun w => by
        apply Subtype.ext
        exact e.apply_symm_apply w.1 }
    calc
      twoFiveWeightCount u v k =
          Fintype.card C := by
        rw [Fintype.card_subtype]
        rfl
      _ = Fintype.card D :=
        Fintype.card_congr E
      _ = fiveSubmoduleWeightCount W k := by
        rw [fiveSubmoduleWeightCount,
          Nat.card_eq_fintype_card]
  have hactive :
      twoFiveActiveCoordinates u v =
        fiveSubmoduleActiveCoordinates W := by
    unfold twoFiveActiveCoordinates
    unfold fiveSubmoduleActiveCoordinates
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨e x, ?_⟩
      rw [← hword x]
      exact hx
    · rintro ⟨w, hw⟩
      obtain ⟨x, rfl⟩ := e.surjective w
      refine ⟨x, ?_⟩
      rw [hword]
      exact hw
  have hdistribution :=
    twoFiveCode_weight_distribution u v hinjective
  rwa [hactive, hcount 1, hcount 2,
    hcount 3] at hdistribution

@[expose] noncomputable def fourFiveSubgroupSupportCount
    (A : Subgroup FourFiveBase)
    (m : ℕ) : ℕ :=
  Nat.card {a : A //
    ((MulAction.toPermHom
      FourFiveBase TwentyFourFivePoints) a).support.card = m}

@[expose] noncomputable def fourFiveSubgroupActiveCoordinates
    (A : Subgroup FourFiveBase) : ℕ :=
  by
    classical
    exact
      (Finset.univ.filter fun i : Fin 4 =>
        ∃ a : A, a.1 i ≠ 1).card

theorem fourFive_subgroup_card_twenty_five_support_distribution
    (A : Subgroup FourFiveBase)
    (hAcard : Nat.card A = 25) :
    0 < fourFiveSubgroupSupportCount A 5 ∨
      (fourFiveSubgroupActiveCoordinates A = 3 ∧
        fourFiveSubgroupSupportCount A 10 = 12 ∧
        fourFiveSubgroupSupportCount A 15 = 12) ∨
      (fourFiveSubgroupActiveCoordinates A = 4 ∧
        ((fourFiveSubgroupSupportCount A 10 = 8 ∧
            fourFiveSubgroupSupportCount A 15 = 0) ∨
          (fourFiveSubgroupSupportCount A 10 = 4 ∧
            fourFiveSubgroupSupportCount A 15 = 8) ∨
          (fourFiveSubgroupSupportCount A 10 = 0 ∧
            fourFiveSubgroupSupportCount A 15 = 16))) := by
  classical
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
  have hWcard : Nat.card W = 25 := by
    calc
      Nat.card W = Nat.card A :=
        Nat.card_congr eAW.symm
      _ = 25 := hAcard
  have hcount (k : ℕ) :
      fiveSubmoduleWeightCount W k =
        fourFiveSubgroupSupportCount A (5 * k) := by
    let C :=
      {w : W // fiveWeight w.1 = k}
    let D :=
      {a : A //
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints) a).support.card =
            5 * k}
    let E : C ≃ D := {
      toFun := fun w => ⟨eAW.symm w.1, by
        rw [fourFiveBase_support_card_eq_five_mul_weight]
        change
          5 * fiveWeight (w.1 : FiveVector) = 5 * k
        rw [w.prop]⟩
      invFun := fun a => ⟨eAW a.1, by
        have ha := a.prop
        rw [fourFiveBase_support_card_eq_five_mul_weight] at ha
        change
          fiveWeight (a.1 : FourFiveBase) = k
        omega⟩
      left_inv := fun w => by
        apply Subtype.ext
        exact eAW.apply_symm_apply w.1
      right_inv := fun a => by
        apply Subtype.ext
        exact eAW.symm_apply_apply a.1 }
    calc
      fiveSubmoduleWeightCount W k =
          Nat.card C := by
        rfl
      _ = Nat.card D :=
        Nat.card_congr E
      _ = fourFiveSubgroupSupportCount A (5 * k) := by
        rfl
  have hactive :
      fiveSubmoduleActiveCoordinates W =
        fourFiveSubgroupActiveCoordinates A := by
    unfold fiveSubmoduleActiveCoordinates
    unfold fourFiveSubgroupActiveCoordinates
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨eAW.symm w, ?_⟩
      change Multiplicative.ofAdd (w.1 i) ≠ 1
      simpa using hw
    · rintro ⟨a, ha⟩
      refine ⟨eAW a, ?_⟩
      change Multiplicative.toAdd (a.1 i) ≠ 0
      simpa using ha
  have hdistribution :=
    five_submodule_card_twenty_five_weight_distribution
      W hWcard
  rw [hactive, hcount 1, hcount 2,
    hcount 3] at hdistribution
  norm_num at hdistribution
  exact hdistribution

theorem card_fixedPoints_fourFiveSubgroup
    (A : Subgroup FourFiveBase) :
    Nat.card
        (MulAction.fixedPoints A TwentyFourFivePoints) =
      (4 - fourFiveSubgroupActiveCoordinates A) * 5 + 4 := by
  classical
  let I :=
    Finset.univ.filter fun i : Fin 4 =>
      ¬∃ a : A, a.1 i ≠ 1
  let E :
      MulAction.fixedPoints A TwentyFourFivePoints ≃
        (I × Degree20.FiveCycle) ⊕ Fin 4 := {
    toFun := fun x =>
      match hx : x.1 with
      | Sum.inl p =>
          Sum.inl
            ⟨⟨p.1, by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              rintro ⟨a, ha⟩
              have hfix :=
                (MulAction.mem_fixedPoints.mp x.prop) a
              rw [hx] at hfix
              injection hfix with hpair
              have hsecond := congrArg Prod.snd hpair
              change a.1 p.1 * p.2 = p.2 at hsecond
              apply ha
              rw [← mul_right_cancel_iff (a := p.2)]
              simpa using hsecond⟩,
              p.2⟩
      | Sum.inr i => Sum.inr i
    invFun := fun y =>
      match y with
      | Sum.inl p =>
          ⟨Sum.inl (p.1.1, p.2), by
            rw [MulAction.mem_fixedPoints]
            intro a
            apply congrArg Sum.inl
            apply Prod.ext
            · rfl
            · change a.1 p.1.1 * p.2 = p.2
              have hinactive := p.1.2
              rw [Finset.mem_filter] at hinactive
              have ha : a.1 p.1.1 = 1 := by
                by_contra hne
                exact hinactive.2 ⟨a, hne⟩
              rw [ha, one_mul]⟩
      | Sum.inr i =>
          ⟨Sum.inr i, by
            rw [MulAction.mem_fixedPoints]
            intro a
            rfl⟩
    left_inv := fun x => by
      rcases x with ⟨x, hx⟩
      cases x with
      | inl p => rfl
      | inr i => rfl
    right_inv := fun y => by
      cases y with
      | inl p =>
          apply congrArg Sum.inl
          apply Prod.ext
          · apply Subtype.ext
            rfl
          · rfl
      | inr i => rfl }
  have hsplit :
      fourFiveSubgroupActiveCoordinates A + I.card = 4 := by
    have hpartition :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 4)))
        (fun i => ∃ a : A, a.1 i ≠ 1)
    simpa [fourFiveSubgroupActiveCoordinates,
      I] using hpartition
  calc
    Nat.card
        (MulAction.fixedPoints A TwentyFourFivePoints) =
        Nat.card
          ((I × Degree20.FiveCycle) ⊕ Fin 4) :=
      Nat.card_congr E
    _ =
        Nat.card I * Nat.card Degree20.FiveCycle +
          Nat.card (Fin 4) := by
      rw [Nat.card_sum, Nat.card_prod]
    _ = I.card * 5 + 4 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_coe,
        Degree20.card_fiveCycle,
        Nat.card_eq_fintype_card,
        Fintype.card_fin]
    _ =
        (4 - fourFiveSubgroupActiveCoordinates A) *
            5 + 4 := by
      omega

end FiveTransitive.Degree24

end CFSG
