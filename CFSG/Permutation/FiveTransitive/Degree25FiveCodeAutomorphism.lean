module

public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeSubmodule

public section

namespace CFSG

namespace FiveTransitive.Degree25

open FiveTransitive.Degree24

@[expose] def fourFiveSubgroupAddEquiv
    (A : Subgroup Degree20.FourFiveBase) :
    let B : AddSubgroup FiveVector :=
      A.toAddSubgroup'
    Additive A ≃+
      AddSubgroup.toZModSubmodule 5 B := by
  let B : AddSubgroup FiveVector :=
    A.toAddSubgroup'
  exact {
  toFun a := ⟨
    (fun i => Multiplicative.toAdd (a.toMul.1 i)), by
      change
        (fun i => Multiplicative.ofAdd
          (Multiplicative.toAdd (a.toMul.1 i))) ∈ A
      exact a.toMul.prop⟩
  invFun w :=
    Additive.ofMul ⟨
      (fun i => Multiplicative.ofAdd (w.1 i)), by
        change Multiplicative.ofAdd w.1 ∈ A
        exact w.prop⟩
  left_inv a := by
    rfl
  right_inv w := by
    apply Subtype.ext
    funext i
    rfl
  map_add' a b := by
    apply Subtype.ext
    funext i
    rfl }

theorem fourFive_subgroup_weight_preserving_mulAut_order_ne_five
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ v : A,
        fiveWeight
          ((v : A) : Degree20.FourFiveBase) = 1)
    (a : MulAut A)
    (hweight : ∀ v : A,
      fiveWeight
          (((a v : A) : A) :
            Degree20.FourFiveBase) =
        fiveWeight
          ((v : A) : Degree20.FourFiveBase)) :
    orderOf a ≠ 5 := by
  classical
  let B : AddSubgroup FiveVector :=
    A.toAddSubgroup'
  let W : Submodule (ZMod 5) FiveVector :=
    AddSubgroup.toZModSubmodule 5 B
  let eAW : Additive A ≃+ W :=
    fourFiveSubgroupAddEquiv A
  let addAut : W ≃+ W :=
    eAW.symm.trans
      ((MulEquiv.toAdditive a).trans eAW)
  let linMap : W →ₗ[ZMod 5] W :=
    AddMonoidHom.toZModLinearMapEquiv 5
      addAut.toAddMonoidHom
  have hlinMapBijective :
      Function.Bijective linMap := by
    constructor
    · intro x y hxy
      apply addAut.injective
      exact hxy
    · intro y
      obtain ⟨x, hx⟩ := addAut.surjective y
      exact ⟨x, hx⟩
  let linAut : W ≃ₗ[ZMod 5] W :=
    LinearEquiv.ofBijective linMap hlinMapBijective
  have hWcard : Nat.card W = 125 := by
    calc
      Nat.card W = Nat.card (Additive A) :=
        Nat.card_congr eAW.symm.toEquiv
      _ = Nat.card A := Nat.card_congr Additive.toMul
      _ = 125 := hAcard
  have heAWWeight (v : Additive A) :
      fiveWeight (eAW v) =
        fiveWeight
          ((v.toMul : A) :
            Degree20.FourFiveBase) := by
    rfl
  have hnoWeightOneW :
      ¬∃ w : W, fiveWeight w = 1 := by
    rintro ⟨w, hw⟩
    apply hnoWeightOne
    let v : Additive A := eAW.symm w
    refine ⟨v.toMul, ?_⟩
    rw [← heAWWeight v]
    rw [eAW.apply_symm_apply]
    exact hw
  have hlinWeight :
      ∀ w : W,
        fiveWeight (linAut w) = fiveWeight w := by
    intro w
    let v : Additive A := eAW.symm w
    calc
      fiveWeight (linAut w) =
          fiveWeight
            (eAW
              (Additive.ofMul
                (a v.toMul))) := rfl
      _ = fiveWeight
          (((a v.toMul : A) : A) :
            Degree20.FourFiveBase) :=
        heAWWeight
          (Additive.ofMul (a v.toMul))
      _ = fiveWeight
          ((v.toMul : A) :
            Degree20.FourFiveBase) :=
        hweight v.toMul
      _ = fiveWeight (eAW v) :=
        (heAWWeight v).symm
      _ = fiveWeight w := by
        rw [eAW.apply_symm_apply]
  intro haOrder
  have haPow : a ^ 5 = 1 := by
    simpa only [haOrder] using pow_orderOf_eq_one a
  have hlinPow : linAut ^ 5 = 1 := by
    apply LinearEquiv.ext
    intro w
    rw [LinearEquiv.coe_one]
    simp only [id_eq]
    let v : Additive A := eAW.symm w
    have happ : (a ^ 5) v.toMul = v.toMul := by
      rw [haPow]
      rfl
    simp only [pow_succ, pow_zero, one_mul,
      LinearEquiv.mul_apply]
    change
      eAW
          (Additive.ofMul
            ((a ^ 5) (eAW.symm w).toMul)) =
        w
    rw [happ]
    exact eAW.apply_symm_apply w
  have hlinNe : linAut ≠ 1 := by
    intro hlinOne
    have haOne : a = 1 := by
      apply MulEquiv.ext
      intro v
      let w : W := eAW (Additive.ofMul v)
      have happ :=
        congrArg
          (fun q : W ≃ₗ[ZMod 5] W => q w)
          hlinOne
      change addAut w = w at happ
      change eAW (Additive.ofMul (a v)) = w at happ
      have happ' := congrArg eAW.symm happ
      have happ'' :=
        congrArg
          (fun z : Additive A => z.toMul)
          happ'
      apply Subtype.ext
      exact congrArg (fun z : A => z.1) happ''
    rw [haOne, orderOf_one] at haOrder
    norm_num at haOrder
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlinOrder : orderOf linAut = 5 :=
    orderOf_eq_prime hlinPow hlinNe
  exact
    five_submodule_weight_preserving_order_ne_five
      W hWcard hnoWeightOneW linAut hlinWeight hlinOrder

end FiveTransitive.Degree25

end CFSG
