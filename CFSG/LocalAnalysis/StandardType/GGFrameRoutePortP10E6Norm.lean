module

public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeCount
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section WeylDual

variable (w w₁ w₂ : WeylGroup TwistTag.E6.tag)

theorem p10i_weylDual_add (y y' : Fin TwistTag.E6.tag.rank → ZMod 3) :
    TwE6NormThree.weylDual w (y + y') =
      TwE6NormThree.weylDual w y + TwE6NormThree.weylDual w y' := by
  funext j
  simp only [TwE6NormThree.weylDual, TwE6NormThree.dot3, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem p10i_weylDual_smul (c : ZMod 3) (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    TwE6NormThree.weylDual w (c • y) = c • TwE6NormThree.weylDual w y := by
  funext j
  simp only [TwE6NormThree.weylDual, TwE6NormThree.dot3, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem p10i_weylDual_one (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    TwE6NormThree.weylDual 1 y = y := by
  funext j
  simp [TwE6NormThree.weylDual, TwE6NormThree.dot3, Pi.single_apply]

theorem p10i_weylDual_mul (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    TwE6NormThree.weylDual (w₁ * w₂) y =
      TwE6NormThree.weylDual w₂ (TwE6NormThree.weylDual w₁ y) := by
  funext j
  simp only [TwE6NormThree.weylDual]
  rw [mul_smul, TwE6NormThree.dot3_smul]

@[expose] noncomputable def p10iWeylPerm :
    WeylGroup TwistTag.E6.tag →* Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod 3) where
  toFun w :=
    { toFun := fun y => TwE6NormThree.weylDual w⁻¹ y
      invFun := fun y => TwE6NormThree.weylDual w y
      left_inv := fun y => by
        show TwE6NormThree.weylDual w (TwE6NormThree.weylDual w⁻¹ y) = y
        rw [← p10i_weylDual_mul, inv_mul_cancel, p10i_weylDual_one]
      right_inv := fun y => by
        show TwE6NormThree.weylDual w⁻¹ (TwE6NormThree.weylDual w y) = y
        rw [← p10i_weylDual_mul, mul_inv_cancel, p10i_weylDual_one] }
  map_one' := Equiv.ext fun y => by
    simp [p10i_weylDual_one]
  map_mul' w₁ w₂ := Equiv.ext fun y => by
    change TwE6NormThree.weylDual (w₁ * w₂)⁻¹ y =
      TwE6NormThree.weylDual w₁⁻¹ (TwE6NormThree.weylDual w₂⁻¹ y)
    rw [mul_inv_rev, p10i_weylDual_mul]

theorem p10iWeylPerm_apply (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    p10iWeylPerm w y = TwE6NormThree.weylDual w⁻¹ y :=
  rfl

end WeylDual

@[expose] noncomputable def p10iScalarPerm :
    (ZMod 3)ˣ →* Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod 3) :=
  MulAction.toPermHom (ZMod 3)ˣ (Fin TwistTag.E6.tag.rank → ZMod 3)

theorem p10iScalarPerm_apply (u : (ZMod 3)ˣ) (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    p10iScalarPerm u y = (u : ZMod 3) • y :=
  rfl

theorem p10i_commute (u : (ZMod 3)ˣ) (w : WeylGroup TwistTag.E6.tag) :
    Commute (p10iScalarPerm u) (p10iWeylPerm w) := by
  refine Equiv.ext fun y => ?_
  change (u : ZMod 3) • TwE6NormThree.weylDual w⁻¹ y =
    TwE6NormThree.weylDual w⁻¹ ((u : ZMod 3) • y)
  rw [p10i_weylDual_smul]

@[expose] noncomputable def p10iPerm :
    (ZMod 3)ˣ × WeylGroup TwistTag.E6.tag →* Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod 3) :=
  p10iScalarPerm.noncommCoprod p10iWeylPerm p10i_commute

theorem p10iPerm_apply (u : (ZMod 3)ˣ) (w : WeylGroup TwistTag.E6.tag)
    (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    p10iPerm (u, w) y = (u : ZMod 3) • TwE6NormThree.weylDual w⁻¹ y := by
  rw [p10iPerm, MonoidHom.noncommCoprod_apply]
  rfl

theorem p10i_card_perm_domain :
    Nat.card ((ZMod 3)ˣ × WeylGroup TwistTag.E6.tag) = 103680 := by
  have hW : Nat.card (WeylGroup TwistTag.E6.tag) = 51840 :=
    CFSG.RankThree.E6.card_weylGroup_E6
  have hU : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_prod, hW, hU]

@[expose] noncomputable def p10iCoordHom {K : Type} [Group K] (A : Subgroup (MulAut K))
    (e : A ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3)) :
    MulAut ↥A →* Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod 3) :=
  (Equiv.permCongrHom (e.toEquiv.trans Multiplicative.toAdd)).toMonoidHom.comp (MulAut.toPerm ↥A)

theorem p10iCoordHom_apply {K : Type} [Group K] (A : Subgroup (MulAut K))
    (e : A ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3)) (ξ : MulAut ↥A)
    (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    p10iCoordHom A e ξ y =
      Multiplicative.toAdd (e (ξ (e.symm (Multiplicative.ofAdd y)))) :=
  rfl

theorem p10iCoordHom_injective {K : Type} [Group K] (A : Subgroup (MulAut K))
    (e : A ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3)) :
    Function.Injective (p10iCoordHom A e) := by
  intro ξ ξ' h
  refine MulEquiv.ext fun a => ?_
  have h1 := congrArg (fun p => p (Multiplicative.toAdd (e a))) h
  simp only [p10iCoordHom_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1
  exact e.injective (Multiplicative.toAdd.injective h1)

set_option linter.unusedVariables false in
theorem p10i_twE6_normalizer_bound
    {K : Type} [Group K] [Finite K] (A : Subgroup (MulAut K))
    (e : A ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3))
    (hreal : ∀ α : MulAut K, ∀ hα : α ∈ Subgroup.normalizer (A : Set (MulAut K)),
      ∃ (w : WeylGroup TwistTag.E6.tag) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
        ∀ a : A, Multiplicative.toAdd (e (ggConjAut A hα a)) =
          ε • TwE6NormThree.weylDual w (Multiplicative.toAdd (e a))) :
    Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) A) ∣ 103680 := by
  have hinj := p10iCoordHom_injective A e
  have hle : (ggAutomizer (⊤ : Subgroup (MulAut K)) A).map (p10iCoordHom A e) ≤
      p10iPerm.range := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hEq : φ = ggConjAut A hgN := MulEquiv.ext fun b => Subtype.ext (hφg b)
    obtain ⟨w, ε, hε, hact⟩ := hreal g hgN
    have hne : ε ≠ 0 := by
      rcases hε with rfl | rfl <;> decide
    refine ⟨(Units.mk0 ε hne, w⁻¹), ?_⟩
    refine Equiv.ext fun y => ?_
    rw [p10iPerm_apply, hEq, p10iCoordHom_apply, inv_inv]
    have h1 := hact (e.symm (Multiplicative.ofAdd y))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
    rw [h1]
    rfl
  have h2 : Nat.card ((ggAutomizer (⊤ : Subgroup (MulAut K)) A).map (p10iCoordHom A e)) =
      Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) A) :=
    Subgroup.card_map_of_injective hinj
  rw [← h2]
  exact (Subgroup.card_dvd_of_le hle).trans
    ((Subgroup.card_range_dvd p10iPerm).trans (p10i_card_perm_domain ▸ dvd_rfl))

end CFSG.StandardType.FrameRoute

end
