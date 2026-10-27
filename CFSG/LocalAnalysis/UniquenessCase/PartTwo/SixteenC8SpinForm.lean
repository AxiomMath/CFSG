module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LieType.SpinGeom
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private theorem sixteenC8SpinForm_polarQ_eq (x y : SpinW) :
    polarQ spinQ x y = QuadraticMap.polar (coordinateQuadPlus 4 (ZMod 2))
      (Multiplicative.toAdd x) (Multiplicative.toAdd y) := by
  unfold polarQ spinQ
  rw [toAdd_mul]
  rfl

private theorem sixteenC8SpinForm_polar_add_left_gen {K : Type} [Field K]
    (x y z : Fin (2 * 4) → K) :
    QuadraticMap.polar (coordinateQuadPlus 4 K) (x + y) z =
      QuadraticMap.polar (coordinateQuadPlus 4 K) x z +
        QuadraticMap.polar (coordinateQuadPlus 4 K) y z :=
  QuadraticMap.polar_add_left _ _ _ _

private theorem sixteenC8SpinForm_polar_add_right_gen {K : Type} [Field K]
    (x y z : Fin (2 * 4) → K) :
    QuadraticMap.polar (coordinateQuadPlus 4 K) x (y + z) =
      QuadraticMap.polar (coordinateQuadPlus 4 K) x y +
        QuadraticMap.polar (coordinateQuadPlus 4 K) x z :=
  QuadraticMap.polar_add_right _ _ _ _

private theorem sixteenC8SpinForm_polarQ_frameF (x : SpinW) (k : Fin 4) :
    polarQ spinQ x (Multiplicative.ofAdd (frameF (ZMod 2) k)) =
      coordX (ZMod 2) (Multiplicative.toAdd x) k := by
  rw [sixteenC8SpinForm_polarQ_eq, toAdd_ofAdd]
  rfl

private theorem sixteenC8SpinForm_polarQ_frameE (x : SpinW) (k : Fin 4) :
    polarQ spinQ x (Multiplicative.ofAdd (frameE (ZMod 2) k)) =
      coordY (ZMod 2) (Multiplicative.toAdd x) k := by
  rw [sixteenC8SpinForm_polarQ_eq, toAdd_ofAdd]
  rfl

private theorem sixteenC8SpinForm_isQuadF2 : IsQuadF2 spinQ := by
  constructor
  · intro x y z
    rw [sixteenC8SpinForm_polarQ_eq, sixteenC8SpinForm_polarQ_eq,
      sixteenC8SpinForm_polarQ_eq, toAdd_mul]
    exact sixteenC8SpinForm_polar_add_left_gen (Multiplicative.toAdd x)
      (Multiplicative.toAdd y) (Multiplicative.toAdd z)
  · intro x y z
    rw [sixteenC8SpinForm_polarQ_eq, sixteenC8SpinForm_polarQ_eq,
      sixteenC8SpinForm_polarQ_eq, toAdd_mul]
    exact sixteenC8SpinForm_polar_add_right_gen (Multiplicative.toAdd x)
      (Multiplicative.toAdd y) (Multiplicative.toAdd z)

private theorem sixteenC8SpinForm_nondegenerate :
    ∀ x : SpinW, x ≠ 1 → ∃ y : SpinW, polarQ spinQ x y ≠ 0 := by
  classical
  intro x hx
  have hv : Multiplicative.toAdd x ≠ 0 := fun h => hx (toAdd_eq_zero.1 h)
  by_cases hX : ∃ k : Fin 4, coordX (ZMod 2) (Multiplicative.toAdd x) k ≠ 0
  · obtain ⟨k, hk⟩ := hX
    exact ⟨Multiplicative.ofAdd (frameF (ZMod 2) k),
      by rw [sixteenC8SpinForm_polarQ_frameF]; exact hk⟩
  · have hX0 : ∀ k : Fin 4, coordX (ZMod 2) (Multiplicative.toAdd x) k = 0 := by
      intro k
      by_contra hk
      exact hX ⟨k, hk⟩
    have hY : ∃ k : Fin 4, coordY (ZMod 2) (Multiplicative.toAdd x) k ≠ 0 := by
      by_contra h
      have hY0 : ∀ k : Fin 4, coordY (ZMod 2) (Multiplicative.toAdd x) k = 0 := by
        intro k
        by_contra hk
        exact h ⟨k, hk⟩
      exact hv (vec_ext (fun k => by rw [hX0 k, coordX_zero])
        fun k => by rw [hY0 k, coordY_zero])
    obtain ⟨k, hk⟩ := hY
    exact ⟨Multiplicative.ofAdd (frameE (ZMod 2) k),
      by rw [sixteenC8SpinForm_polarQ_frameE]; exact hk⟩

private def sixteenC8SpinFormU :
    @Subgroup SpinW ((inferInstance : CommGroup SpinW)).toGroup where
  carrier := {w | ∀ k : Fin 4, coordY (ZMod 2) (Multiplicative.toAdd w) k = 0}
  mul_mem' := fun {a b} ha hb k => by
    rw [toAdd_mul]
    exact (coordY_add (Multiplicative.toAdd a) (Multiplicative.toAdd b) k).trans
      (by rw [ha k, hb k, add_zero])
  one_mem' := fun k => by
    rw [toAdd_one]
    exact coordY_zero k
  inv_mem' := fun {a} ha k => by
    rw [toAdd_inv]
    change coordY (ZMod 2) (0 - Multiplicative.toAdd a) k = 0
    rw [coordY_sub (0 : Fin (2 * 4) → ZMod 2) (Multiplicative.toAdd a) k, coordY_zero,
      ha k]
    simp

private noncomputable def sixteenC8SpinFormUEquiv :
    ↥sixteenC8SpinFormU ≃ (Fin 4 → ZMod 2) :=
  Equiv.ofBijective
    (fun w => fun k => coordX (ZMod 2) (Multiplicative.toAdd (w : SpinW)) k) (by
      constructor
      · intro w w' h
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        apply vec_ext
        · intro k
          exact congrFun h k
        · intro k
          rw [w.2 k, w'.2 k]
      · intro a
        refine ⟨⟨Multiplicative.ofAdd (∑ k : Fin 4, a k • frameE (ZMod 2) k), ?_⟩, ?_⟩
        · intro k
          rw [toAdd_ofAdd]
          exact (coordY_sum Finset.univ (fun j : Fin 4 => a j • frameE (ZMod 2) j) k).trans
            (Finset.sum_eq_zero fun j _ => by
              rw [coordY_smul (a j) (frameE (ZMod 2) j) k, coordY_frameE j k, mul_zero])
        · funext k
          change coordX (ZMod 2)
            (Multiplicative.toAdd (Multiplicative.ofAdd
              (∑ j : Fin 4, a j • frameE (ZMod 2) j))) k = a k
          rw [toAdd_ofAdd]
          refine (coordX_sum Finset.univ
            (fun j : Fin 4 => a j • frameE (ZMod 2) j) k).trans ?_
          trans ∑ j ∈ Finset.univ, (if j = k then a j else 0)
          · exact Finset.sum_congr rfl fun j _ => by
              by_cases h : j = k
              · rw [coordX_smul (a j) (frameE (ZMod 2) j) k, coordX_frameE j k, if_pos h,
                  if_pos h, mul_one]
              · rw [coordX_smul (a j) (frameE (ZMod 2) j) k, coordX_frameE j k, if_neg h,
                  if_neg h, mul_zero]
          · exact Finset.sum_ite_eq_of_mem' Finset.univ k a (Finset.mem_univ k))

private theorem sixteenC8SpinForm_cardU : Nat.card ↥sixteenC8SpinFormU = 2 ^ 4 := by
  rw [Nat.card_congr sixteenC8SpinFormUEquiv, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem sixteenC8SpinForm_cardSpinW : Nat.card SpinW = 2 ^ 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem sixteenC8SpinForm_rankU : rk ↥sixteenC8SpinFormU = 4 := by
  unfold rk
  rw [sixteenC8SpinForm_cardU, padicValNat.prime_pow]

theorem spinQ_isPlus : IsPlusQuadF2 spinQ := by
  refine ⟨⟨sixteenC8SpinForm_isQuadF2, sixteenC8SpinForm_nondegenerate⟩,
    sixteenC8SpinFormU, ?_, ?_⟩
  · intro u hu
    rw [spinQ, quad_eq_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [hu k, mul_zero]
  · rw [sixteenC8SpinForm_rankU, rk_top, rk, sixteenC8SpinForm_cardSpinW,
      padicValNat.prime_pow]

theorem spinQ_invariant : QuadInvariant spinQ spinH :=
  fun _ hh x => spinQ_spinH hh x

theorem exists_plusQuad_spinH : ∃ Q : SpinW → ZMod 2, IsPlusQuadF2 Q ∧ QuadInvariant Q spinH :=
  ⟨spinQ, spinQ_isPlus, spinQ_invariant⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
