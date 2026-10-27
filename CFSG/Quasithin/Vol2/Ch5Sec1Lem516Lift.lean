module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QLine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL diagSL_conj)

@[expose] def sl2Ord3 (F : Type) [Field F] [CharP F 2] : SL(2, F) :=
  ⟨!![1, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    linear_combination -h2⟩

theorem coe_sl2Ord3 (F : Type) [Field F] [CharP F 2] :
    ((sl2Ord3 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, 0] := rfl

theorem coe_sl2Ord3_sq (F : Type) [Field F] [CharP F 2] :
    ((sl2Ord3 F * sl2Ord3 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Ord3, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2Ord3_mul_unipSL (F : Type) [Field F] [CharP F 2] :
    sl2Ord3 F * unipSL 1 = unipSL 1 * (sl2Ord3 F * sl2Ord3 F) := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Ord3, coe_unipSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2Ord3_sq_mul_unipSL (F : Type) [Field F] [CharP F 2] :
    sl2Ord3 F * sl2Ord3 F * unipSL 1 = unipSL 1 * sl2Ord3 F := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Ord3, coe_unipSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2Ord3_sum (F : Type) [Field F] [CharP F 2] (v : Fin 2 → F) :
    v + (sl2Ord3 F : Matrix (Fin 2) (Fin 2) F).mulVec v +
      ((sl2Ord3 F * sl2Ord3 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec v = 0 := by
  have h2 : ∀ a : F, a + a = 0 := CharTwo.add_self_eq_zero
  rw [coe_sl2Ord3_sq, coe_sl2Ord3]
  funext i
  fin_cases i <;>
    simp [dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;>
    linear_combination (h2 (v 0)) + h2 (v 1)

theorem fact516Lift (n : ℕ) : Fact516Lift n := by
  intro G _ _ L R S hnat hE hS x hxR hxS
  refine ⟨x, hxR, by rw [mul_inv_cancel]; exact Subgroup.one_mem _, ?_⟩
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord hS
  have hSL : S ≤ L := hS.1
  have : IsMulCommutative ↥R := hE.1
  have hsq : ∀ w : ↥R, w * w = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_mul, ← sq]
    exact hE.2 w w.2)
  let A : SL(2, F) →* MulAut ↥R := (autOn L R).subtype.comp ψ.symm.toMonoidHom
  have hA : ∀ g, A g = ((ψ.symm g : ↥(autOn L R)) : MulAut ↥R) := fun _ => rfl
  have hAY : ∀ (g : SL(2, F)) (w : ↥R), Multiplicative.toAdd (Y (A g w)) =
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w)) := by
    intro g w
    rw [hA, hc.intertwine, MulEquiv.apply_symm_apply]
  have hfixC : ∀ (g : SL(2, F)) (w : ↥R), (w : G) ∈ Subgroup.centralizer (L : Set G) →
      A g w = w := by
    intro g w hw
    obtain ⟨l, hlL, hla⟩ := mem_autOn_iff.mp (ψ.symm g).2
    apply Subtype.ext
    rw [hA, ← hla, conjAct_apply_coe, Subgroup.mem_centralizer_iff.mp hw l hlL,
      mul_inv_cancel_right]
  have hC : ∀ w : ↥R, Y w = 1 → (w : G) ∈ Subgroup.centralizer (L : Set G) :=
    fun w hw => (hc.ker w).mp hw
  let P : ↥R →* ↥R :=
    { toFun := fun w => w * A (sl2Ord3 F) w * A (sl2Ord3 F * sl2Ord3 F) w
      map_one' := by simp
      map_mul' := fun w w' => by
        simp only [map_mul (A (sl2Ord3 F)), map_mul (A (sl2Ord3 F * sl2Ord3 F))]
        ac_rfl }
  have hP : ∀ w, P w = w * A (sl2Ord3 F) w * A (sl2Ord3 F * sl2Ord3 F) w := fun _ => rfl
  have hPY : ∀ w, Y (P w) = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [hP, map_mul Y, map_mul Y, toAdd_mul, toAdd_mul, hAY, hAY, toAdd_one]
    exact sl2Ord3_sum F _
  have hPC : ∀ w : ↥R, (w : G) ∈ Subgroup.centralizer (L : Set G) → P w = w := by
    intro w hw
    rw [hP, hfixC _ w hw, hfixC _ w hw, hsq, one_mul]
  have hPP : ∀ w, P (P w) = P w := fun w => hPC _ (hC _ (hPY w))
  set u := A (unipSL 1) with hu
  have e1 : ∀ w, A (sl2Ord3 F) (u w) = u (A (sl2Ord3 F * sl2Ord3 F) w) := by
    intro w
    rw [hu, ← MulAut.mul_apply, ← map_mul, sl2Ord3_mul_unipSL,
      map_mul A (unipSL 1) (sl2Ord3 F * sl2Ord3 F), MulAut.mul_apply]
  have e2 : ∀ w, A (sl2Ord3 F * sl2Ord3 F) (u w) = u (A (sl2Ord3 F) w) := by
    intro w
    rw [hu, ← MulAut.mul_apply, ← map_mul, sl2Ord3_sq_mul_unipSL, map_mul A (unipSL 1) (sl2Ord3 F),
      MulAut.mul_apply]
  have hPu : ∀ w, P (u w) = u (P w) := by
    intro w
    rw [hP, hP, e1, e2, map_mul u, map_mul u]
    ac_rfl
  have hline : ∀ w : ↥R, (Multiplicative.toAdd (Y w)) 1 = 0 → u w = w := by
    intro w hw
    set k := w * (P w)⁻¹ with hk
    have hPk : P k = 1 := by rw [hk, map_mul, map_inv, hPP, mul_inv_cancel]
    have hYk : Y (u k * k⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hu, hAY, hk, map_mul, map_inv, hPY,
        inv_one, mul_one, toAdd_one, coe_unipSL]
      funext i
      fin_cases i <;> simp [dotProduct, Fin.sum_univ_two, hw]
    have hPuk : P (u k * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hPu, hPk, map_one, inv_one, one_mul]
    have huk : u k = k := by
      have h1 := hPC _ (hC _ hYk)
      rw [hPuk] at h1
      exact (mul_inv_eq_one.mp h1.symm)
    have hw' : w = k * P w := by rw [hk, inv_mul_cancel_right]
    rw [hw', map_mul, huk, hfixC _ _ (hC _ (hPY w))]
  have hall : ∀ (b : F) (w : ↥R), (Multiplicative.toAdd (Y w)) 1 = 0 →
      A (unipSL b) w = w := by
    intro b w hw
    by_cases hb : b = 0
    · rw [hb, Vol2.Ch10.SecA.unipSL_zero, map_one, MulAut.one_apply]
    obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' b
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hb (by rw [hμ, mul_zero])
    have hconj : unipSL b = diagSL hμ0 * unipSL 1 * (diagSL hμ0)⁻¹ := by
      rw [diagSL_conj, mul_one, hμ, sq]
    have hw' : (Multiplicative.toAdd (Y (A (diagSL hμ0)⁻¹ w))) 1 = 0 := by
      rw [hAY]
      have hinv : (((diagSL hμ0)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![μ⁻¹, 0; 0, μ] := by
        rw [Matrix.SpecialLinearGroup.coe_inv, coe_diagSL, Matrix.adjugate_fin_two_of]
        simp
      rw [hinv]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw]
    rw [hconj, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ← hu, hline _ hw',
      ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hx1 : (Multiplicative.toAdd (Y ⟨x, hxR⟩)) 1 = 0 :=
    (hc.snd_eq_zero_iff hSL ⟨x, hxR⟩).mpr hxS
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hLR := hc.le_normalizer
  have hsS : ((autHom hLR ⟨s, hSL hs⟩ : ↥(autOn L R)) : MulAut ↥R) ∈ autOn S R :=
    mem_autOn_iff.mpr ⟨⟨s, hLR (hSL hs)⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (hc.sylow _).mp hsS
  have hsb : autHom hLR ⟨s, hSL hs⟩ = ψ.symm (unipSL b) := by
    rw [← hb, MulEquiv.symm_apply_apply]
  have h1 := congrArg Subtype.val (hall b ⟨x, hxR⟩ hx1)
  rw [hA, ← hsb, autHom_apply_coe] at h1
  calc s * x = s * x * s⁻¹ * s := by group
    _ = x * s := by rw [h1]

end CFSG.Quasithin.H13
