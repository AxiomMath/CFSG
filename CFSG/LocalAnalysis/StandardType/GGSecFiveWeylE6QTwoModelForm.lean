module

public import CFSG.LocalAnalysis.StandardType.GGE6IsoOrbit
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e6ModelForm (x y : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  E6Dep.bil6 (E6Dep.coordF.mulVec x) (E6Dep.coordF.mulVec y)

theorem e6ModelForm_add_left (x x' y : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm (x + x') y = e6ModelForm x y + e6ModelForm x' y := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_add, dotProduct_add]

theorem e6ModelForm_add_right (x y y' : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm x (y + y') = e6ModelForm x y + e6ModelForm x y' := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_add, dotProduct_add]

theorem e6ModelForm_smul_left (c : ZMod 3) (x y : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm (c • x) y = c * e6ModelForm x y := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem e6ModelForm_smul_right (c : ZMod 3) (x y : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm x (c • y) = c * e6ModelForm x y := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem e6ModelForm_zero_right (x : Fin Tag.E6.rank → ZMod 3) : e6ModelForm x 0 = 0 := by
  simp [e6ModelForm, E6Dep.bil6]

theorem e6ModelForm_sub_left (x x' y : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm (x - x') y = e6ModelForm x y - e6ModelForm x' y := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_sub, sub_dotProduct]

theorem e6ModelForm_sub_right (x y y' : Fin Tag.E6.rank → ZMod 3) :
    e6ModelForm x (y - y') = e6ModelForm x y - e6ModelForm x y' := by
  simp [e6ModelForm, E6Dep.bil6, Matrix.mulVec_sub, dotProduct_sub]

@[expose] def e6ModelBaseTwo : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 1, 1, 1, 0]

@[expose] def e6ModelCol (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ((CartanMatrix.E 6 j i : ℤ) : ZMod 3)

theorem cartanE_six_symm (i j : Fin Tag.E6.rank) : CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartan_six_eq : Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6

private theorem e6ModelCol_diag (i : Fin Tag.E6.rank) : e6ModelCol i i = 2 := by
  unfold e6ModelCol
  fin_cases i <;> decide

private theorem e6ModelCol_ne_zero (i : Fin Tag.E6.rank) : e6ModelCol i ≠ 0 := by
  intro h
  have h2 : e6ModelCol i i = 0 := by simpa using congrFun h i
  rw [e6ModelCol_diag] at h2
  exact absurd h2 (by decide)

theorem adRefl_eq (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    TableBExc.E6Three.adRefl .E6 3 i x = x - x i • e6ModelCol i := by
  funext j
  simp only [TableBExc.E6Three.adRefl, e6ModelCol, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (Tag.cartan .E6 i j : ℤ) = CartanMatrix.E 6 i j from by rw [cartan_six_eq],
    cartanE_six_symm j i]

theorem adRefl_fixed_iff (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    TableBExc.E6Three.adRefl .E6 3 i x = x ↔ x i = 0 := by
  rw [adRefl_eq]
  constructor
  · intro h
    have h' : x i • e6ModelCol i = 0 := (sub_eq_self).mp h
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact h0
    · exact absurd h0 (e6ModelCol_ne_zero i)
  · intro h
    simp [h]

@[expose] def e6ModelO90Pred (x : Fin Tag.E6.rank → ZMod 3) : Prop :=
  NoOffRest.kDotP 3 x = 0 ∧ x ≠ 0 ∧ e6ModelForm x x = 2

instance : DecidablePred e6ModelO90Pred := fun x => by unfold e6ModelO90Pred; infer_instance

@[expose] def e6ModelO90 : Finset (Fin Tag.E6.rank → ZMod 3) :=
  Finset.univ.filter e6ModelO90Pred

theorem e6ModelO90_card : e6ModelO90.card = 90 := by
  decide +kernel

theorem e6ModelO90_fixed_card (i : Fin Tag.E6.rank) :
    (e6ModelO90.filter fun x => x i = 0).card = 30 := by
  revert i
  decide +kernel

theorem e6ModelBaseTwo_mem_hypE6 : e6ModelBaseTwo ∈ NoOffRest.hypE6 := by
  rw [NoOffRest.mem_hypE6]
  decide +kernel

theorem e6ModelO90_perp_baseTwo_card :
    (e6ModelO90.filter fun x => e6ModelForm e6ModelBaseTwo x = 0).card = 24 := by
  decide +kernel

theorem e6ModelBaseTwo_ne_zero : e6ModelBaseTwo ≠ 0 := by
  decide +kernel

theorem e6ModelForm_baseTwo : e6ModelForm e6ModelBaseTwo e6ModelBaseTwo = 2 := by
  decide +kernel

theorem e6ModelForm_col_col (i j : Fin Tag.E6.rank) :
    e6ModelForm (e6ModelCol i) (e6ModelCol j) = 2 * ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) := by
  revert i j
  decide +kernel

end CFSG.StandardType.E6QTwo

end
