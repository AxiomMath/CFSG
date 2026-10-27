module

public import CFSG.Quasithin.MS93.ML3Basic

public section

namespace CFSG.Quasithin.MS93

open Matrix

variable {F : Type} [Field F]

theorem rootElt_mulVec {i j : Fin 3} (h : i ≠ j) (c : F) (x : Fin 3 → F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + Pi.single i (c * x j) := by
  rw [coe_rootElt h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

section CharTwo

variable [CharP F 2]

@[expose] def swap01 : SL3 F :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

theorem coe_swap01 :
    ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] :=
  rfl

theorem swap01_mul_self : (swap01 : SL3 F) * swap01 = 1 := by
  apply Subtype.ext
  change ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((swap01 : SL3 F) : Matrix _ _ F) = 1
  rw [coe_swap01]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap01_inv : (swap01 : SL3 F)⁻¹ = swap01 :=
  inv_eq_of_mul_eq_one_right swap01_mul_self

private theorem swap01_conj_aux (i j i' j' : Fin 3) (hij : i ≠ j) (hij' : i' ≠ j') (c : F)
    (h : ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (1 + single i j c) =
      (1 + single i' j' c) * ((swap01 : SL3 F) : Matrix _ _ F)) :
    swap01 * rootElt i j c * swap01⁻¹ = rootElt i' j' c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt i j c : SL3 F) :
      Matrix _ _ F) = ((rootElt i' j' c : SL3 F) : Matrix _ _ F) * ((swap01 : SL3 F) :
      Matrix _ _ F)
  rw [coe_rootElt hij, coe_rootElt hij']
  exact h

theorem swap01_conj_rootElt02 (c : F) : swap01 * rootElt 0 2 c * swap01⁻¹ = rootElt 1 2 c := by
  refine swap01_conj_aux 0 2 1 2 (by decide) (by decide) c ?_
  rw [coe_swap01]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem swap01_conj_rootElt12 (c : F) : swap01 * rootElt 1 2 c * swap01⁻¹ = rootElt 0 2 c := by
  refine swap01_conj_aux 1 2 0 2 (by decide) (by decide) c ?_
  rw [coe_swap01]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem swap01_mulVec (x : Fin 3 → F) :
    ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 1, x 0, x 2] := by
  rw [coe_swap01]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rootElt_mul_self (i j : Fin 3) (c : F) : rootElt i j c * rootElt i j c = 1 := by
  rw [← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero]

end CharTwo

section Comm

variable {V : Type*} [CommGroup V] (ρ : SL3 F →* MulAut V)

@[expose] def dc (g : SL3 F) (v : V) : V := ρ g v * v⁻¹

theorem dc_mul_right (g : SL3 F) (v w : V) : dc ρ g (v * w) = dc ρ g v * dc ρ g w := by
  simp only [dc, map_mul, mul_inv]
  ac_rfl

theorem dc_one_left (v : V) : dc ρ 1 v = 1 := by
  simp [dc]

theorem dc_eq_one_iff (g : SL3 F) (v : V) : dc ρ g v = 1 ↔ ρ g v = v := by
  rw [dc, mul_inv_eq_one]

theorem act_eq_mul_dc (g : SL3 F) (v : V) : ρ g v = v * dc ρ g v := by
  rw [dc, mul_comm, inv_mul_cancel_right]

theorem dc_mul (g h : SL3 F) (v : V) :
    dc ρ (g * h) v = dc ρ g (dc ρ h v) * dc ρ g v * dc ρ h v := by
  simp only [dc, map_mul, MulAut.mul_apply, map_inv, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem dc_conj (g h : SL3 F) (v : V) :
    dc ρ (h * g * h⁻¹) v = ρ h (dc ρ g (ρ h⁻¹ v)) := by
  have hh : ρ h (ρ h⁻¹ v) = v := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have e1 : ρ (h * g * h⁻¹) v = ρ h (ρ g (ρ h⁻¹ v)) := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  rw [dc, dc, e1, map_mul (ρ h), map_inv (ρ h), hh]

theorem dc_dc_comm {g h : SL3 F} (hgh : g * h = h * g) (v : V) :
    dc ρ g (dc ρ h v) = dc ρ h (dc ρ g v) := by
  have e1 := dc_mul ρ g h v
  have e2 := dc_mul ρ h g v
  rw [hgh] at e1
  rw [e1] at e2
  have : dc ρ g (dc ρ h v) * (dc ρ g v * dc ρ h v) = dc ρ h (dc ρ g v) * (dc ρ g v * dc ρ h v) := by
    calc _ = dc ρ g (dc ρ h v) * dc ρ g v * dc ρ h v := by rw [mul_assoc]
      _ = dc ρ h (dc ρ g v) * dc ρ h v * dc ρ g v := e2
      _ = _ := by rw [mul_assoc, mul_comm (dc ρ h v)]
  exact mul_right_cancel this

theorem dc_dc_self (hV : ∀ v : V, v ^ 2 = 1) {g : SL3 F} (hg : g * g = 1) (v : V) :
    dc ρ g (dc ρ g v) = 1 := by
  have h2 : ρ g (ρ g v) = v := by
    rw [← MulAut.mul_apply, ← map_mul, hg, map_one, MulAut.one_apply]
  have hinv : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV w)
  simp only [dc, map_mul, h2, hinv]
  rw [show v * ρ g v * (ρ g v * v) = (v * ρ g v) ^ 2 by rw [sq]; ac_rfl, hV]

end Comm

section Ext

variable {V : Type*} [CommGroup V] (ρ : SL3 F →* MulAut V)

structure NatNatExt where
  ι : Multiplicative (Fin 3 → F) →* V
  β : V →* Multiplicative (Fin 3 → F)
  ι_injective : Function.Injective ι
  β_surjective : Function.Surjective β
  ker_β : β.ker = ι.range
  ι_equiv : ∀ (g : SL3 F) (x : Fin 3 → F),
    ρ g (ι (Multiplicative.ofAdd x)) =
      ι (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x))
  β_equiv : ∀ (g : SL3 F) (v : V),
    Multiplicative.toAdd (β (ρ g v)) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v)

variable {ρ}

namespace NatNatExt

variable (E : NatNatExt ρ)

theorem toAdd_β_dc (g : SL3 F) (v : V) :
    Multiplicative.toAdd (E.β (dc ρ g v)) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (E.β v) -
        Multiplicative.toAdd (E.β v) := by
  rw [dc, map_mul, map_inv, toAdd_mul, toAdd_inv, E.β_equiv, sub_eq_add_neg]

theorem dc_ι (g : SL3 F) (x : Fin 3 → F) :
    dc ρ g (E.ι (Multiplicative.ofAdd x)) =
      E.ι (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x)) := by
  rw [dc, E.ι_equiv, ← map_inv, ← map_mul, sub_eq_add_neg, ofAdd_add, ofAdd_neg]

theorem mem_range_ι_iff (v : V) : v ∈ E.ι.range ↔ E.β v = 1 := by
  rw [← E.ker_β, MonoidHom.mem_ker]

end NatNatExt

end Ext

end CFSG.Quasithin.MS93
