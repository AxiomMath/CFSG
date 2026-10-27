module

public import CFSG.Quasithin.Background.F918T0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

section Wedge

variable {d : ℕ}

private theorem vecMulVec_add_mem_altMat (u v : Fin d → ZMod 2) :
    Matrix.vecMulVec u v + Matrix.vecMulVec v u ∈ altMat d := by
  refine ⟨by rw [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
    add_comm], fun i => ?_⟩
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  rw [mul_comm (v i)]
  exact CharTwo.add_self_eq_zero _

private noncomputable def wedgeAlt (d : ℕ) :
    (Fin d → ZMod 2) [⋀^Fin 2]→ₗ[ZMod 2] ↥(altMat d) where
  toFun v := ⟨Matrix.vecMulVec (v 0) (v 1) + Matrix.vecMulVec (v 1) (v 0),
    vecMulVec_add_mem_altMat _ _⟩
  map_update_add' v i x y := by
    apply Subtype.ext
    fin_cases i <;> simp [Matrix.vecMulVec_add, Matrix.add_vecMulVec] <;> abel
  map_update_smul' v i c x := by
    apply Subtype.ext
    fin_cases i <;> simp [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_add]
  map_eq_zero_of_eq' v i j hv hij := by
    apply Subtype.ext
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    ext k l
    simp only [h01, ZeroMemClass.coe_zero, Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _

private noncomputable def wedgeLin (d : ℕ) :
    ⋀[ZMod 2]^2 (Fin d → ZMod 2) →ₗ[ZMod 2] ↥(altMat d) :=
  exteriorPower.alternatingMapLinearEquiv (wedgeAlt d)

private theorem wedgeLin_ιMulti (v : Fin 2 → Fin d → ZMod 2) :
    (wedgeLin d (exteriorPower.ιMulti (ZMod 2) 2 v) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      Matrix.vecMulVec (v 0) (v 1) + Matrix.vecMulVec (v 1) (v 0) := by
  rw [wedgeLin, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private theorem wedgeLin_injective : Function.Injective (wedgeLin d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply ((Pi.basisFun (ZMod 2) (Fin d)).exteriorPower 2).ext_elem
  intro s
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply]
  have key : exteriorPower.ιMultiDual (ZMod 2) 2 (Pi.basisFun (ZMod 2) (Fin d)) s =
      (Matrix.entryLinearMap (ZMod 2) (ZMod 2) (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1)) ∘ₗ (altMat d).subtype ∘ₗ wedgeLin d := by
    ext v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.ιMultiDual_apply_ιMulti,
      Matrix.det_fin_two, Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
      LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, wedgeLin_ιMulti,
      Matrix.entryLinearMap_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
    rw [CharTwo.sub_eq_add]
    ring
  rw [key]
  simp [hx]

private theorem wedgeLin_surjective : Function.Surjective (wedgeLin d) := by
  intro B
  refine ⟨∑ i : Fin d, exteriorPower.ιMulti (ZMod 2) 2
    ![Pi.single i 1, fun j => if i < j then (B : Matrix (Fin d) (Fin d) (ZMod 2)) i j else 0], ?_⟩
  apply Subtype.ext
  obtain ⟨hB1, hB2⟩ := B.2
  ext k l
  simp only [map_sum, Submodule.coe_sum, wedgeLin_ιMulti, Matrix.sum_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_apply, mul_ite,
    ite_mul, one_mul, zero_mul, mul_zero, mul_one, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, h.asymm]
  · simp [hB2]
  · have hsym : (B : Matrix (Fin d) (Fin d) (ZMod 2)) l k =
        (B : Matrix (Fin d) (Fin d) (ZMod 2)) k l := by
      conv_rhs => rw [← hB1]
      rfl
    simp [h, h.asymm, hsym]

private theorem wedgeLin_map (M : Matrix (Fin d) (Fin d) (ZMod 2))
    (x : ⋀[ZMod 2]^2 (Fin d → ZMod 2)) :
    (wedgeLin d (exteriorPower.map 2 (Matrix.toLin' M) x) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      M * (wedgeLin d x : Matrix (Fin d) (Fin d) (ZMod 2)) * Mᵀ := by
  have hx : x ∈ Submodule.span (ZMod 2) (Set.range (exteriorPower.ιMulti (ZMod 2) 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [exteriorPower.map_apply_ιMulti, wedgeLin_ιMulti, wedgeLin_ιMulti]
    simp only [Function.comp_apply, Matrix.toLin'_apply, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  | zero => simp
  | add y z _ _ hy hz =>
    simp only [map_add, Submodule.coe_add, hy, hz, Matrix.mul_add, Matrix.add_mul]
  | smul c y _ hy =>
    simp only [map_smul, Submodule.coe_smul, hy, Matrix.mul_smul, Matrix.smul_mul]

end Wedge

theorem extSq5_equiv_alt :
    ∃ Ψ : Multiplicative ↥(⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) ≃* Multiplicative ↥(altMat 5),
      ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (x : Multiplicative ↥(⋀[ZMod 2]^2 (Fin 5 → ZMod 2))),
        Ψ (extSqAct (ZMod 2) 5 γ x) = altMulAct γ (Ψ x) := by
  refine ⟨AddEquiv.toMultiplicative (LinearEquiv.ofBijective (wedgeLin 5)
    ⟨wedgeLin_injective, wedgeLin_surjective⟩).toAddEquiv, fun γ x => ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact wedgeLin_map (mat γ) (Multiplicative.toAdd x)

end CFSG.Quasithin
