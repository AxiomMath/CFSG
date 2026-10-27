module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2Aut
import CFSG.Dihedral.GorensteinWalter.PGL2CharTwo

public section

namespace CFSG.Quasithin.L21521E

open CFSG.PSL2Table CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Quasithin.L21521
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem toPGL_surjective_of_charTwo [Finite K] [CharP K 2] :
    Function.Surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL(2, K)) :=
  CFSG.GorensteinWalter.toPGL_surjective_of_charTwo' K

theorem mem_borel_of_conj_unip_mem {y : PSL(2, K)}
    (h : y * mk (unip 1) * y⁻¹ ∈ unipotent K) : y ∈ borel K := by
  obtain ⟨M, rfl⟩ := exists_mk_eq y
  rw [mk_conj, mk_mem_unipotent_iff, conj_unip_apply_10] at h
  rw [mk_mem_borel_iff, mem_borelSL_iff]
  have h1 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 = 0 := by
    have := neg_eq_zero.mp h.1
    simpa using this
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h1

theorem exists_twist_of_unipotent_stable [Finite K] [CharP K 2] (β : MulAut PSL(2, K))
    (hβ : ∀ x ∈ unipotent K, β x ∈ unipotent K) :
    ∃ (t : K) (σ : K ≃+* K), t ≠ 0 ∧ ∀ s : K, β (mk (unip s)) = mk (unip (t * σ s)) := by
  obtain ⟨γ, rfl⟩ := (semilinearEquivAut K).surjective β
  have hx : semilinearEquivAut K γ = pglAction K γ.left * psl2FieldAut K γ.right := by
    change semilinearAction K γ = _
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  obtain ⟨y, hy⟩ := toPGL_surjective_of_charTwo (K := K) γ.left
  have hpgl : pglAction K γ.left = MulAut.conj y := by rw [← hy, pglAction_toPGL]
  rw [hx, hpgl] at hβ ⊢
  have h1 := hβ _ (mk_unip_mem_unipotent 1)
  rw [MulAut.mul_apply, psl2FieldAut_mk_unip', map_one, MulAut.conj_apply] at h1
  obtain ⟨M, hM, rfl⟩ := mem_borel_of_conj_unip_mem h1
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := (mem_borelSL_iff M).mp hM
  have hdet := det_entries M
  rw [hM10, mul_zero, sub_zero] at hdet
  have h0 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨(M : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2, γ.right, pow_ne_zero 2 h0, fun s => ?_⟩
  rw [MulAut.mul_apply, psl2FieldAut_mk_unip', MulAut.conj_apply, mk_conj,
    conj_unip_of_borel hM10]

end CFSG.Quasithin.L21521E
