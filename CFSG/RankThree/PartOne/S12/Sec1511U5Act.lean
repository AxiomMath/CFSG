module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAction

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5M

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev Gam : Type :=
  primeFormUnitary h (idGram K 5) ⋊[primeFormFieldU h
    (isPrimeFormGram_idGram (K := K) (n := 5))] (K ≃+* K)

variable {h}

@[expose] noncomputable def act (g : Gam h) (v : Fin 5 → K) : Fin 5 → K :=
  ((g.left : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ (fun i => g.right (v i))

theorem act_mul (g g' : Gam h) (v : Fin 5 → K) : act (g * g') v = act g (act g' v) := by
  simp only [act, SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
    Units.val_mul, coe_primeFormFieldU, coe_glAut]
  rw [← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem act_one (v : Fin 5 → K) : act (1 : Gam h) v = v := by
  ext i
  simp [act]

theorem act_add (g : Gam h) (v w : Fin 5 → K) : act g (v + w) = act g v + act g w := by
  unfold act
  rw [← Matrix.mulVec_add]
  congr 1
  ext i
  simp

theorem act_smul (g : Gam h) (c : K) (v : Fin 5 → K) : act g (c • v) = g.right c • act g v := by
  unfold act
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

@[expose] noncomputable def actL (g : Gam h) :
    (Fin 5 → K) →ₛₗ[(g.right : K →+* K)] (Fin 5 → K) where
  toFun := act g
  map_add' := act_add g
  map_smul' := act_smul g

theorem actL_apply (g : Gam h) (v : Fin 5 → K) : actL g v = act g v := rfl

theorem act_inv_act (g : Gam h) (v : Fin 5 → K) : act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_injective (g : Gam h) : Function.Injective (act g) := fun v w hvw => by
  have := congrArg (act g⁻¹) hvw
  rwa [act_inv_act, act_inv_act] at this

theorem toLinU_apply_vec (A : primeFormUnitary h (idGram K 5)) (v : Fin 5 → K) :
    ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) v =
      ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := by
  change Matrix.toLin' ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) v = _
  rw [Matrix.toLin'_apply]

theorem scalar_mulVec (c : Kˣ) (w : Fin 5 → K) :
    ((GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w =
      (c : K) • w := by
  ext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem act_ker (hq : 3 < 2 ^ f) (g : Gam h)
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g = 1) :
    g.right = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ ∀ v, act g v = c • v := by
  obtain ⟨hr, c, -, hc⟩ := (primeFormPsi_eq_one_iff' (by norm_num) hq g).1 hg
  refine ⟨hr, c, c.ne_zero, fun v => ?_⟩
  have h1 : (fun i => g.right (v i)) = v := by
    rw [hr]
    rfl
  unfold act
  rw [h1, hc]
  exact scalar_mulVec c v

theorem conj_rel (g : Gam h) (A : primeFormUnitary h (idGram K 5)) (v : Fin 5 → K) :
    ((idUAction h 5 g A : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K).val *ᵥ act g v =
      act g (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) := by
  obtain ⟨M, σ⟩ := g
  rw [idUAction_mk]
  have h1 : (fun i => σ ((((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) i)) =
      (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ) *ᵥ (fun i => σ (v i)) := by
    ext i
    exact RingHom.map_mulVec (σ : K →+* K) _ _ i
  simp only [act, Subgroup.coe_mul, Units.val_mul, coe_primeFormFieldU, coe_glAut, Subgroup.coe_inv,
    Matrix.mulVec_mulVec, h1]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp

end U5M

end Sec1511

end CFSG.RankThree.PartOne
