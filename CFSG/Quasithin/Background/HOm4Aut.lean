module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutPGammaL

public section

namespace CFSG.Quasithin.H.Om4

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ABGLocalTools

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_eq_conj_map (α : MulAut (SpecialLinearGroup (Fin 2) K)) :
    ∃ (G : GL (Fin 2) K) (τ : K ≃+* K), ∀ b : SpecialLinearGroup (Fin 2) K,
      ((α b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (G : Matrix (Fin 2) (Fin 2) K) * (b : Matrix (Fin 2) (Fin 2) K).map τ *
          ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨x, hx⟩ := semilinearAction_surjective K (psl2MulAutOf α)
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective x.left
  refine ⟨G, x.right, fun b => ?_⟩
  have h1 : ProjectiveSpecialLinearGroup.toPGL (psl2MulAutOf α (QuotientGroup.mk' _ b)) =
      ProjectiveSpecialLinearGroup.toPGL (semilinearAction K x (QuotientGroup.mk' _ b)) := by
    rw [hx]
  have hdecomp : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  rw [psl2MulAutOf_mk, hdecomp, map_mul, semilinearAction_inl, semilinearAction_inr,
    MulAut.mul_apply, toPGL_pglAction, psl2FieldAut_toPGL] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    x.left * (pgl2FieldAut K) x.right (ProjGenLinGroup.mk (SpecialLinearGroup.toGL b)) *
      x.left⁻¹ at h1
  rw [pgl2FieldAut_apply, ← hG] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * pgl2RingEquiv x.right
      (QuotientGroup.mk' _ (SpecialLinearGroup.toGL b)) * (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [pgl2RingEquiv_mk] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * ProjGenLinGroup.mk
      (GeneralLinearGroup.map x.right.toRingHom (SpecialLinearGroup.toGL b)) *
        (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [← map_mul, ← map_inv, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hw
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hw'
  have hmap : ((GeneralLinearGroup.map x.right.toRingHom (SpecialLinearGroup.toGL b) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (b : Matrix (Fin 2) (Fin 2) K).map x.right :=
    rfl
  have hαb : ((SpecialLinearGroup.toGL (α b) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((α b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [hmap, hαb] at hw'
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdetb : (b : Matrix (Fin 2) (Fin 2) K).det = 1 := b.2
  have hdetαb : ((α b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    (α b).2
  have hdG : (G : Matrix (Fin 2) (Fin 2) K).det * ((G⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdτ : ((b : Matrix (Fin 2) (Fin 2) K).map x.right).det = 1 := by
    have : ((b : Matrix (Fin 2) (Fin 2) K).map x.right).det =
        x.right.toRingHom (b : Matrix (Fin 2) (Fin 2) K).det :=
      (RingHom.map_det x.right.toRingHom _).symm
    rw [this, hdetb, map_one]
  have hd := congrArg Matrix.det hw'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hdetαb, one_mul, Matrix.scalar_apply,
    Matrix.det_diagonal, Fin.prod_univ_two, hdτ, mul_one, hdG] at hd
  have hw1 : (w : K) = 1 := by
    have h3 : ((w : K) + 1) * ((w : K) + 1) = 0 := by linear_combination hd + ((w : K) + 1) * h2
    have h4 := mul_self_eq_zero.mp h3
    linear_combination h4 - h2
  rw [hw1, map_one, mul_one] at hw'
  exact hw'

omit [Finite K] in
theorem sl2_isSimple (h4 : 4 ≤ Nat.card K) : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

omit [Finite K] in
theorem sl2_commutator_eq_top (h4 : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)), (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K))⁆ =
      (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) := by
  have hs := sl2_isSimple h4
  rcases hs.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)),
      (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K))⁆ with h | h
  · exfalso
    set a : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp⟩
    set b : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp⟩
    have hab : a * b * a⁻¹ * b⁻¹ ∈ ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)),
        (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K))⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top (G := SpecialLinearGroup (Fin 2) K) b)
    rw [h, Subgroup.mem_bot] at hab
    have h1 : a * b = b * a := by
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hab, one_mul]
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    simp [a, b, Matrix.mul_apply, Fin.sum_univ_two] at h2
  · exact h

end CFSG.Quasithin.H.Om4
