module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

section Helpers

private theorem irreducible_X_pow_three_sub_C {K : Type*} [Field K] {c : K}
    (hc : ∀ d : K, d ^ 3 ≠ c) : Irreducible (X ^ 3 - C c : K[X]) := by
  have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
    fun μ hμ => ?_
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hμ
  exact hc μ hμ

private theorem natDegree_dvd_finrank_of_aeval_eq_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {f : K[X]} (hf : Irreducible f) (T : Module.End K M)
    (hT : aeval T f = 0) : f.natDegree ∣ Module.finrank K M := by
  haveI := Fact.mk hf
  let φ : AdjoinRoot f →ₐ[K] Module.End K M :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval T) fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hT, mul_zero]
  letI : Module (AdjoinRoot f) M := Module.compHom M φ.toRingHom
  have : IsScalarTower K (AdjoinRoot f) M := ⟨fun c a m => by
    change φ (c • a) m = c • φ a m
    rw [map_smul]
    rfl⟩
  have h1 : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  rw [← Module.finrank_mul_finrank K (AdjoinRoot f) M, h1]
  exact dvd_mul_right _ _

private theorem coe_aeval_restrict_apply {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (T : Module.End K M) {W : Submodule K M} (hW : ∀ v ∈ W, T v ∈ W) (p : K[X]) (w : W) :
    ((aeval (T.restrict hW) p w : W) : M) = aeval T p w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      Submodule.coe_smul, LinearMap.restrict_apply]

end Helpers

section Invariant

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem three_dvd_finrank_of_invariant {M : Module.End K V} {l : K} (hl : ∀ c : K, c ^ 3 ≠ l)
    (hM : M ^ 3 = algebraMap K (Module.End K V) l) (W : Submodule K V)
    (hW : ∀ w ∈ W, M w ∈ W) : 3 ∣ Module.finrank K W := by
  have hirr : Irreducible (X ^ 3 - C l : K[X]) := irreducible_X_pow_three_sub_C hl
  have hMpoly : aeval M (X ^ 3 - C l : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hM, sub_self]
  have hT : aeval (M.restrict hW) (X ^ 3 - C l : K[X]) = 0 := by
    ext w
    rw [coe_aeval_restrict_apply, hMpoly]
    simp
  have hdvd := natDegree_dvd_finrank_of_aeval_eq_zero hirr (M.restrict hW) hT
  have hdeg : (X ^ 3 - C l : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  rwa [hdeg] at hdvd

end Invariant

section Matrices

variable {K : Type} [Field K]

theorem false_of_cyclic_partner {M g X : GL (Fin 6) K} {l ζ : Kˣ} (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hM : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hg3 : g ^ 3 = 1) (hgM : g * M = M * g)
    (hζ : IsPrimitiveRoot ζ 3)
    (hXg : X * g = GeneralLinearGroup.scalar (Fin 6) ζ * (g * X)) : False := by
  classical
  let gL : Module.End K (Fin 6 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) (g : Matrix (Fin 6) (Fin 6) K)
  let ML : Module.End K (Fin 6 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) (M : Matrix (Fin 6) (Fin 6) K)
  let XL : Module.End K (Fin 6 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) (X : Matrix (Fin 6) (Fin 6) K)
  have hscalar : ∀ c : K, (Matrix.scalar (Fin 6) c : Matrix (Fin 6) (Fin 6) K) =
      algebraMap K (Matrix (Fin 6) (Fin 6) K) c := by
    intro c
    rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    congr 1
  have hζ3K : (ζ : K) ^ 3 = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hζ.pow_eq_one
    simpa using h
  have hζne1K : (ζ : K) ≠ 1 := fun h => hζ.ne_one (by norm_num) (Units.ext h)
  have hζne0K : (ζ : K) ≠ 0 := ζ.ne_zero
  have hmul : (ζ : K) * (ζ : K) ^ 2 = 1 := by
    rw [← pow_succ' (ζ : K) 2]
    exact hζ3K
  have hζinv : (ζ : K)⁻¹ = (ζ : K) ^ 2 := (mul_eq_one_iff_inv_eq₀ hζne0K).mp hmul
  have hζinv_mul_ζ2 : (ζ : K)⁻¹ * (ζ : K) ^ 2 = (ζ : K) := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hζne0K, one_mul]
  have hζ2ne1 : (ζ : K) ^ 2 ≠ 1 := by
    intro h
    apply hζne1K
    calc (ζ : K) = (ζ : K) * 1 := (mul_one _).symm
      _ = (ζ : K) * (ζ : K) ^ 2 := by rw [← h]
      _ = (ζ : K) ^ (2 + 1) := (pow_succ' (ζ : K) 2).symm
      _ = 1 := hζ3K
  have hζsub : (ζ : K) - (ζ : K) ^ 2 ≠ 0 := by
    have h : (ζ : K) - (ζ : K) ^ 2 = (ζ : K) * (1 - (ζ : K)) := by ring
    rw [h]
    exact mul_ne_zero hζne0K (sub_ne_zero.mpr (Ne.symm hζne1K))
  have hsum : (ζ : K) ^ 2 + (ζ : K) + 1 = 0 := by
    have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + (ζ : K) + 1) = 0 := by
      have h2 : ((ζ : K) - 1) * ((ζ : K) ^ 2 + (ζ : K) + 1) = (ζ : K) ^ 3 - 1 := by ring
      rw [h2, hζ3K, sub_self]
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hζne1K
    · exact h2
  have hM_lin : ML ^ 3 = algebraMap K (Module.End K (Fin 6 → K)) (l : K) := by
    have hmat : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 =
        algebraMap K (Matrix (Fin 6) (Fin 6) K) (l : K) := by
      rw [← Units.val_pow_eq_pow_val, hM, GeneralLinearGroup.coe_scalar]
      exact hscalar (l : K)
    have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) hmat
    simpa [ML] using this
  have hg3L : gL ^ 3 = 1 := by
    have hmat : (g : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
    have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) hmat
    simpa [gL] using this
  have hgML : gL * ML = ML * gL := by
    have hmat : (g : Matrix (Fin 6) (Fin 6) K) * (M : Matrix (Fin 6) (Fin 6) K) =
        (M : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) := by
      rw [← Units.val_mul, hgM, Units.val_mul]
    have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) hmat
    simpa [gL, ML] using this
  have hXgL : XL * gL =
      algebraMap K (Module.End K (Fin 6 → K)) (ζ : K) * (gL * XL) := by
    have hmat : (X : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) =
        algebraMap K (Matrix (Fin 6) (Fin 6) K) (ζ : K) *
          ((g : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K)) := by
      rw [← Units.val_mul, hXg, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mul]
      rw [hscalar (ζ : K)]
    have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)) hmat
    simpa [gL, ML, XL] using this
  have heig : ∀ c : K,
      gL.eigenspace c = LinearMap.ker (aeval gL (Polynomial.X - Polynomial.C c)) := by
    intro c
    have h : aeval gL (Polynomial.X - Polynomial.C c) = gL - c • 1 := by
      rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [Module.End.eigenspace_def, h]
  have hgML_apply : ∀ v : Fin 6 → K, gL (ML v) = ML (gL v) := fun v => by
    rw [← Module.End.mul_apply, hgML, Module.End.mul_apply]
  have h3V1 : 3 ∣ Module.finrank K (gL.eigenspace (1 : K)) := by
    refine three_dvd_finrank_of_invariant (M := ML) (l := (l : K)) ?_ hM_lin
      (gL.eigenspace (1 : K)) ?_
    · intro c hc
      by_cases hc0 : c = 0
      · subst hc0
        rw [zero_pow (by norm_num)] at hc
        exact l.ne_zero hc.symm
      · exact hl (Units.mk0 c hc0)
          (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc))
    · intro w hw
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [hgML_apply, hw, map_smul]
  have h3Vz : 3 ∣ Module.finrank K (gL.eigenspace (ζ : K)) := by
    refine three_dvd_finrank_of_invariant (M := ML) (l := (l : K)) ?_ hM_lin
      (gL.eigenspace (ζ : K)) ?_
    · intro c hc
      by_cases hc0 : c = 0
      · subst hc0
        rw [zero_pow (by norm_num)] at hc
        exact l.ne_zero hc.symm
      · exact hl (Units.mk0 c hc0)
          (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc))
    · intro w hw
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [hgML_apply, hw, map_smul]
  have h3Vz2 : 3 ∣ Module.finrank K (gL.eigenspace ((ζ : K) ^ 2)) := by
    refine three_dvd_finrank_of_invariant (M := ML) (l := (l : K)) ?_ hM_lin
      (gL.eigenspace ((ζ : K) ^ 2)) ?_
    · intro c hc
      by_cases hc0 : c = 0
      · subst hc0
        rw [zero_pow (by norm_num)] at hc
        exact l.ne_zero hc.symm
      · exact hl (Units.mk0 c hc0)
          (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc))
    · intro w hw
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [hgML_apply, hw, map_smul]
  have hcop1 : IsCoprime (Polynomial.X - Polynomial.C (1 : K))
      (Polynomial.X - Polynomial.C (ζ : K)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hζne1K)))
  have hcop2 : IsCoprime (Polynomial.X - Polynomial.C (1 : K))
      (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hζ2ne1)))
  have hcop3 : IsCoprime (Polynomial.X - Polynomial.C (ζ : K))
      (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr hζsub)
  have hcop12 : IsCoprime ((Polynomial.X - Polynomial.C (1 : K)) *
      (Polynomial.X - Polynomial.C (ζ : K))) (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)) :=
    IsCoprime.mul_left hcop2 hcop3
  have hpoly : ((Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C (ζ : K))) *
      (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)) = Polynomial.X ^ 3 - Polynomial.C (1 : K) := by
    have h : ((Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C (ζ : K))) *
        (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)) =
        Polynomial.X ^ 3 - Polynomial.C (1 + (ζ : K) + (ζ : K) ^ 2) * Polynomial.X ^ 2 +
          Polynomial.C ((ζ : K) + (ζ : K) ^ 2 + (ζ : K) ^ 3) * Polynomial.X -
          Polynomial.C ((ζ : K) ^ 3) := by
      simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_1]
      ring
    rw [h]
    have h1 : 1 + (ζ : K) + (ζ : K) ^ 2 = 0 := by linear_combination hsum
    have h2 : (ζ : K) + (ζ : K) ^ 2 + (ζ : K) ^ 3 = 0 := by
      linear_combination hsum + hζ3K
    rw [h1, h2, hζ3K]
    simp
  have hsup1 : gL.eigenspace (1 : K) ⊔ gL.eigenspace (ζ : K) =
      LinearMap.ker (aeval gL ((Polynomial.X - Polynomial.C (1 : K)) *
        (Polynomial.X - Polynomial.C (ζ : K)))) := by
    rw [heig (1 : K), heig (ζ : K)]
    exact Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime gL hcop1
  have hsup2 : (gL.eigenspace (1 : K) ⊔ gL.eigenspace (ζ : K)) ⊔
      gL.eigenspace ((ζ : K) ^ 2) = LinearMap.ker (aeval gL
        (((Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C (ζ : K))) *
          (Polynomial.X - Polynomial.C ((ζ : K) ^ 2)))) := by
    rw [hsup1, heig ((ζ : K) ^ 2)]
    exact Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime gL hcop12
  have hker : aeval gL (Polynomial.X ^ 3 - Polynomial.C (1 : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hg3L]
    simp
  have htop : (gL.eigenspace (1 : K) ⊔ gL.eigenspace (ζ : K)) ⊔
      gL.eigenspace ((ζ : K) ^ 2) = ⊤ := by
    rw [hsup2, hpoly, hker, LinearMap.ker_zero]
  have hdisj1 : Disjoint (gL.eigenspace (1 : K)) (gL.eigenspace (ζ : K)) := by
    rw [heig (1 : K), heig (ζ : K)]
    exact Polynomial.disjoint_ker_aeval_of_isCoprime gL hcop1
  have hdisj2 : Disjoint (gL.eigenspace (1 : K) ⊔ gL.eigenspace (ζ : K))
      (gL.eigenspace ((ζ : K) ^ 2)) := by
    rw [hsup1, heig ((ζ : K) ^ 2)]
    exact Polynomial.disjoint_ker_aeval_of_isCoprime gL hcop12
  have hdim1 := Submodule.finrank_sup_add_finrank_inf_eq
    (gL.eigenspace (1 : K)) (gL.eigenspace (ζ : K))
  rw [hdisj1.eq_bot, finrank_bot, add_zero] at hdim1
  have hdim2 := Submodule.finrank_sup_add_finrank_inf_eq
    (gL.eigenspace (1 : K) ⊔ gL.eigenspace (ζ : K)) (gL.eigenspace ((ζ : K) ^ 2))
  rw [hdisj2.eq_bot, finrank_bot, add_zero] at hdim2
  have hfin : Module.finrank K (Fin 6 → K) =
      (Module.finrank K (gL.eigenspace (1 : K)) + Module.finrank K (gL.eigenspace (ζ : K))) +
        Module.finrank K (gL.eigenspace ((ζ : K) ^ 2)) := by
    rw [← finrank_top (R := K) (M := Fin 6 → K), ← htop, hdim2, hdim1]
  have hXgL_apply : ∀ v : Fin 6 → K, XL (gL v) = (ζ : K) • gL (XL v) := by
    intro v
    have h := congrArg (fun f : Module.End K (Fin 6 → K) => f v) hXgL
    simpa [Module.End.mul_apply, Module.algebraMap_end_apply] using h
  have hgL_XL : ∀ v : Fin 6 → K, gL (XL v) = (ζ : K)⁻¹ • XL (gL v) := by
    intro v
    rw [hXgL_apply v, smul_smul, inv_mul_cancel₀ hζne0K, one_smul]
  have hXmap : ∀ c : K, ∀ v ∈ gL.eigenspace c,
      XL v ∈ gL.eigenspace ((ζ : K)⁻¹ * c) := by
    intro c v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hgL_XL v, hv, map_smul, smul_smul]
  have hXinj : Function.Injective XL := by
    have h := Matrix.mulVec_injective_of_isUnit (A := (X : Matrix (Fin 6) (Fin 6) K)) X.isUnit
    intro a b hab
    exact h (by simpa [XL, Matrix.toLin'_apply', Matrix.mulVecLin_apply] using hab)
  have hXV1 : ∀ v ∈ gL.eigenspace (1 : K), XL v ∈ gL.eigenspace ((ζ : K) ^ 2) := by
    intro v hv
    have h := hXmap (1 : K) v hv
    rwa [show (ζ : K)⁻¹ * 1 = (ζ : K) ^ 2 from by rw [hζinv, mul_one]] at h
  have hle1 : Module.finrank K (gL.eigenspace (1 : K)) ≤
      Module.finrank K (gL.eigenspace ((ζ : K) ^ 2)) := by
    apply LinearMap.finrank_le_finrank_of_injective (f := XL.restrict hXV1)
    intro a b hab
    exact Subtype.ext (hXinj (by simpa [LinearMap.restrict_apply] using congrArg Subtype.val hab))
  have hXV2 : ∀ v ∈ gL.eigenspace ((ζ : K) ^ 2), XL v ∈ gL.eigenspace (ζ : K) := by
    intro v hv
    have h := hXmap ((ζ : K) ^ 2) v hv
    rwa [hζinv_mul_ζ2] at h
  have hle2 : Module.finrank K (gL.eigenspace ((ζ : K) ^ 2)) ≤
      Module.finrank K (gL.eigenspace (ζ : K)) := by
    apply LinearMap.finrank_le_finrank_of_injective (f := XL.restrict hXV2)
    intro a b hab
    exact Subtype.ext (hXinj (by simpa [LinearMap.restrict_apply] using congrArg Subtype.val hab))
  have hXV3 : ∀ v ∈ gL.eigenspace (ζ : K), XL v ∈ gL.eigenspace (1 : K) := by
    intro v hv
    have h := hXmap (ζ : K) v hv
    rwa [show (ζ : K)⁻¹ * (ζ : K) = 1 from inv_mul_cancel₀ hζne0K] at h
  have hle3 : Module.finrank K (gL.eigenspace (ζ : K)) ≤
      Module.finrank K (gL.eigenspace (1 : K)) := by
    apply LinearMap.finrank_le_finrank_of_injective (f := XL.restrict hXV3)
    intro a b hab
    exact Subtype.ext (hXinj (by simpa [LinearMap.restrict_apply] using congrArg Subtype.val hab))
  have hd1 : Module.finrank K (gL.eigenspace ((ζ : K) ^ 2)) =
      Module.finrank K (gL.eigenspace (1 : K)) :=
    le_antisymm (le_trans hle2 hle3) hle1
  have hd2 : Module.finrank K (gL.eigenspace (ζ : K)) =
      Module.finrank K (gL.eigenspace (1 : K)) :=
    le_antisymm hle3 (le_trans hle1 hle2)
  have hV6 : Module.finrank K (Fin 6 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have h6 : Module.finrank K (Fin 6 → K) = 3 * Module.finrank K (gL.eigenspace (1 : K)) := by
    rw [hfin, hd1, hd2]
    ring
  rw [hV6] at h6
  obtain ⟨k, hk⟩ := h3V1
  rw [hk] at h6
  omega

end Matrices

end CFSG.StandardType.UnitSixThreeKG

end
