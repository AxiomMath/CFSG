module

public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.Open.PGLModelDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal

theorem nine3_orth63_quadCoe (K : Type) [Field K] (b c : K) :
    ⇑(CFSG.LieType.Universal.Spin.quadMinus 3 K b c) =
      CFSG.PGLModel.minusQuadForm 2 (K := K) b c := by
  funext v
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  rfl

theorem nine3_orth63_orthogonal_eq (K : Type) [Field K] (b c : K) :
    CFSG.PGLModel.orthogonalMinus 2 K b c =
      (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus 3 K b c)).comap
        (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).toMonoidHom := by
  have h := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
    (ι := Fin 2 ⊕ Fin 2 ⊕ Fin 2) (K := K)
    (Q := CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
    (Q₀ := CFSG.PGLModel.minusQuadForm 2 (K := K) b c) (nine3_orth63_quadCoe K b c)
  simpa [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup,
    CFSG.MatrixModel.isometryCore] using h

theorem nine3_orth63_rank_eq (K : Type) [Field K] (r : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) :
    Matrix.rank ((r : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) - 1) =
      Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K r)) := by
  have h : (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K r :
        (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K)).toLinearMap -
        LinearMap.id =
      ((r : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) - 1).mulVecLin := by
    ext x
    simp [Matrix.sub_mulVec, toLinEquiv_apply, Matrix.one_mulVec]
  rw [Matrix.rank, CFSG.RankThree.OrthogonalInvolutions.commSpace]
  exact (congrArg (fun m : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) →ₗ[K]
      (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) => Module.finrank K (LinearMap.range m)) h).symm

theorem nine3_rank_one_isometry_eq_reflect {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    {t : V ≃ₗ[K] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht1 : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace t) = 1) :
    ∃ x, Q x ≠ 0 ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect Q x := by
  have htt : t * t = 1 :=
    CFSG.RankThree.PartOne.KCOrthogonal.mul_self_eq_one_of_finrank_commSpace_eq_one hQ ht ht1
  have hne : CFSG.RankThree.OrthogonalInvolutions.commSpace t ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at ht1
    exact one_ne_zero ht1.symm
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have htx : t x = -x := by
    obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hxmem
    have htv : t (t v) = v := by
      have := congrArg (fun g : V ≃ₗ[K] V => g v) htt
      simpa [LinearEquiv.mul_apply] using this
    have h1 : x = t v - v := hv.symm
    rw [h1, map_sub, htv]
    abel
  have hfix_le : CFSG.RankThree.OrthogonalInvolutions.fixSpace t ≤
      LinearMap.ker (polarBilin Q x) := by
    intro y hy
    rw [LinearMap.mem_ker, polarBilin_apply_apply]
    have hty : t y = y := CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hy
    have hp : polar Q x y = polar Q (t x) (t y) :=
      (CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem ht x y).symm
    rw [htx, hty, QuadraticMap.polar_neg_left] at hp
    have h3 : (2 : K) * polar Q x y = 0 := by linear_combination hp
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hker_finrank : Module.finrank K (LinearMap.ker (polarBilin Q x)) =
      Module.finrank K V - 1 := by
    have hφ : polarBilin Q x ≠ 0 := by
      intro hzero
      apply hx0
      apply hQ.1 x
      intro w
      rw [polarBilin_apply_apply]
      exact LinearMap.congr_fun hzero w
    have hrange_ne : LinearMap.range (polarBilin Q x) ≠ ⊥ := by
      intro hbot
      apply hφ
      ext w
      have hmem : polarBilin Q x w ∈ LinearMap.range (polarBilin Q x) :=
        LinearMap.mem_range_self _ w
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    have hrange : LinearMap.range (polarBilin Q x) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      obtain ⟨w, hw⟩ : ∃ w, polarBilin Q x w ≠ 0 := by
        by_contra hcon
        exact hφ (LinearMap.ext fun w => by
          have h := not_exists.mp hcon w
          simpa using not_not.mp h)
      exact ⟨(c / polarBilin Q x w) • w, by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hw]⟩
    have h4 := (polarBilin Q x).finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self] at h4
    omega
  have hfix_eq : CFSG.RankThree.OrthogonalInvolutions.fixSpace t =
      LinearMap.ker (polarBilin Q x) := by
    apply Submodule.eq_of_le_of_finrank_eq hfix_le
    have hdim := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace t
    rw [ht1] at hdim
    omega
  have hfix_ker : ∀ z, polarBilin Q x z = 0 → t z = z := by
    intro z hz
    have hz' : z ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace t := by
      rw [hfix_eq]
      exact LinearMap.mem_ker.mpr hz
    exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hz'
  have hQx : Q x ≠ 0 := by
    intro hQx0
    have hxker : x ∈ LinearMap.ker (polarBilin Q x) := by
      rw [LinearMap.mem_ker, polarBilin_apply_apply, QuadraticMap.polar_self, hQx0, smul_zero]
    have hxt : t x = x := hfix_ker x (LinearMap.mem_ker.mp (hfix_eq ▸ hxker))
    have h2x : (2 : K) • x = 0 := by
      have hxneg : x = -x := hxt.symm.trans htx
      have h : x + x = 0 := by
        nth_rewrite 2 [hxneg]
        exact add_neg_cancel x
      simpa [two_smul] using h
    exact hx0 ((smul_eq_zero.mp h2x).resolve_left h2)
  refine ⟨x, hQx, ?_⟩
  have h2Q : (2 : K) * Q x ≠ 0 := mul_ne_zero h2 hQx
  refine LinearEquiv.ext fun y => ?_
  set c : K := polar Q x y / (2 * Q x) with hcdef
  have hz : polarBilin Q x (y - c • x) = 0 := by
    rw [polarBilin_apply_apply, polar_sub_right, polar_smul_right, QuadraticMap.polar_self,
      nsmul_eq_mul, smul_eq_mul, hcdef]
    field_simp
    ring
  have h1 : t (y - c • x) = y - c • x := hfix_ker _ hz
  have h2' : CFSG.ClassicalGroups.Orthogonal.reflect Q x (y - c • x) = y - c • x :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hz
  have h3 : CFSG.ClassicalGroups.Orthogonal.reflect Q x x = -x :=
    CFSG.GH74.Filter.reflect_apply_self hQx
  calc t y = t ((y - c • x) + c • x) := by rw [sub_add_cancel]
    _ = t (y - c • x) + c • t x := by rw [map_add, map_smul]
    _ = (y - c • x) + c • (-x) := by rw [h1, htx]
    _ = (y - c • x) + c • CFSG.ClassicalGroups.Orthogonal.reflect Q x x := by rw [h3]
    _ = CFSG.ClassicalGroups.Orthogonal.reflect Q x (y - c • x) +
        c • CFSG.ClassicalGroups.Orthogonal.reflect Q x x := by rw [h2']
    _ = CFSG.ClassicalGroups.Orthogonal.reflect Q x ((y - c • x) + c • x) := by
        rw [map_add, map_smul]
    _ = CFSG.ClassicalGroups.Orthogonal.reflect Q x y := by rw [sub_add_cancel]

end CFSG.LocalAnalysis.WeakClosure81
