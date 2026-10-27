module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Model
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

noncomputable section

private def s16kThetaEquiv : (Fin 6 → ZMod 2) ≃+ (Fin 3 → S16kF4) :=
  AddEquiv.ofBijective s16kTheta s16kTheta_bijective

private lemma s16kThetaEquiv_apply (v : Fin 6 → ZMod 2) :
    s16kThetaEquiv v = s16kTheta v := rfl

private lemma s16kThetaEquiv_symm_theta (v : Fin 6 → ZMod 2) :
    s16kThetaEquiv.symm (s16kTheta v) = v := by
  rw [← s16kThetaEquiv_apply]
  exact s16kThetaEquiv.symm_apply_apply v

private lemma s16k_mulVec_mul (M N : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (v : Fin 6 → ZMod 2) : M.mulVec (N.mulVec v) = (M * N).mulVec v :=
  Matrix.mulVec_mulVec v M N

private lemma s16k_mulVec_mul_symm (M N : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (v : Fin 6 → ZMod 2) : (M * N).mulVec v = M.mulVec (N.mulVec v) :=
  (Matrix.mulVec_mulVec v M N).symm

private lemma s16k_mulVec_omega_comm (g : S16kGL6)
    (hg : g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6)) (v : Fin 6 → ZMod 2) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (s16kOmegaBlk.mulVec v) =
      s16kOmegaBlk.mulVec ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) := by
  have h := (s16k_centralizer_scal_iff g).1 hg
  rw [s16k_mulVec_mul, h, s16k_mulVec_mul_symm]

private def s16kConjFun (g : S16kGL6) (x : Fin 3 → S16kF4) : Fin 3 → S16kF4 :=
  s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (s16kThetaEquiv.symm x))

private lemma s16kConjFun_theta (g : S16kGL6) (v : Fin 6 → ZMod 2) :
    s16kConjFun g (s16kTheta v) =
      s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) := by
  simp only [s16kConjFun, s16kThetaEquiv_symm_theta]

private lemma s16kConjFun_zero (g : S16kGL6) : s16kConjFun g 0 = 0 := by
  simp only [s16kConjFun, Matrix.mulVec_zero, map_zero]

private lemma s16kConjFun_add (g : S16kGL6) (x y : Fin 3 → S16kF4) :
    s16kConjFun g (x + y) = s16kConjFun g x + s16kConjFun g y := by
  simp only [s16kConjFun, map_add, Matrix.mulVec_add]

private lemma s16kConjFun_smul_alpha (g : S16kGL6)
    (hg : g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6)) (x : Fin 3 → S16kF4) :
    s16kConjFun g (s16kAlpha • x) = s16kAlpha • s16kConjFun g x := by
  obtain ⟨v, rfl⟩ := s16kThetaEquiv.surjective x
  change s16kConjFun g (s16kAlpha • s16kTheta v) =
    s16kAlpha • s16kConjFun g (s16kTheta v)
  calc
    s16kConjFun g (s16kAlpha • s16kTheta v)
        = s16kConjFun g (s16kTheta (s16kOmegaBlk.mulVec v)) := by
          rw [s16kTheta_omega]
    _ = s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (s16kOmegaBlk.mulVec v)) := s16kConjFun_theta g _
    _ = s16kTheta (s16kOmegaBlk.mulVec
          ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v)) := by
          rw [s16k_mulVec_omega_comm g hg]
    _ = s16kAlpha • s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) :=
          s16kTheta_omega _
    _ = s16kAlpha • s16kConjFun g (s16kTheta v) := by rw [s16kConjFun_theta]

private lemma s16kConjFun_smul_emb (g : S16kGL6) (a : ZMod 2) (x : Fin 3 → S16kF4) :
    s16kConjFun g (s16kEmb a • x) = s16kEmb a • s16kConjFun g x := by
  have h : a = 0 ∨ a = 1 := by
    have ha := ZMod.val_lt a
    rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · exact Or.inl ((ZMod.val_eq_zero a).1 h0)
    · refine Or.inr ((ZMod.val_eq_one (by norm_num) a).1 ?_)
      omega
  rcases h with rfl | rfl
  · rw [map_zero, zero_smul, zero_smul, s16kConjFun_zero]
  · rw [map_one, one_smul, one_smul]

private lemma s16kConjFun_smul (g : S16kGL6)
    (hg : g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6)) (c : S16kF4)
    (x : Fin 3 → S16kF4) :
    s16kConjFun g (c • x) = c • s16kConjFun g x := by
  obtain ⟨a, b, rfl⟩ := s16kF4_coeff c
  calc
    s16kConjFun g ((s16kEmb a + s16kAlpha * s16kEmb b) • x)
        = s16kConjFun g (s16kEmb a • x + (s16kAlpha * s16kEmb b) • x) := by
          rw [add_smul]
    _ = s16kConjFun g (s16kEmb a • x) +
          s16kConjFun g ((s16kAlpha * s16kEmb b) • x) := s16kConjFun_add g _ _
    _ = s16kEmb a • s16kConjFun g x +
          s16kAlpha • (s16kEmb b • s16kConjFun g x) := by
          rw [s16kConjFun_smul_emb, mul_smul, s16kConjFun_smul_alpha g hg,
            s16kConjFun_smul_emb]
    _ = (s16kEmb a + s16kAlpha * s16kEmb b) • s16kConjFun g x := by
          rw [add_smul, mul_smul]

private def s16kConjLin (g : S16kGL6)
    (hg : g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6)) :
    (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4) where
  toFun := s16kConjFun g
  map_add' := s16kConjFun_add g
  map_smul' := s16kConjFun_smul g hg

theorem s16k_f4_lin (g : S16kGL6) (hg : g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6)) :
    ∃ f : (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4), ∀ v : Fin 6 → ZMod 2,
      f (s16kTheta v) = s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) := by
  exact ⟨s16kConjLin g hg, fun v => s16kConjFun_theta g v⟩

private def s16kAddEquivOfLinAut (f : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4)) :
    (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) :=
  s16kThetaEquiv.trans (f.toAddEquiv.trans s16kThetaEquiv.symm)

private def s16kLinEquivOfAddEquiv (φ : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2)) :
    (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  __ := φ.toAddMonoidHom.toZModLinearMap 2
  invFun := φ.symm
  left_inv := φ.symm_apply_apply
  right_inv := φ.apply_symm_apply

private def s16kUnitOfAddEquiv (φ : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2)) : S16kGL6 :=
  (Matrix.GeneralLinearGroup.toLin).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (s16kLinEquivOfAddEquiv φ))

private lemma s16kUnitOfAddEquiv_apply (φ : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2))
    (v : Fin 6 → ZMod 2) :
    ((s16kUnitOfAddEquiv φ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v =
      φ v := by
  have h : Matrix.GeneralLinearGroup.toLin (s16kUnitOfAddEquiv φ) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (s16kLinEquivOfAddEquiv φ) :=
    MulEquiv.apply_symm_apply _ _
  have h2 : (Matrix.GeneralLinearGroup.toLin (s16kUnitOfAddEquiv φ) :
      (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      (φ.toAddMonoidHom.toZModLinearMap 2) := by
    rw [h]
    rfl
  have hv := congrArg (fun (G : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) => G v) h2
  simpa [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply] using hv

private def s16kUnitOfLinAut (f : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4)) : S16kGL6 :=
  s16kUnitOfAddEquiv (s16kAddEquivOfLinAut f)

private lemma s16kUnitOfLinAut_theta (f : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4))
    (v : Fin 6 → ZMod 2) :
    s16kTheta
        (((s16kUnitOfLinAut f : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
      f (s16kTheta v) := by
  rw [s16kUnitOfLinAut, s16kUnitOfAddEquiv_apply]
  unfold s16kAddEquivOfLinAut
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, s16kThetaEquiv_apply]
  exact s16kThetaEquiv.apply_symm_apply _

private lemma s16kUnitOfLinAut_mem (f : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4)) :
    s16kUnitOfLinAut f ∈ Subgroup.centralizer (s16kScal : Set S16kGL6) := by
  rw [s16k_centralizer_scal_iff]
  refine Matrix.toLin'.injective ?_
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
    s16k_mulVec_mul_symm ((s16kUnitOfLinAut f : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) s16kOmegaBlk v,
    s16k_mulVec_mul_symm s16kOmegaBlk ((s16kUnitOfLinAut f : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) v]
  apply s16kTheta_bijective.1
  rw [s16kUnitOfLinAut_theta f (s16kOmegaBlk.mulVec v), s16kTheta_omega v,
    f.map_smul, ← s16kUnitOfLinAut_theta f v,
    ← s16kTheta_omega (((s16kUnitOfLinAut f : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v)]

theorem s16k_f4_unit (c' : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4)) :
    ∃ c : S16kGL6, c ∈ Subgroup.centralizer (s16kScal : Set S16kGL6) ∧
      ∀ v : Fin 6 → ZMod 2,
        s16kTheta ((c : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) = c' (s16kTheta v) :=
  ⟨s16kUnitOfLinAut c', s16kUnitOfLinAut_mem c', s16kUnitOfLinAut_theta c'⟩

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
