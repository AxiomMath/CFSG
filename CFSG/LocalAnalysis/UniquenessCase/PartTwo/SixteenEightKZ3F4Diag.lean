module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Lin
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

open Module

noncomputable section

private lemma s16k_f4_commute_of_mul_comm (g g' : S16kGL6)
    (f f' : (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4))
    (hf : ∀ v : Fin 6 → ZMod 2, f (s16kTheta v) =
      s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v))
    (hf' : ∀ v : Fin 6 → ZMod 2, f' (s16kTheta v) =
      s16kTheta ((g' : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v))
    (hgg' : g * g' = g' * g) : f * f' = f' * f := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := s16kTheta_bijective.2 x
  have h1 : f (f' (s16kTheta v)) = s16kTheta ((g * g').val.mulVec v) := by
    rw [hf' v, hf, Matrix.mulVec_mulVec, ← Units.val_mul]
  have h2 : f' (f (s16kTheta v)) = s16kTheta ((g' * g).val.mulVec v) := by
    rw [hf v, hf', Matrix.mulVec_mulVec, ← Units.val_mul]
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2, hgg']

private lemma s16k_f4_pow_apply (g : S16kGL6)
    (f : (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4))
    (hf : ∀ v : Fin 6 → ZMod 2, f (s16kTheta v) =
      s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v))
    (n : ℕ) (v : Fin 6 → ZMod 2) :
    (f ^ n) (s16kTheta v) =
      s16kTheta (((g ^ n : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ f n, Module.End.mul_apply, hf v, ih (g.val.mulVec v),
        Matrix.mulVec_mulVec, ← Units.val_mul, ← pow_succ g n]

theorem s16k_f4_conj_diag {E : Subgroup S16kGL6}
    (hE : E ≤ Subgroup.centralizer (s16kScal : Set S16kGL6)) (hE1 : IsElemAbelian 3 E) :
    ∃ c ∈ Subgroup.centralizer (s16kScal : Set S16kGL6), ∃ μ : E → Fin 3 → S16kF4,
      ∀ (e : E) (i : Fin 3),
        (μ e i = 1 ∨ μ e i = s16kAlpha ∨ μ e i = s16kAlpha ^ 2) ∧
        ∀ v : Fin 6 → ZMod 2,
          s16kTheta (((c * (e : S16kGL6) * c⁻¹ : S16kGL6) :
            Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) i = μ e i * s16kTheta v i := by
  classical
  let f : E → (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4) := fun e =>
    (s16k_f4_lin (e : S16kGL6) (hE e.2)).choose
  have hf : ∀ (e : E) (v : Fin 6 → ZMod 2),
      f e (s16kTheta v) =
        s16kTheta (((e : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) :=
    fun e => (s16k_f4_lin (e : S16kGL6) (hE e.2)).choose_spec
  have hcomm : ∀ e e' : E, Commute (f e) (f e') := by
    intro e e'
    have hmul : (e : S16kGL6) * (e' : S16kGL6) = (e' : S16kGL6) * (e : S16kGL6) := by
      simpa using congrArg (fun x : E => (x : S16kGL6)) (hE1.1.is_comm.comm e e')
    exact s16k_f4_commute_of_mul_comm (e : S16kGL6) (e' : S16kGL6) (f e) (f e')
      (hf e) (hf e') hmul
  have hpow : ∀ e : E, f e ^ 3 = 1 := by
    intro e
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := s16kTheta_bijective.2 x
    rw [s16k_f4_pow_apply (e : S16kGL6) (f e) (hf e) 3 v]
    have h3 : (e : S16kGL6) ^ 3 = 1 := hE1.2 (e : S16kGL6) e.2
    rw [h3]
    simp
  obtain ⟨b, μ0, hb⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one
      (K := S16kF4) (V := Fin 3 → S16kF4) (p := 3) (ζ := s16kAlpha)
      s16kAlpha_primitive f hcomm hpow
  have hfr : Module.finrank S16kF4 (Fin 3 → S16kF4) = 3 :=
    Module.finrank_fin_fun (R := S16kF4)
  let b' : Basis (Fin 3) S16kF4 (Fin 3 → S16kF4) := b.reindex (finCongr hfr)
  let μ : E → Fin 3 → S16kF4 := fun e j => μ0 e ((finCongr hfr).symm j)
  have hb'_apply : ∀ j : Fin 3, b' j = b ((finCongr hfr).symm j) :=
    fun j => Basis.reindex_apply b (finCongr hfr) j
  have hb' : ∀ (e : E) (j : Fin 3), f e (b' j) = μ e j • b' j := by
    intro e j
    rw [hb'_apply j]
    exact hb e ((finCongr hfr).symm j)
  have hμ3 : ∀ (e : E) (j : Fin 3), μ e j ^ 3 = 1 := by
    intro e j
    have key : ∀ n : ℕ, (f e ^ n) (b' j) = (μ e j) ^ n • b' j := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ' (f e) n, Module.End.mul_apply, ih, LinearMap.map_smul, hb' e j,
            smul_smul, pow_succ]
    have h1 : (f e ^ 3) (b' j) = (μ e j) ^ 3 • b' j := key 3
    rw [hpow e] at h1
    have h2 : (μ e j ^ 3 - 1) • b' j = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      simpa using h1.symm
    have hne : b' j ≠ 0 := Basis.ne_zero b' j
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hne)
  let b₂ : Basis (Fin 3) S16kF4 (Fin 3 → S16kF4) := Pi.basisFun S16kF4 (Fin 3)
  let c' : (Fin 3 → S16kF4) ≃ₗ[S16kF4] (Fin 3 → S16kF4) :=
    b'.equiv b₂ (Equiv.refl (Fin 3))
  have hc'b' : ∀ j : Fin 3, c' (b' j) = b₂ j := by
    intro j
    show b'.equiv b₂ (Equiv.refl (Fin 3)) (b' j) = b₂ j
    rw [Basis.equiv_apply]
    rfl
  have hc'symm : ∀ j : Fin 3, c'.symm (b₂ j) = b' j := by
    intro j
    rw [← hc'b' j, LinearEquiv.symm_apply_apply]
  have hcoord : ∀ (e : E) (x : Fin 3 → S16kF4) (i : Fin 3),
      (c' (f e (c'.symm x))) i = μ e i * x i := by
    intro e x i
    let ψ : (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4) :=
      c'.toLinearMap.comp ((f e).comp c'.symm.toLinearMap)
    let χ : (Fin 3 → S16kF4) →ₗ[S16kF4] (Fin 3 → S16kF4) :=
      LinearMap.pi (fun i : Fin 3 =>
        μ e i • (LinearMap.proj i : (Fin 3 → S16kF4) →ₗ[S16kF4] S16kF4))
    have hL : ψ = χ := by
      refine b₂.ext ?_
      intro j
      change c' (f e (c'.symm (b₂ j))) = (LinearMap.pi (fun i : Fin 3 =>
        μ e i • (LinearMap.proj i : (Fin 3 → S16kF4) →ₗ[S16kF4] S16kF4))) (b₂ j)
      rw [hc'symm j, hb' e j, LinearEquiv.map_smul, hc'b' j]
      ext k
      simp only [Pi.smul_apply, LinearMap.pi_apply, LinearMap.proj_apply,
        LinearMap.smul_apply, smul_eq_mul]
      by_cases hk : k = j
      · rw [hk]
      · have h0 : b₂ j k = 0 := by
          change (Pi.basisFun S16kF4 (Fin 3)) j k = 0
          rw [Pi.basisFun_apply, Pi.single_eq_of_ne hk]
        rw [h0, mul_zero, mul_zero]
    exact congrFun (DFunLike.congr_fun hL x) i
  obtain ⟨c, hc, hcv⟩ := s16k_f4_unit c'
  have hc_inv : ∀ w : Fin 6 → ZMod 2,
      s16kTheta (((c⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w) =
        c'.symm (s16kTheta w) := by
    intro w
    have key : c' (s16kTheta (((c⁻¹ : S16kGL6) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w)) = s16kTheta w := by
      rw [← hcv (((c⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w)]
      rw [Matrix.mulVec_mulVec]
      have hcc : (c : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          ((c⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hcc, Matrix.one_mulVec]
    rw [← key, LinearEquiv.symm_apply_apply]
  refine ⟨c, hc, μ, ?_⟩
  intro e i
  refine ⟨s16kF4_cube (μ e i) (hμ3 e i), ?_⟩
  intro v
  have hdv : (((c * (e : S16kGL6) * c⁻¹ : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
      (c : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
        (((e : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (((c⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v)) := by
    simp only [Units.val_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hmain : s16kTheta (((c * (e : S16kGL6) * c⁻¹ : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
      fun k => μ e k * s16kTheta v k := by
    rw [hdv, hcv, ← hf e, hc_inv]
    funext i
    exact hcoord e (s16kTheta v) i
  exact congrFun hmain i

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
