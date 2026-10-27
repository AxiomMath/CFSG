module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Defs
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.NaturalEndField
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped Matrix

section Scalar

variable {n : Type} [Fintype n] [DecidableEq n] [Nontrivial n]

lemma matrix_scalar_of_comm (F : Matrix n n (ZMod 2) →ₗ[ZMod 2] Matrix n n (ZMod 2))
    (hL : ∀ i j, i ≠ j → ∀ X, F (Matrix.transvection i j (1 : ZMod 2) * X) =
      Matrix.transvection i j (1 : ZMod 2) * F X)
    (hR : ∀ i j, i ≠ j → ∀ X, F (X * Matrix.transvection i j (1 : ZMod 2)) =
      F X * Matrix.transvection i j (1 : ZMod 2)) :
    ∃ c : ZMod 2, ∀ X, F X = c • X := by
  have hL' : ∀ i j, i ≠ j → ∀ X, F (Matrix.single i j (1 : ZMod 2) * X) =
      Matrix.single i j (1 : ZMod 2) * F X := by
    intro i j hij X
    have := hL i j hij X
    simp only [Matrix.transvection, add_mul, one_mul, map_add] at this
    simpa using this
  have hR' : ∀ i j, i ≠ j → ∀ X, F (X * Matrix.single i j (1 : ZMod 2)) =
      F X * Matrix.single i j (1 : ZMod 2) := by
    intro i j hij X
    have := hR i j hij X
    simp only [Matrix.transvection, mul_add, mul_one, map_add] at this
    simpa using this
  set Z := F 1 with hZ
  have hcomm : Pairwise fun i j => Commute (Matrix.single i j (1 : ZMod 2)) Z := by
    intro i j hij
    have h1 := hL' i j hij 1
    have h2 := hR' i j hij 1
    rw [mul_one] at h1
    rw [one_mul] at h2
    exact h1.symm.trans h2
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  have hZc : Z = c • (1 : Matrix n n (ZMod 2)) := by
    rw [← hc]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hoff : ∀ k l, k ≠ l → F (Matrix.single k l (1 : ZMod 2)) =
      c • Matrix.single k l (1 : ZMod 2) := by
    intro k l hkl
    have := hL' k l hkl 1
    rw [mul_one, ← hZ, hZc] at this
    rw [this]
    simp
  have hdiag : ∀ k, F (Matrix.single k k (1 : ZMod 2)) = c • Matrix.single k k (1 : ZMod 2) := by
    intro k
    obtain ⟨m, hm⟩ := exists_ne k
    have h1 : Matrix.single k k (1 : ZMod 2) =
        Matrix.single k m (1 : ZMod 2) * Matrix.single m k (1 : ZMod 2) := by
      rw [Matrix.single_mul_single_same]; simp
    rw [h1, hL' k m hm.symm, hoff m k hm, Matrix.mul_smul, Matrix.single_mul_single_same]
  have hall : ∀ k l, F (Matrix.single k l (1 : ZMod 2)) = c • Matrix.single k l (1 : ZMod 2) := by
    intro k l
    by_cases h : k = l
    · subst h; exact hdiag k
    · exact hoff k l h
  refine ⟨c, fun X => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ZMod 2) := by
    rw [Matrix.smul_single]; simp
  rw [this, map_smul, hall, smul_comm]

end Scalar

section Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def slOfDet (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det = 1) :
    ↥(StatedSL 3 (ZMod 2)) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h]; exact one_ne_zero),
    Subgroup.subset_closure h⟩

private lemma slOfDet_coe (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det = 1) :
    (((slOfDet A h : ↥(StatedSL 3 (ZMod 2))) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = A := rfl

private lemma tensor_left {H : Subgroup (GLV V)}
    {φ : ↥H ≃* (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2)))}
    {ψ : V ≃ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
        (((φ γ).1 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ψ v *
          (((φ γ).2 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)
    (g : ↥(StatedSL 3 (ZMod 2))) (v : V) :
    ψ ((φ.symm (g, 1) : GLV V) v) =
      ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ψ v := by
  rw [hψ]
  simp

private lemma tensor_right {H : Subgroup (GLV V)}
    {φ : ↥H ≃* (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2)))}
    {ψ : V ≃ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
        (((φ γ).1 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ψ v *
          (((φ γ).2 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)
    (g : ↥(StatedSL 3 (ZMod 2))) (v : V) :
    ψ ((φ.symm (1, g) : GLV V) v) =
      ψ v * ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  rw [hψ]
  simp

private lemma transvection_det (i j : Fin 3) (h : i ≠ j) :
    (Matrix.transvection i j (1 : ZMod 2)).det = 1 :=
  Matrix.det_transvection_of_ne i j h 1

private lemma commutant_scalar_of_tensor {H : Subgroup (GLV V)}
    {φ : ↥H ≃* (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2)))}
    {ψ : V ≃ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
        (((φ γ).1 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ψ v *
          (((φ γ).2 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)
    {f : Module.End (ZMod 2) V} (hf : f ∈ endCommutant H) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  set F : Matrix (Fin 3) (Fin 3) (ZMod 2) →ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    ψ.toLinearMap ∘ₗ f ∘ₗ ψ.symm.toLinearMap with hF
  have hFapp : ∀ X, F X = ψ (f (ψ.symm X)) := fun X => rfl
  have hcomm : ∀ (γ : ↥H) (v : V), (γ : GLV V) (f v) = f ((γ : GLV V) v) := fun γ v =>
    apply_of_mem_endCommutant hf γ.2 v
  have hLeft : ∀ g : ↥(StatedSL 3 (ZMod 2)), ∀ X,
      F (((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) =
        ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) * F X := by
    intro g X
    set γ : ↥H := φ.symm (g, 1) with hγ
    have h1 : ψ.symm (((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) = (γ : GLV V) (ψ.symm X) := by
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hγ, tensor_left hψ, LinearEquiv.apply_symm_apply]
    rw [hFapp, hFapp, h1, ← hcomm, hγ, tensor_left hψ]
  have hRight : ∀ g : ↥(StatedSL 3 (ZMod 2)), ∀ X,
      F (X * ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) =
        F X * ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
    intro g X
    set γ : ↥H := φ.symm (1, g) with hγ
    have h1 : ψ.symm (X * ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) = (γ : GLV V) (ψ.symm X) := by
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hγ, tensor_right hψ, LinearEquiv.apply_symm_apply]
    rw [hFapp, hFapp, h1, ← hcomm, hγ, tensor_right hψ]
  obtain ⟨c, hc⟩ := matrix_scalar_of_comm F
    (fun i j hij X => by
      have := hLeft (slOfDet _ (transvection_det i j hij)) X
      rwa [slOfDet_coe] at this)
    (fun i j hij X => by
      have := hRight (slOfDet (Matrix.transvection j i (1 : ZMod 2)) (transvection_det j i hij.symm)) X
      rw [slOfDet_coe] at this
      simpa [Matrix.transvection, Matrix.transpose_add] using this)
  refine ⟨c, fun v => ?_⟩
  apply ψ.injective
  have := hc (ψ v)
  rw [hFapp, LinearEquiv.symm_apply_apply] at this
  rw [this, map_smul]

private lemma endIsField_of_isTensorModel_three_aux [Finite V] {H : Subgroup (GLV V)}
    (hH : IsTensorModel 3 (ZMod 2) H) : EndIsField H 1 := by
  obtain ⟨φ, ψ, hψ⟩ := hH
  have : Nontrivial V := ψ.toEquiv.nontrivial
  let θ : ZMod 2 →ₐ[ZMod 2] ↥(endCommutant H) := Algebra.ofId (ZMod 2) _
  have hθinj : Function.Injective θ := (algebraMap (ZMod 2) ↥(endCommutant H)).injective
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, hc⟩ := commutant_scalar_of_tensor hψ x.2
    refine ⟨c, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    rw [hc v]
    simp [θ, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  let E1 : ZMod 2 ≃ₐ[ZMod 2] ↥(endCommutant H) := AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Nat.card_zmod,
      GaloisField.card 2 1 one_ne_zero]
    norm_num
  exact ⟨E1.symm.trans (FiniteField.algEquivOfCardEq 2 hcard)⟩

private def M7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private def M7inv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

private lemma M7_mul_inv : M7 * M7inv = 1 := by decide
private lemma M7_inv_mul : M7inv * M7 = 1 := by decide
private lemma M7_det : M7.det = 1 := by decide
private lemma M7_poly : M7 * M7 * M7 + M7 + 1 = 0 := by decide
private lemma M7inv_poly_ne : M7inv * M7inv * M7inv + M7inv + 1 ≠ 0 := by decide

private def g7 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  ⟨M7, M7inv, M7_mul_inv, M7_inv_mul⟩

private def g7S : ↥(StatedSL 3 (ZMod 2)) := ⟨g7, Subgroup.subset_closure M7_det⟩

private lemma g7S_coe : ((g7S : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = M7 := rfl

private lemma g7Sinv_coe : (((g7S⁻¹ : ↥(StatedSL 3 (ZMod 2))) :
    Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = M7inv := rfl

private lemma adjoint_poly {W : Type} [AddCommGroup W] (F : W → W → ZMod 2)
    (hadd : ∀ x y w, F (x + y) w = F x w + F y w)
    (hadd2 : ∀ v x y, F v (x + y) = F v x + F v y)
    (hnd : ∀ w, (∀ v, F v w = 0) → w = 0) (A B : W → W)
    (hAB : ∀ v w, F (A v) w = F v (B w)) (hp : ∀ v, A (A (A v)) + A v + v = 0)
    (w : W) : B (B (B w)) + B w + w = 0 := by
  apply hnd
  intro v
  have h0 : F 0 w = 0 := by
    have := hadd 0 0 w
    simpa using this
  have h := congrArg (fun x => F x w) (hp v)
  simp only [hadd, h0] at h
  have e1 : F v (B w) = F (A v) w := (hAB v w).symm
  have e2 : F v (B (B (B w))) = F (A (A (A v))) w := by
    rw [← hAB, ← hAB, ← hAB]
  rw [hadd2, hadd2, e1, e2, ← h]

theorem endIsField_and_not_selfDual_of_isTensorModel_three {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {H : Subgroup (GLV V)} (hH : IsTensorModel 3 (ZMod 2) H) :
    EndIsField H 1 ∧ ¬ SelfDual H ⊤ := by
  refine ⟨endIsField_of_isTensorModel_three_aux hH, ?_⟩
  rintro ⟨f, hnd, hinv⟩
  obtain ⟨φ, ψ, hψ⟩ := hH
  set ga : ↥H := φ.symm (g7S, 1) with hga
  set gb : ↥H := φ.symm (g7S⁻¹, 1) with hgb
  have ha : ∀ v, ψ ((ga : GLV V) v) = M7 * ψ v := fun v => by
    rw [hga, tensor_left hψ, g7S_coe]
  have hb : ∀ v, ψ ((gb : GLV V) v) = M7inv * ψ v := fun v => by
    rw [hgb, tensor_left hψ, g7Sinv_coe]
  have hgab : ∀ w, (ga : GLV V) ((gb : GLV V) w) = w := fun w => by
    apply ψ.injective
    rw [ha, hb, ← mul_assoc, M7_mul_inv, one_mul]
  let F : V → V → ZMod 2 := fun v w => f ⟨v, Submodule.mem_top⟩ ⟨w, Submodule.mem_top⟩
  have hadd : ∀ x y w, F (x + y) w = F x w + F y w := fun x y w => by
    have := f.map_add (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule (ZMod 2) V))
      ⟨y, Submodule.mem_top⟩
    exact congrArg (fun g => g ⟨w, Submodule.mem_top⟩) this
  have hadd2 : ∀ v x y, F v (x + y) = F v x + F v y := fun v x y => by
    exact (f ⟨v, Submodule.mem_top⟩).map_add ⟨x, Submodule.mem_top⟩ ⟨y, Submodule.mem_top⟩
  have hnd' : ∀ w, (∀ v, F v w = 0) → w = 0 := by
    intro w hw
    have := hnd.2 ⟨w, Submodule.mem_top⟩ (fun x => hw x)
    exact congrArg Subtype.val this
  have hAB : ∀ v w, F ((ga : GLV V) v) w = F v ((gb : GLV V) w) := by
    intro v w
    have := hinv (ga : GLV V) ga.2 ⟨v, Submodule.mem_top⟩ ⟨(gb : GLV V) w, Submodule.mem_top⟩
      ⟨(ga : GLV V) v, Submodule.mem_top⟩ ⟨w, Submodule.mem_top⟩ rfl (hgab w)
    exact this
  have hp : ∀ v, (ga : GLV V) ((ga : GLV V) ((ga : GLV V) v)) + (ga : GLV V) v + v = 0 := by
    intro v
    apply ψ.injective
    rw [map_add, map_add, ha, ha, ha, map_zero]
    have : M7 * (M7 * (M7 * ψ v)) + M7 * ψ v + ψ v = (M7 * M7 * M7 + M7 + 1) * ψ v := by
      noncomm_ring
    rw [this, M7_poly, zero_mul]
  have key := adjoint_poly F hadd hadd2 hnd' (fun v => (ga : GLV V) v) (fun v => (gb : GLV V) v) hAB hp
    (ψ.symm 1)
  have key' := congrArg ψ key
  simp only [map_add, hb, map_zero, LinearEquiv.apply_symm_apply] at key'
  apply M7inv_poly_ne
  have : M7inv * (M7inv * (M7inv * 1)) + M7inv * 1 + 1 = M7inv * M7inv * M7inv + M7inv + 1 := by
    noncomm_ring
  rw [← this]
  exact key'

end Tensor

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
