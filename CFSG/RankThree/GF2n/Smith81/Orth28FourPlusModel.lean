module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorAlg
public import CFSG.RankThree.GF2n.Smith81.TiOmega4Plus
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormAct
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormSylow
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.RankThree.GF2n.Smith81.D2
open CFSG.RankThree.OrthogonalInvolutions
open scoped Matrix MatrixGroups

section Coord

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def thetaC (μ : (ι → K) ≃ₗ[K] Mat2 K) : ((ι → K) × (ι → K)) ≃ₗ[K] Cube 3 K where
  toFun p x := (μ (if x 0 = 0 then p.1 else p.2)) (x 1) (x 2)
  invFun T := (μ.symm (Matrix.of fun b c => T ![0, b, c]),
    μ.symm (Matrix.of fun b c => T ![1, b, c]))
  map_add' p q := by
    funext x
    by_cases h : x 0 = 0 <;> simp [h]
  map_smul' c p := by
    funext x
    by_cases h : x 0 = 0 <;> simp [h]
  left_inv p := by
    ext x
    · show μ.symm (μ p.1) x = p.1 x
      simp
    · show μ.symm (μ p.2) x = p.2 x
      simp
  right_inv T := by
    funext x
    have hx : x = ![x 0, x 1, x 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a
    generalize x 1 = b
    generalize x 2 = c
    fin_cases a <;> simp

theorem thetaC_apply (μ : (ι → K) ≃ₗ[K] Mat2 K) (p : (ι → K) × (ι → K)) (x : Fin 3 → Fin 2) :
    thetaC μ p x = (μ (if x 0 = 0 then p.1 else p.2)) (x 1) (x 2) := rfl

@[expose] def swL (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : Mat2 K) : (ι → K) →ₗ[K] (ι → K) :=
  μ.symm.toLinearMap ∘ₗ pairLin h k ∘ₗ μ.toLinearMap

theorem mu_swL (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : Mat2 K) (v : ι → K) :
    μ (swL μ h k v) = h * μ v * kᵀ := by
  simp [swL]

theorem swL_comp (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : Mat2 K) :
    swL μ h k = swL μ h 1 ∘ₗ swL μ 1 k := by
  refine LinearMap.ext fun v => ?_
  apply μ.injective
  simp [mu_swL, Matrix.mul_assoc]

theorem thetaC_orthTensor_zero (μ : (ι → K) ≃ₗ[K] Mat2 K) (g : Mat2 K)
    (p : (ι → K) × (ι → K)) :
    thetaC μ (orthTensor g id p) = actMap 0 g (thetaC μ p) := by
  funext x
  rw [actMap_apply, thetaC_apply]
  obtain h | h : x 0 = 0 ∨ x 0 = 1 := by
    generalize x 0 = a
    fin_cases a <;> simp
  · simp [orthTensor, Fin.sum_univ_two, thetaC_apply, Function.update_apply, h]
  · simp [orthTensor, Fin.sum_univ_two, thetaC_apply, Function.update_apply, h]

theorem thetaC_orthTensor_one (μ : (ι → K) ≃ₗ[K] Mat2 K) (h : Mat2 K)
    (p : (ι → K) × (ι → K)) :
    thetaC μ (orthTensor 1 (swL μ h 1) p) = actMap 1 h (thetaC μ p) := by
  funext x
  rw [actMap_apply, thetaC_apply, orthTensor_one_linear]
  have e : ∀ q : ι → K, μ (swL μ h 1 q) (x 1) (x 2) =
      ∑ b : Fin 2, h (x 1) b * μ q b (x 2) := by
    intro q
    rw [mu_swL, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_apply]
  by_cases h0 : x 0 = 0 <;> simp [thetaC_apply, Function.update_apply, h0, e]

theorem thetaC_orthTensor_two (μ : (ι → K) ≃ₗ[K] Mat2 K) (k : Mat2 K)
    (p : (ι → K) × (ι → K)) :
    thetaC μ (orthTensor 1 (swL μ 1 k) p) = actMap 2 k (thetaC μ p) := by
  funext x
  rw [actMap_apply, thetaC_apply, orthTensor_one_linear]
  have e : ∀ q : ι → K, μ (swL μ 1 k q) (x 1) (x 2) =
      ∑ b : Fin 2, k (x 2) b * μ q (x 1) b := by
    intro q
    rw [mu_swL, Matrix.one_mul, Matrix.mul_apply]
    simp [Matrix.transpose_apply, mul_comm]
  by_cases h0 : x 0 = 0 <;> simp [thetaC_apply, Function.update_apply, h0, e]

theorem thetaC_orthTensor (μ : (ι → K) ≃ₗ[K] Mat2 K) (g h k : Mat2 K) (p : (ι → K) × (ι → K)) :
    thetaC μ (orthTensor g (swL μ h k) p) = kronMap ![g, h, k] (thetaC μ p) := by
  have e1 : orthTensor g (swL μ h k) p =
      orthTensor g id (orthTensor 1 (swL μ h 1) (orthTensor 1 (swL μ 1 k) p)) := by
    have h1 := orthTensor_comp (1 : Mat2 K) 1 (swL μ h 1) (swL μ 1 k) p
    have h2 := orthTensor_comp g 1 (LinearMap.id : (ι → K) →ₗ[K] (ι → K))
      (swL μ h 1 ∘ₗ swL μ 1 k) p
    rw [one_mul] at h1
    rw [← swL_comp] at h1 h2
    rw [mul_one] at h2
    rw [h1]
    simpa using h2.symm
  rw [e1, thetaC_orthTensor_zero, thetaC_orthTensor_one, thetaC_orthTensor_two, kronMap_fin3]
  rfl

end Coord

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def swEquiv (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : SL(2, K)) : (ι → K) ≃ₗ[K] (ι → K) :=
  μ.trans ((pairEquiv h k).trans μ.symm)

theorem swEquiv_apply (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : SL(2, K)) (v : ι → K) :
    swEquiv μ h k v = μ.symm ((h : Mat2 K) * μ v * (k : Mat2 K)ᵀ) := rfl

theorem coe_swEquiv (μ : (ι → K) ≃ₗ[K] Mat2 K) (h k : SL(2, K)) :
    ⇑(swEquiv μ h k) = swL μ (h : Mat2 K) (k : Mat2 K) := by
  funext v
  apply μ.injective
  rw [swEquiv_apply, mu_swL, LinearEquiv.apply_symm_apply]

theorem swEquiv_mul (μ : (ι → K) ≃ₗ[K] Mat2 K) (h h' k k' : SL(2, K)) :
    swEquiv μ (h * h') (k * k') = swEquiv μ h k * swEquiv μ h' k' := by
  refine LinearEquiv.ext fun v => ?_
  apply μ.injective
  simp [swEquiv_apply, Matrix.mul_assoc]

theorem swEquiv_one (μ : (ι → K) ≃ₗ[K] Mat2 K) : swEquiv μ 1 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  simp [swEquiv_apply]

@[expose] def swHom (μ : (ι → K) ≃ₗ[K] Mat2 K) :
    SL(2, K) × SL(2, K) →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun p := swEquiv μ p.1 p.2
  map_one' := swEquiv_one μ
  map_mul' p q := swEquiv_mul μ p.1 q.1 p.2 q.2

theorem swHom_apply (μ : (ι → K) ≃ₗ[K] Mat2 K) (p : SL(2, K) × SL(2, K)) :
    swHom μ p = swEquiv μ p.1 p.2 := rfl

theorem swHom_injective (μ : (ι → K) ≃ₗ[K] Mat2 K) : Function.Injective (swHom μ) := by
  intro p q h
  apply pairHom_injective
  have h' : ∀ X : Mat2 K, (p.1 : Mat2 K) * X * (p.2 : Mat2 K)ᵀ =
      (q.1 : Mat2 K) * X * (q.2 : Mat2 K)ᵀ := by
    intro X
    have := congrArg (fun T : (ι → K) ≃ₗ[K] (ι → K) => μ (T (μ.symm X))) h
    simpa [swHom_apply, swEquiv_apply] using this
  exact LinearEquiv.ext fun X => by simpa [pairHom_apply] using h' X

theorem swEquiv_mem_orthogonalGroup {qU : QuadraticForm K (ι → K)}
    {μ : (ι → K) ≃ₗ[K] Mat2 K} (hμ : ∀ v, (μ v).det = qU v) (h k : SL(2, K)) :
    swEquiv μ h k ∈ TauCeti.QuadraticMap.orthogonalGroup qU := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [← hμ, ← hμ, swEquiv_apply, LinearEquiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
    one_mul, mul_one]

theorem swEquiv_mem_omega {qU : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin qU).Nondegenerate) {μ : (ι → K) ≃ₗ[K] Mat2 K}
    (hμ : ∀ v, (μ v).det = qU v) (h4 : 4 ≤ Nat.card K) (h k : SL(2, K)) :
    swEquiv μ h k ∈ omegaGroup qU hnd := by
  let P : SL(2, K) × SL(2, K) →* ↥(TauCeti.QuadraticMap.orthogonalGroup qU) :=
    (swHom μ).codRestrict _ fun p => swEquiv_mem_orthogonalGroup hμ p.1 p.2
  let D := dicksonHom qU hnd
  have hcomm : ∀ f : SL(2, K) →* Multiplicative (ZMod 2), ∀ a, f a = 1 := by
    intro f a
    have := Abelianization.commutator_subset_ker f
    rw [sl2_commutator_eq_top h4] at this
    exact MonoidHom.mem_ker.mp (this (Subgroup.mem_top a))
  have h1 : D (P (h, 1)) = 1 := hcomm (D.comp (P.comp (MonoidHom.inl _ _))) h
  have h2 : D (P (1, k)) = 1 := hcomm (D.comp (P.comp (MonoidHom.inr _ _))) k
  have h3 : D (P (h, k)) = 1 := by
    have : (h, k) = (h, 1) * (1, k) := by simp
    rw [this, map_mul, map_mul, h1, h2, one_mul]
  have h5 : P (h, k) ∈ D.ker := h3
  rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at h5
  exact h5

theorem card_orthogonalGroup_four {qU : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin qU).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType qU) (hdim : Module.finrank K (ι → K) = 4) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qU) =
      2 * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd (m := 1)
    (by omega) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hq2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq
  simp only [Finset.Icc_self, Finset.prod_singleton] at h
  zify [hq2]
  convert h using 1
  ring

theorem mem_omegaGroup_iff_exists_swEquiv {qU : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin qU).Nondegenerate) {μ : (ι → K) ≃ₗ[K] Mat2 K}
    (hμ : ∀ v, (μ v).det = qU v) (h4 : 4 ≤ Nat.card K)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType qU) (hι : Fintype.card ι = 4)
    {o : (ι → K) ≃ₗ[K] (ι → K)} :
    o ∈ omegaGroup qU hnd ↔ ∃ h k : SL(2, K), o = swEquiv μ h k := by
  refine ⟨fun ho => ?_, fun ⟨h, k, hk⟩ => hk ▸ swEquiv_mem_omega hnd hμ h4 h k⟩
  have hdim : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial (ι → K) := inferInstance
  haveI : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun e : (ι → K) ≃ₗ[K] (ι → K) => (e : (ι → K) → (ι → K)))
      DFunLike.coe_injective
  have hPΩ : (swHom μ).range ≤ omegaGroup qU hnd := by
    rintro _ ⟨⟨h, k⟩, rfl⟩
    exact swEquiv_mem_omega hnd hμ h4 h k
  have hcardP : Nat.card (swHom μ).range = Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (swHom_injective μ)).toEquiv, Nat.card_prod,
      card_sl2]
    have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
    ring
  have hidx := relIndex_omegaGroup qU hnd
  have hmul := Subgroup.relIndex_mul_card (H := omegaGroup qU hnd)
    (K := TauCeti.QuadraticMap.orthogonalGroup qU)
  rw [inf_of_le_left (omegaGroup_le qU hnd), hidx, card_orthogonalGroup_four hnd hplus hdim] at hmul
  have hcardΩ : Nat.card (omegaGroup qU hnd) = Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    omega
  have heq : (swHom μ).range = omegaGroup qU hnd :=
    Subgroup.eq_of_le_of_card_ge hPΩ (by rw [hcardP, hcardΩ])
  have : o ∈ (swHom μ).range := heq ▸ ho
  obtain ⟨⟨h, k⟩, hhk⟩ := this
  exact ⟨h, k, hhk.symm⟩

end Omega

section Normalize

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_sq_eq_one {a : K} (h : a ^ 2 = 1) : a = 1 := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) * (a - 1) = 0 := by linear_combination h + (1 - a) * h2K
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)

theorem exists_sqrt_det (h : Fin 3 → Mat2 K) (hu : ∀ i, IsUnit (h i).det) :
    ∃ r : Fin 3 → K, (∀ i, r i ≠ 0) ∧ ∀ i, (h i).det = r i * r i := by
  have hex : ∀ i, ∃ r : K, (h i).det = r * r := fun i =>
    (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (h i).det)
  choose r hr using hex
  refine ⟨r, fun i h0 => ?_, hr⟩
  have := (hu i).ne_zero
  rw [hr i, h0, mul_zero] at this
  exact this rfl

theorem det_inv_smul {r : K} (hr : r ≠ 0) (A : Mat2 K) :
    ((r⁻¹ • A : Mat2 K)).det = (r⁻¹) ^ 2 * A.det := by
  rw [Matrix.det_smul, Fintype.card_fin]

theorem exists_scalar_sl (h : Fin 3 → Mat2 K) (hu : ∀ i, IsUnit (h i).det) :
    ∃ (c : K) (s : Fin 3 → Mat2 K), c ≠ 0 ∧ (∀ i, (s i).det = 1) ∧
      kronMap h = c • kronMap s := by
  obtain ⟨r, hr0, hr⟩ := exists_sqrt_det h hu
  refine ⟨∏ i, r i, fun i => (r i)⁻¹ • h i, Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i,
    fun i => ?_, kronMap_smul_pi h _ r fun i => ?_⟩
  · rw [det_inv_smul (hr0 i), hr i]
    field_simp [hr0 i]
  · rw [smul_smul, mul_inv_cancel₀ (hr0 i), one_smul]

theorem exists_sl_of_involution (h : Fin 3 → Mat2 K) (hu : ∀ i, IsUnit (h i).det)
    (hsq : kronMap h ∘ₗ kronMap h = LinearMap.id) :
    ∃ s : Fin 3 → Mat2 K, (∀ i, (s i).det = 1) ∧ kronMap h = kronMap s := by
  have hsq' : kronMap (h * h) = LinearMap.id := by rw [kronMap_mul, hsq]
  obtain ⟨l, hl0, hl⟩ : ∃ l : Fin 3 → K, (∀ i, l i ≠ 0) ∧ ∀ i, (h * h) i = l i • 1 := by
    have := kronMap_eq_one_scalar (h * h) hsq'
    choose l hl0 hl using this
    exact ⟨l, hl0, hl⟩
  have hprod : (∏ i, l i) = 1 := by
    have h1 : kronMap (h * h) = (∏ i, l i) • kronMap (1 : Fin 3 → Mat2 K) :=
      kronMap_smul_pi (h * h) 1 l hl
    rw [hsq', kronMap_one] at h1
    have h2 := LinearMap.congr_fun h1 (fun _ => (1 : K))
    have h3 := congrFun h2 (fun _ => 0)
    simpa using h3.symm
  have hdet2 : ∀ i, ((h i).det) ^ 2 = (l i) ^ 2 := by
    intro i
    have h1 := congrArg Matrix.det (hl i)
    rw [Pi.mul_apply, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h1
    rw [pow_two, h1]
    ring
  have hdprod : (∏ i, (h i).det) = 1 := by
    have h1 : (∏ i, (h i).det) ^ 2 = 1 := by
      rw [← Finset.prod_pow, Finset.prod_congr rfl fun i _ => hdet2 i, Finset.prod_pow, hprod,
        one_pow]
    exact eq_one_of_sq_eq_one h1
  obtain ⟨r, hr0, hr⟩ := exists_sqrt_det h hu
  have hrprod : (∏ i, r i) = 1 := by
    have h1 : (∏ i, r i) ^ 2 = 1 := by
      rw [pow_two, ← Finset.prod_mul_distrib]
      simpa [← hr] using hdprod
    exact eq_one_of_sq_eq_one h1
  refine ⟨fun i => (r i)⁻¹ • h i, fun i => ?_, ?_⟩
  · rw [det_inv_smul (hr0 i), hr i]
    field_simp [hr0 i]
  · have := kronMap_smul_pi h (fun i => (r i)⁻¹ • h i) r fun i => by
      rw [smul_smul, mul_inv_cancel₀ (hr0 i), one_smul]
    rw [this, hrprod, one_smul]

end Normalize

end CFSG.RankThree.GF2n.Smith81.FourPlus
