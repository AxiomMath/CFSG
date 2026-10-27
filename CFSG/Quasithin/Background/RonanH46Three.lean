module

public import CFSG.Quasithin.Background.HFL3PRank
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def diagGL1 (K : Type) [Field K] : Kˣ →* GL (Fin 3) K where
  toFun c := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 1, (c : K)]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp)
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.diagonal]
  map_mul' c d := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_three]

@[expose] noncomputable def dHom (hK : Nat.card K = (2 ^ 1) ^ 2) : Kˣ →* MulAut (HMod 1 K) :=
  (rhoT hK).comp (diagGL1 K)

@[expose] noncomputable def Dsub (hK : Nat.card K = (2 ^ 1) ^ 2) : Subgroup (MulAut (HMod 1 K)) :=
  (dHom hK).range

private theorem coe_diagGL1 (c : Kˣ) :
    ((diagGL1 K c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, 1, (c : K)] := rfl

private theorem dHom_apply (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Kˣ) :
    dHom hK c = rhoT hK (diagGL1 K c) := rfl

private theorem dHom_mem_Dsub (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Kˣ) : dHom hK c ∈ Dsub hK :=
  MonoidHom.mem_range.2 ⟨c, rfl⟩

private theorem dHom_injective (hK : Nat.card K = (2 ^ 1) ^ 2) : Function.Injective (dHom hK) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK (B := diagGL1 K c) hc
  have e00 := congrFun (congrFun hd 0) 0
  have e22 := congrFun (congrFun hd 2) 2
  rw [coe_diagGL1] at e00 e22
  simp at e00 e22
  apply Units.ext
  rw [Units.val_one]
  linear_combination e22 - e00

private theorem card_units_eq_three (hK : Nat.card K = (2 ^ 1) ^ 2) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK] <;> norm_num

theorem card_Dsub (hK : Nat.card K = (2 ^ 1) ^ 2) : Nat.card ↥(Dsub hK) = 3 :=
  (Nat.card_congr (MonoidHom.ofInjective (dHom_injective hK)).symm.toEquiv).trans
    (card_units_eq_three hK)

theorem Dsub_iso (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nonempty (↥(Dsub hK) ≃* Multiplicative (ZMod 3)) :=
  ⟨mulEquivOfPrimeCardEq (card_Dsub hK) (Nat.card_zmod 3)⟩

private theorem Q2_map_le_img (hK : Nat.card K = (2 ^ 1) ^ 2) : (Q2 K).map (rho hK) ≤ img hK := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact ⟨g, rfl⟩

private theorem Q2_map_le_centSub (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (Q2 K).map (rho hK) ≤ centSub (blkW 1 K) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  rw [mem_centSub]
  intro u hu
  exact blkW_le_fixV hg hK hu

private theorem dHom_mem_centSub (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Kˣ) :
    dHom hK c ∈ centSub (blkW 1 K) := by
  rw [mem_centSub]
  intro u hu
  obtain ⟨h02, h12, h22⟩ := mem_blkW.1 hu
  have h20 : mat u 2 0 = 0 := by rw [← herm_apply, h02, map_zero]
  have h21 : mat u 2 1 = 0 := by rw [← herm_apply, h12, map_zero]
  apply mat_injective
  change mat (rhoT hK (diagGL1 K c) u) = mat u
  rw [mat_rhoT, coe_diagGL1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h22, h20, h21]

private theorem Dsub_le_linImg (hK : Nat.card K = (2 ^ 1) ^ 2) : Dsub hK ≤ linImg hK := by
  intro x hx
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hx
  exact ⟨diagGL1 K c, rfl⟩

theorem sup_eq_linImg (hK : Nat.card K = (2 ^ 1) ^ 2) : img hK ⊔ Dsub hK = linImg hK := by
  refine le_antisymm (sup_le (img_le_linImg hK) (Dsub_le_linImg hK)) ?_
  intro x hx
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hx
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, Matrix.GeneralLinearGroup.det A = u := ⟨_, rfl⟩
  have hdiag : Matrix.GeneralLinearGroup.det (diagGL1 K u) = u := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagGL1, Matrix.det_diagonal,
      Fin.prod_univ_three]
    simp
  obtain ⟨S, hS⟩ : ∃ S : GL (Fin 3) K, S = A * (diagGL1 K u)⁻¹ := ⟨_, rfl⟩
  have hSdet : (S : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det S = 1 := by
      rw [hS, map_mul, map_inv, hdiag, hu, mul_inv_cancel]
    have h2 := congrArg Units.val h1
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h2
    simpa using h2
  have hA : rhoT hK A = rho hK ⟨(S : Matrix (Fin 3) (Fin 3) K), hSdet⟩ * dHom hK u := by
    rw [rho_mk hK hSdet, dHom_apply, ← map_mul]
    congr 1
    rw [hS, inv_mul_cancel_right]
  rw [hA]
  exact Subgroup.mul_mem_sup ⟨_, rfl⟩ (dHom_mem_Dsub hK u)

private theorem ker_rhoT_eq_center (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (rhoT hK).ker = Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h
    have hd0 : d ≠ 0 := by
      rintro rfl
      have h1 := Units.mul_inv g
      rw [hd, zero_smul, zero_mul] at h1
      exact zero_ne_one h1
    exact ⟨Units.mk0 d hd0, Units.ext ((coe_scalGL (Units.mk0 d hd0)).trans
      (by rw [Units.val_mk0]; exact hd.symm))⟩
  · rintro ⟨l, rfl⟩
    exact rhoT_eq_one_of_smul hK (coe_scalGL l) (norm_eq_one_of_four hK l.ne_zero)

theorem linImg_equiv_pgl (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nonempty (↥(linImg hK) ≃* (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K))) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (ker_rhoT_eq_center hK)).symm.trans
    (QuotientGroup.quotientKerEquivRange (rhoT hK))).symm⟩

private theorem exists_factor (hK : Nat.card K = (2 ^ 1) ^ 2) {z : MulAut (HMod 1 K)} (hz : z ∈ norm hK)
    (hfix : ∀ X ∈ blkW 1 K, z X = X) :
    ∃ g ∈ Q2 K, ∃ c : Kˣ, z = rho hK g * dHom hK c := by
  classical
  set p₁ : Fin 3 → K := Pi.single 0 1 with hp₁
  set p₂ : Fin 3 → K := Pi.single 1 1 with hp₂
  have hli : LinearIndependent K ![p₁, p₂] := by
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [hp₁, hp₂] at h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨D, α, rfl, hD₁, hD₂, hα⟩ := eq_rhoT_of_fix_line le_rfl hK hz hli
    (fun c => hfix _ (pt_mem_blkW hK (by simp [hp₁, hp₂])))
    (hfix _ (pt_mem_blkW hK (by simp [hp₂])))
  have hc₁ : ∀ i, (D : Matrix (Fin 3) (Fin 3) K) i 0 = α * p₁ i := by
    intro i
    have := congrFun hD₁ i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp₁] using this
  have hc₂ : ∀ i, (D : Matrix (Fin 3) (Fin 3) K) i 1 = α * p₂ i := by
    intro i
    have := congrFun hD₂ i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp₂] using this
  obtain ⟨a, b, γ, hDm⟩ : ∃ a b γ : K,
      (D : Matrix (Fin 3) (Fin 3) K) = !![α, 0, a; 0, α, b; 0, 0, γ] :=
    ⟨(D : Matrix (Fin 3) (Fin 3) K) 0 2, (D : Matrix (Fin 3) (Fin 3) K) 1 2,
      (D : Matrix (Fin 3) (Fin 3) K) 2 2, by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hc₁, hc₂, hp₁, hp₂]⟩
  have hdetD : (D : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit D)).ne_zero
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hα
    exact zero_ne_one hα
  have hγ0 : γ ≠ 0 := by
    intro h0
    apply hdetD
    rw [hDm, Matrix.det_fin_three]
    simp [h0]
  obtain ⟨g, hg_def⟩ : ∃ g : SpecialLinearGroup (Fin 3) K,
      g = ⟨!![1, 0, a / γ; 0, 1, b / γ; 0, 0, 1], by
        rw [Matrix.det_fin_three]; simp⟩ := ⟨_, rfl⟩
  have hgM : (g : Matrix (Fin 3) (Fin 3) K) = !![1, 0, a / γ; 0, 1, b / γ; 0, 0, 1] := by
    rw [hg_def]
  have hgQ : g ∈ Q2 K := by
    rw [mem_Q2]
    refine ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.2
      ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
    · rw [hgM]
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hji (by decide) | simp
    · rw [hgM]
      fin_cases i <;> simp
    · rw [hgM]
      simp
  have hc0 : γ / α ≠ 0 := div_ne_zero hγ0 hα0
  refine ⟨g, hgQ, Units.mk0 (γ / α) hc0, ?_⟩
  have hD : D = SpecialLinearGroup.toGL g * diagGL1 K (Units.mk0 (γ / α) hc0) *
      scalGL (Units.mk0 α hα0) := by
    have hgG : ((SpecialLinearGroup.toGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, 0, a / γ; 0, 1, b / γ; 0, 0, 1] := hgM
    apply Units.ext
    simp only [Units.val_mul, coe_scalGL, coe_diagGL1, Units.val_mk0, hgG, hDm]
    rw [Matrix.mul_smul, Matrix.mul_one]
    ext i j
    rw [Matrix.smul_apply, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  have hscal : rhoT hK (scalGL (Units.mk0 α hα0)) = 1 :=
    rhoT_eq_one_of_smul hK (coe_scalGL (Units.mk0 α hα0)) (norm_eq_one_of_four hK hα0)
  rw [hD, map_mul, map_mul, hscal, mul_one]
  rfl

theorem centSub_blkW_eq (hK : Nat.card K = (2 ^ 1) ^ 2) :
    norm hK ⊓ centSub (blkW 1 K) = (Q2 K).map (rho hK) ⊔ Dsub hK := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hzN, hzc⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨g, hg, c, rfl⟩ := exists_factor hK hzN (fun X hX => mem_centSub.1 hzc X hX)
    exact Subgroup.mul_mem_sup (Subgroup.mem_map.2 ⟨g, hg, rfl⟩) (dHom_mem_Dsub hK c)
  · refine sup_le ?_ ?_
    · exact le_inf ((Q2_map_le_img hK).trans Subgroup.le_normalizer) (Q2_map_le_centSub hK)
    · intro x hx
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hx
      exact Subgroup.mem_inf.2 ⟨rhoT_mem_norm hK _, dHom_mem_centSub hK c⟩

theorem part3 (hK : Nat.card K = (2 ^ 1) ^ 2) {M : Subgroup (MulAut (HMod 1 K))}
    (hLM : img hK ≤ M) (hMN : M ≤ norm hK) :
    M ⊓ centSub (blkW 1 K) = (Q2 K).map (rho hK) ∨
      ∃ D : Subgroup (MulAut (HMod 1 K)), Nonempty (↥D ≃* Multiplicative (ZMod 3)) ∧
        Nonempty (↥(img hK ⊔ D) ≃* (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K))) ∧
        M ⊓ centSub (blkW 1 K) = (Q2 K).map (rho hK) ⊔ D := by
  by_cases h : M ⊓ centSub (blkW 1 K) = (Q2 K).map (rho hK)
  · exact Or.inl h
  right
  have hQle : (Q2 K).map (rho hK) ≤ M ⊓ centSub (blkW 1 K) :=
    le_inf ((Q2_map_le_img hK).trans hLM) (Q2_map_le_centSub hK)
  have hCle : M ⊓ centSub (blkW 1 K) ≤ (Q2 K).map (rho hK) ⊔ Dsub hK := by
    intro z hz
    rw [← centSub_blkW_eq hK]
    exact Subgroup.mem_inf.2 ⟨hMN (Subgroup.mem_inf.1 hz).1, (Subgroup.mem_inf.1 hz).2⟩
  have hDle : Dsub hK ≤ M ⊓ centSub (blkW 1 K) := by
    obtain ⟨z, hzC, hzQ⟩ : ∃ z ∈ M ⊓ centSub (blkW 1 K), z ∉ (Q2 K).map (rho hK) := by
      by_contra hcon
      refine h (le_antisymm (fun z hz => ?_) hQle)
      by_contra hzQ
      exact hcon ⟨z, hz, hzQ⟩
    obtain ⟨g, hg, c, rfl⟩ := exists_factor hK (hMN (Subgroup.mem_inf.1 hzC).1)
      (fun X hX => mem_centSub.1 (Subgroup.mem_inf.1 hzC).2 X hX)
    have hgC : rho hK g ∈ M ⊓ centSub (blkW 1 K) := hQle (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
    have hdC : dHom hK c ∈ M ⊓ centSub (blkW 1 K) := by
      have h1 := (M ⊓ centSub (blkW 1 K)).mul_mem
        ((M ⊓ centSub (blkW 1 K)).inv_mem hgC) hzC
      rwa [inv_mul_cancel_left] at h1
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hzQ
      rw [map_one, mul_one]
      exact Subgroup.mem_map.2 ⟨g, hg, rfl⟩
    have hc3 : c ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact pow_three_eq_one_of_four hK c.ne_zero)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have htop : Subgroup.zpowers c = ⊤ :=
      Subgroup.eq_top_of_le_card (Subgroup.zpowers c)
        (by rw [Nat.card_zpowers, hordc, card_units_eq_three hK])
    have hle : Dsub hK ≤ Subgroup.zpowers (dHom hK c) := by
      intro x hx
      obtain ⟨c', rfl⟩ := MonoidHom.mem_range.1 hx
      have hc' : c' ∈ Subgroup.zpowers c := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      rw [map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    exact hle.trans (Subgroup.zpowers_le.2 hdC)
  refine ⟨Dsub hK, Dsub_iso hK, ?_, le_antisymm hCle (sup_le hQle hDle)⟩
  obtain ⟨e⟩ := linImg_equiv_pgl hK
  exact ⟨(MulEquiv.subgroupCongr (sup_eq_linImg hK)).trans e⟩

end CFSG.Quasithin.RonanH46
