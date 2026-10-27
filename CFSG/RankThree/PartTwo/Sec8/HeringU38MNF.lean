module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MCore
public import CFSG.RankThree.PartTwo.Sec8.HeringU38MAux
public import CFSG.RankThree.PartTwo.Sec8.HeringU38MAux2
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.Sec8 CFSG.GH74.KGroups

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem exists_fixed_conj {σ : K ≃+* K} (hσ : orderOf σ = 3) {β : MulAut (unitaryPSU h 3)}
    (hinn : IsInnerAut β) (hcomm : psuField h σ * β = β * psuField h σ) :
    ∃ B : unitaryIsom3 h, glAut σ (B : GL (Fin 3) K) = B ∧ β = psuConj h B := by
  obtain ⟨b, rfl⟩ := hinn
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 b
  set B₂ : unitaryIsom3 h := ⟨g, unitarySU_le_unitaryIsom3 g.2⟩ with hB₂
  have hβ : (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) (unitaryProj h 3 g) =
      psuConj h B₂ := conj_mk_eq_psuConj g
  rw [hβ] at hcomm ⊢
  set B₂' : unitaryIsom3 h := ⟨glAut σ (B₂ : GL (Fin 3) K), glAut_mem_unitaryIsom3 σ B₂.2⟩
    with hB₂'
  have h1 : psuConj h B₂' = psuConj h B₂ := by
    rw [hB₂', ← psuField_mul_psuConj_mul_inv, hcomm, mul_inv_cancel_right]
  have h2 : psuConj h (B₂⁻¹ * B₂') * psuField h 1 = 1 := by
    rw [map_mul, map_inv, h1, map_one, mul_one, inv_mul_cancel]
  obtain ⟨-, c, hcn, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one (B₂⁻¹ * B₂') 1 h2
  have hcA' : (B₂ : GL (Fin 3) K)⁻¹ * glAut σ (B₂ : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    have := hcA
    rwa [Subgroup.coe_mul, Subgroup.coe_inv] at this
  have hσB : glAut σ (B₂ : GL (Fin 3) K) =
      (B₂ : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hcA', mul_inv_cancel_left]
  have hc3 : (c : K) ^ 3 = 1 := by
    have hdet1 : ((B₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_unitarySU_iff h).mp g.2).1
    have hdetσ : (((B₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).det = 1 := by
      rw [show ((B₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        (σ : K →+* K).mapMatrix ((B₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) from rfl,
        ← RingHom.map_det, hdet1, map_one]
    have hm := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K).det) hσB
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three] at hm
    rw [hdetσ, hdet1] at hm
    linear_combination -hm
  have hc9 : (c : K) ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hc3, one_pow]
  have hcinv9 : c⁻¹ ^ 9 = 1 := by
    apply Units.ext
    simp [hc9]
  have hcinv3 : c⁻¹ ^ 3 = 1 := by
    apply Units.ext
    simp [hc3]
  obtain ⟨μ, hμ9, hσμ⟩ := exists_mu h hσ hcinv9 hcinv3
  have hμn : h.norm (μ : K) = 1 := by
    rw [norm_eq_pow_nine h, ← Units.val_pow_eq_pow_val, hμ9, Units.val_one]
  have hμI := scalar_mem_unitaryIsom3_of_norm (h := h) hμn
  set B₃ : unitaryIsom3 h := ⟨GeneralLinearGroup.scalar (Fin 3) μ * (B₂ : GL (Fin 3) K),
    mul_mem hμI B₂.2⟩ with hB₃
  refine ⟨B₃, ?_, ?_⟩
  ·
    show glAut σ (GeneralLinearGroup.scalar (Fin 3) μ * (B₂ : GL (Fin 3) K)) =
      GeneralLinearGroup.scalar (Fin 3) μ * (B₂ : GL (Fin 3) K)
    rw [map_mul, glAut_scalar, hσB, hσμ, map_mul, map_inv]
    have e1 := (commute_scalar c (B₂ : GL (Fin 3) K)).eq
    have e2 := (commute_scalar c (GeneralLinearGroup.scalar (Fin 3) μ)).eq
    calc (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ *
          ((B₂ : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c)
        = (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) μ * GeneralLinearGroup.scalar (Fin 3) c) *
          (B₂ : GL (Fin 3) K) := by rw [e1]; group
      _ = (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) c * GeneralLinearGroup.scalar (Fin 3) μ) *
          (B₂ : GL (Fin 3) K) := by rw [e2]
      _ = GeneralLinearGroup.scalar (Fin 3) μ * (B₂ : GL (Fin 3) K) := by group
  · rw [hB₃, show (⟨GeneralLinearGroup.scalar (Fin 3) μ * (B₂ : GL (Fin 3) K),
      mul_mem hμI B₂.2⟩ : unitaryIsom3 h) = ⟨_, hμI⟩ * B₂ from rfl, map_mul, psuConj_scalar hμI,
      one_mul]

theorem exists_mat3 {σ : K ≃+* K} {ι : F →+* K} (hι : Function.Injective ι)
    (hιs : ∀ y : K, σ y = y → ∃ a, ι a = y) {B : unitaryIsom3 h}
    (hB : glAut σ (B : GL (Fin 3) K) = B) (hB3 : psuConj h B ^ 3 = 1) :
    ∃ B₀ : Mat3, IsU B₀ ∧ ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = B₀.toMat ι ∧
      ∃ c₀ : F, c₀ ≠ 0 ∧ B₀ * B₀ * B₀ = Mat3.smul c₀ 1 := by
  classical
  set M : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hfix : ∀ i j, σ (M i j) = M i j := by
    intro i j
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) hB
    simpa [coe_glAut] using this
  choose f hf using fun i j => hιs (M i j) (hfix i j)
  set B₀ : Mat3 := ⟨f 0 0, f 0 1, f 0 2, f 1 0, f 1 1, f 1 2, f 2 0, f 2 1, f 2 2⟩ with hB₀
  have hMB₀ : M = B₀.toMat ι := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, hB₀, hf]
  have hU : IsU B₀ := by
    show B₀.cjT * B₀ = 1
    apply toMat_injective ι hι
    rw [toMat_mul, ← toMat_cjT h ι, ← hMB₀, toMat_one]
    exact B.2
  have h3 : psuConj h (B ^ 3) * psuField h 1 = 1 := by rw [map_one, mul_one, map_pow, hB3]
  obtain ⟨-, c₁, hc₁n, hc₁A⟩ := eq_one_of_psuConj_mul_psuField_eq_one (B ^ 3) 1 h3
  have hM3 : M * M * M = (c₁ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hc₁A
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at this
    rw [← pow_three', hM]
    exact this
  have hσc : σ (c₁ : K) = c₁ := by
    have h1 : (M * M * M).map σ = M * M * M := by
      rw [Matrix.map_mul, Matrix.map_mul]
      have : M.map σ = M := by
        ext i j
        exact hfix i j
      rw [this]
    rw [hM3] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2
  obtain ⟨c₀, hc₀⟩ := hιs _ hσc
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    have : (c₁ : K) = 0 := by rw [← hc₀, map_zero]
    exact c₁.ne_zero this
  refine ⟨B₀, hU, hMB₀, c₀, hc₀ne, ?_⟩
  apply toMat_injective ι hι
  rw [toMat_mul, toMat_mul, ← hMB₀, hM3, toMat_smul, toMat_one, hc₀]

@[expose] def V3.toVec (ι : F →+* K) (u : V3) : Fin 3 → K := ![ι u.x, ι u.y, ι u.z]

theorem mat3_mulVec (ι : F →+* K) (A : Mat3) (u : V3) :
    A.toMat ι *ᵥ V3.toVec ι u = V3.toVec ι (A.mv u) := by
  ext i
  fin_cases i <;> simp [V3.toVec, Mat3.toMat, Mat3.mv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, map_add, map_mul]

theorem det_cycMat_ne_zero (ι : F →+* K) (hι : Function.Injective ι) {B₀ : Mat3} {u : V3}
    (hu : (Mat3.ofCols u (B₀.mv u) (B₀.mv (B₀.mv u))).det ≠ 0) :
    (cycMat (B₀.toMat ι) (V3.toVec ι u)).det ≠ 0 := by
  have hcyc : cycMat (B₀.toMat ι) (V3.toVec ι u) =
      (Mat3.ofCols u (B₀.mv u) (B₀.mv (B₀.mv u))).toMat ι := by
    have e1 := mat3_mulVec ι B₀ u
    have e2 := mat3_mulVec ι B₀ (B₀.mv u)
    have c0 : ∀ i, V3.toVec ι u i = (Mat3.ofCols u (B₀.mv u) (B₀.mv (B₀.mv u))).toMat ι i 0 := by
      intro i
      fin_cases i <;> simp [V3.toVec, Mat3.toMat, Mat3.ofCols]
    have c1 : ∀ i, V3.toVec ι (B₀.mv u) i =
        (Mat3.ofCols u (B₀.mv u) (B₀.mv (B₀.mv u))).toMat ι i 1 := by
      intro i
      fin_cases i <;> simp [V3.toVec, Mat3.toMat, Mat3.ofCols]
    have c2 : ∀ i, V3.toVec ι (B₀.mv (B₀.mv u)) i =
        (Mat3.ofCols u (B₀.mv u) (B₀.mv (B₀.mv u))).toMat ι i 2 := by
      intro i
      fin_cases i <;> simp [V3.toVec, Mat3.toMat, Mat3.ofCols]
    ext i j
    simp only [cycMat, Matrix.of_apply]
    fin_cases j
    · exact c0 i
    · show (B₀.toMat ι *ᵥ V3.toVec ι u) i = _
      rw [e1]
      exact c1 i
    · show (B₀.toMat ι *ᵥ (B₀.toMat ι *ᵥ V3.toVec ι u)) i = _
      rw [e1, e2]
      exact c2 i
  rw [hcyc, toMat_det]
  intro h0
  exact hu (hι (by rw [h0, map_zero]))

theorem not_regF {ι : F →+* K} (hι : Function.Injective ι) {B : unitaryIsom3 h} {B₀ : Mat3}
    (hMB₀ : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = B₀.toMat ι) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hcube : B₀ * B₀ * B₀ = Mat3.smul c₀ 1) (hreg : RegF B₀)
    (h7 : 7 ∣ Nat.card ((psuConj h B).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)))) :
    False := by
  obtain ⟨y, hy7, hys, hyB⟩ := exists_commuting_seven h B h7
  obtain ⟨u, -, hu⟩ := hreg
  have hcu := det_cycMat_ne_zero ι hι hu
  rw [← hMB₀] at hcu
  have hB : adjM h ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    unfold adjM
    exact mem_unitaryIsom3.mp B.2
  have hB3 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (ι c₀) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hMB₀, ← toMat_mul, ← toMat_mul, hcube, toMat_smul, toMat_one]
  have hc3F : ∀ x : F, x ≠ 0 → x * x * x = 1 := by decide +kernel
  have hc3 : (ι c₀) ^ 3 = 1 := by
    rw [pow_three', ← map_mul, ← map_mul, hc3F c₀ hc₀, map_one]
  have hy : adjM h (mat y) * mat y = 1 := ((mem_unitarySU_iff h).mp y.2).2
  have hy7' : (mat y) ^ 7 = 1 := by rw [← mat_pow, hy7, mat_one]
  have := eq_one_of_regular h hB hB3 hc3 hcu hy hy7' hyB
  exact hys 1 (by rw [this, one_smul])

@[expose] noncomputable def toGU (ι : F →+* K) (A : Mat3) (hA : IsU A) : unitaryIsom3 h :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (A.toMat ι) (by
      intro h0
      have h1 := congrArg Matrix.det (isU_toMat h ι hA)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h1
      exact zero_ne_one h1),
    mem_unitaryIsom3.mpr (isU_toMat h ι hA)⟩

theorem exists_diag_conj {σ : K ≃+* K} {ι : F →+* K} (hι : Function.Injective ι)
    (hισ : ∀ a, σ (ι a) = ι a) {B : unitaryIsom3 h} {B₀ : Mat3}
    (hMB₀ : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = B₀.toMat ι) {H : Mat3} (hH : IsU H)
    {l m : F} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) (hBH : B₀ * H = H * Mat3.diag l l m) :
    ∃ G D : unitaryIsom3 h, glAut σ (G : GL (Fin 3) K) = G ∧ RefData h ι l m D ∧
      B = G * D * G⁻¹ := by
  set G : unitaryIsom3 h := toGU h ι H hH with hG
  have hGm : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = H.toMat ι := rfl
  have hGfix : glAut σ (G : GL (Fin 3) K) = G := by
    apply Units.ext
    rw [coe_glAut, hGm, map_toMat_eq ι hισ]
  set D : unitaryIsom3 h := G⁻¹ * B * G with hDdef
  have hHH : H.cjT * H = 1 := hH
  have hkey : H.cjT * B₀ * H = Mat3.diag l l m := by
    apply toMat_injective ι hι
    have e1 := congrArg (fun X => Mat3.toMat ι X) hBH
    have e2 := congrArg (fun X => Mat3.toMat ι X) hHH
    simp only [toMat_mul, toMat_one] at e1 e2
    rw [toMat_mul, toMat_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have hDm : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (Dg l m).toMat ι := by
    rw [hDdef, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      mat_inv_isom3 h G, hGm, hMB₀, toMat_cjT h ι, ← toMat_mul, ← toMat_mul, hkey]
    rfl
  refine ⟨G, D, hGfix, ⟨hl, hm, hlm, hDm⟩, ?_⟩
  rw [hDdef]
  group

theorem alpha_normal_form {α : MulAut (unitaryPSU h 3)} (hα3 : α ^ 3 = 1)
    (hαout : ¬ IsInnerAut α) (hu4 : ∃ u : unitaryPSU h 3, α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : unitaryIsom3 h,
      α = psuConj h H * psuField h σ * (psuConj h H)⁻¹ := by
  by_cases hD : α ∈ (psuConj h).range
  · exfalso
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨u, hu, hu4, hu2⟩ := hu4
    exact hαout (isInnerAut_psuConj_of_fixed_two_elt h A hα3 hu hu4 hu2)
  · exact unitary_order_three_field_descent (by norm_num : 2 < 2 ^ 3) α hα3 hD

theorem nf_psu {α β : MulAut (unitaryPSU h 3)} (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1)
    (hαβ : α * β = β * α) (hαout : ¬ IsInnerAut α)
    (hu4 : ∃ u : unitaryPSU h 3, α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1) (hβ1 : β ≠ 1)
    (h7 : 7 ∣ Nat.card (β.toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)))) :
    ∃ (G D : unitaryIsom3 h) (σ : K ≃+* K) (ι : F →+* K) (l m : F), orderOf σ = 3 ∧
      (∀ a, σ (ι a) = ι a) ∧ (∀ y : K, σ y = y → ∃ a, ι a = y) ∧ RefData h ι l m D ∧
      α = psuConj h G * psuField h σ * (psuConj h G)⁻¹ ∧
      β = psuConj h G * psuConj h D * (psuConj h G)⁻¹ := by
  classical
  obtain ⟨σ, hσ, H, hαH⟩ := alpha_normal_form h hα3 hαout hu4
  obtain ⟨ι, hισ, hιs⟩ := exists_iota h hσ
  have hι : Function.Injective ι := ι.injective
  set ψ : MulAut (unitaryPSU h 3) := psuConj h H with hψ
  set f : MulAut (unitaryPSU h 3) := psuField h σ with hf
  set β' : MulAut (unitaryPSU h 3) := ψ⁻¹ * β * ψ with hβ'
  have hβinn : IsInnerAut β := Item812Res3.isInnerAut_psu_of_seven_dvd h β hβ3 h7
  have hβ'inn : IsInnerAut β' := by
    have : β' = MulAut.congr (ψ⁻¹ : MulAut (unitaryPSU h 3)) β := by
      ext x
      simp [hβ', MulAut.congr_apply]
    rw [this, isInnerAut_congr]
    exact hβinn
  have hfβ' : f * β' = β' * f := by
    have hf' : f = ψ⁻¹ * α * ψ := by rw [hαH]; group
    calc f * β' = ψ⁻¹ * (α * β) * ψ := by rw [hf', hβ']; group
      _ = ψ⁻¹ * (β * α) * ψ := by rw [hαβ]
      _ = β' * f := by rw [hf', hβ']; group
  have hβ'3 : β' ^ 3 = 1 := by
    have h' := conj_pow (a := ψ⁻¹) (b := β) (i := 3)
    rw [inv_inv] at h'
    rw [hβ', h', hβ3]
    group
  have hβ'1 : β' ≠ 1 := by
    intro h1
    apply hβ1
    have : β = ψ * β' * ψ⁻¹ := by rw [hβ']; group
    rw [this, h1]
    group
  have h7' : 7 ∣ Nat.card (β'.toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3))) := by
    have := Item812Res3.card_eqLocus_conj (ψ⁻¹ : MulAut (unitaryPSU h 3)) β
    rw [inv_inv] at this
    rw [hβ', this]
    exact h7
  obtain ⟨B, hBfix, hβB⟩ := exists_fixed_conj h hσ hβ'inn hfβ'
  have hB3 : psuConj h B ^ 3 = 1 := by rw [← hβB]; exact hβ'3
  obtain ⟨B₀, hB₀U, hMB₀, c₀, hc₀, hcube⟩ := exists_mat3 h hι hιs hBfix hB3
  have hB₀ns : ∀ a : F, B₀ ≠ Mat3.smul a 1 := by
    intro a ha
    apply hβ'1
    have hMa : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (ι a) • 1 := by
      rw [hMB₀, ha, toMat_smul, toMat_one]
    have ha0 : ι a ≠ 0 := by
      intro h0
      apply Units.ne_zero (B : GL (Fin 3) K)
      rw [hMa, h0, zero_smul]
    have hBsc : (B : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (ι a) ha0) := by
      apply Units.ext
      rw [hMa, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      rfl
    rw [hβB]
    exact psuConj_eq_one_of_coe_eq_scalar hBsc
  have hcl := classify hB₀U ⟨c₀, mem_allF c₀, hc₀, hcube⟩ (fun a _ => hB₀ns a)
  rcases hcl with hreg | ⟨H₂, hH₂, l, -, m, -, hl, hm, hlm, hBH⟩
  · exfalso
    have h7B : 7 ∣ Nat.card ((psuConj h B).toMonoidHom.eqLocus
        (MonoidHom.id (unitaryPSU h 3))) := by
      rw [← hβB]
      exact h7'
    exact not_regF h hι hMB₀ hc₀ hcube hreg h7B
  · obtain ⟨G₂, D, hG₂fix, hD, hBGD⟩ := exists_diag_conj h hι hισ hMB₀ (cands_unitary H₂ hH₂) hl hm
      hlm hBH
    have hcommG₂ : f * psuConj h G₂ = psuConj h G₂ * f := by
      have h1 := psuField_mul_psuConj_mul_inv σ G₂
      have h2 : (⟨glAut σ (G₂ : GL (Fin 3) K), glAut_mem_unitaryIsom3 σ G₂.2⟩ : unitaryIsom3 h) =
          G₂ := Subtype.ext hG₂fix
      rw [h2] at h1
      rw [hf]
      calc psuField h σ * psuConj h G₂ = psuField h σ * psuConj h G₂ * (psuField h σ)⁻¹ *
            psuField h σ := by group
        _ = psuConj h G₂ * psuField h σ := by rw [h1]
    refine ⟨H * G₂, D, σ, ι, l, m, hσ, hισ, hιs, hD, ?_, ?_⟩
    · have hfix' : psuConj h G₂ * f * (psuConj h G₂)⁻¹ = f := by
        rw [← hcommG₂]; group
      rw [map_mul, ← hψ, ← hf, hαH]
      calc ψ * f * ψ⁻¹ = ψ * (psuConj h G₂ * f * (psuConj h G₂)⁻¹) * ψ⁻¹ := by rw [hfix']
        _ = ψ * psuConj h G₂ * f * (ψ * psuConj h G₂)⁻¹ := by group
    · have hβe : β = ψ * β' * ψ⁻¹ := by rw [hβ']; group
      rw [map_mul, ← hψ, hβe, hβB, hBGD, map_mul, map_mul, map_inv]
      group

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
