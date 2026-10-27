module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGD
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGA
public import CFSG.Quasithin.Vol2.KGNatSemi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped MatrixGroups

namespace C11P9B

variable {K : Type} [Field K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem inner_of_linear [Finite K] [CharP K 2] [Finite W]
    (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {τ : MulAut W} (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {T T' : (Fin 3 → K) →+ (Fin 3 → K)}
    (hTf : ∀ w, T (f w) = f (τ w)) (hT'f : ∀ w, T' (f w) = f (τ⁻¹ w))
    (hT : ∀ (c : K) x, T (c • x) = c • T x) (hT' : ∀ (c : K) x, T' (c • x) = c • T' x)
    (hU : τ ∈ stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) :
    ∃ γ ∈ gammaW H (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup),
      ∀ x ∈ gammaW H (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup),
        τ * x * τ⁻¹ * (γ * x * γ⁻¹)⁻¹ ∈
          pCoreOf 2 (gammaW H (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hψ := psiW_injective hf g
  rw [gammaW_one_eq hSL hf, pCoreOf_map_of_injective _ hψ, pCoreOf_stabE0]
  obtain ⟨Mg, hMg⟩ := exists_mat_conj T hT g
  obtain ⟨Mg', hMg'⟩ := exists_mat_conj T' hT' g
  have hTT' : ∀ x, T (T' x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT'f, hTf, MulAut.apply_inv_self]
  have hMM : Mg * Mg' = 1 := matrix_eq_of_mulVec fun u => by
    rw [← Matrix.mulVec_mulVec, hMg', hMg, g_ginv_mulVec, hTT', ginv_g_mulVec, Matrix.one_mulVec]
  obtain ⟨m10, m20⟩ := col_zero_of_stab hf g hTf hU hMg
  obtain ⟨m10', m20'⟩ := col_zero_of_stab hf g hT'f (Subgroup.inv_mem _ hU) hMg'
  have hNN : lev Mg * lev Mg' = 1 := by
    rw [← lev_mul m10 m20, hMM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lev]
  have hdet : (lev Mg).det * (lev Mg').det = 1 := by rw [← Matrix.det_mul, hNN, Matrix.det_one]
  have hd0 : (lev Mg).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (lev Mg).det
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hd0 hs
  let A : SL(2, K) := ⟨s⁻¹ • lev Mg, by
    rw [Matrix.det_smul, Fintype.card_fin, hs]
    field_simp⟩
  let A' : SL(2, K) := ⟨s • lev Mg', by
    rw [Matrix.det_smul, Fintype.card_fin, pow_two, ← hs]
    exact hdet⟩
  have hAA' : A * A' = 1 := by
    refine Subtype.ext ?_
    show (s⁻¹ • lev Mg) * (s • lev Mg') = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul, hNN]
  have hAinv : A⁻¹ = A' := inv_eq_of_mul_eq_one_right hAA'
  obtain ⟨⟨B₀, hB₀⟩, hlev0⟩ := leviHom_surjective (K := K) A
  refine ⟨psiW π g B₀, ⟨B₀, hB₀, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨B', hB'⟩ := exists_psiW_eq hf g (hτH _ (psiW_mem π g B))
  have hB'mat : (B' : Matrix (Fin 3) (Fin 3) K) = Mg * (B : Matrix (Fin 3) (Fin 3) K) * Mg' := by
    refine matrix_eq_of_mulVec fun u => ?_
    obtain ⟨w, hw⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u)
    have h1 : f (psiW π g B' w) = f ((τ * psiW π g B * τ⁻¹) w) := by rw [hB']
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hTf, psiW_apply, psiW_apply, hf.act3, hf.act3,
      gconj_mulVec, gconj_mulVec, ← hT'f, hw, ginv_g_mulVec] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMg', hMg, ← h1, ginv_g_mulVec]
  obtain ⟨-, b10, b20⟩ := stabE0_entries hB
  have hM00 : Mg 0 0 * Mg' 0 0 = 1 := by
    have := congrFun (congrFun hMM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, m10', m20'] using this
  have hB'stab : B' ∈ stabE0 K := by
    rw [mem_stabE0, hB'mat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      col_mulVec_e0 m10' m20', Matrix.mulVec_smul, mem_stabE0.mp hB, Matrix.mulVec_smul,
      col_mulVec_e0 m10 m20, smul_smul, mul_comm, hM00, one_smul]
  have hMB10 : (Mg * (B : Matrix (Fin 3) (Fin 3) K)) 1 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, m10, b10, b20]
  have hMB20 : (Mg * (B : Matrix (Fin 3) (Fin 3) K)) 2 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, m20, b10, b20]
  have hY : B₀ * B * B₀⁻¹ ∈ stabE0 K :=
    (stabE0 K).mul_mem ((stabE0 K).mul_mem hB₀ hB) ((stabE0 K).inv_mem hB₀)
  have hlevEq : leviHom K ⟨B', hB'stab⟩ = leviHom K ⟨B₀ * B * B₀⁻¹, hY⟩ := by
    have e1 : (⟨B₀ * B * B₀⁻¹, hY⟩ : ↥(stabE0 K)) = ⟨B₀, hB₀⟩ * ⟨B, hB⟩ * ⟨B₀, hB₀⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, hlev0, hAinv]
    refine Subtype.ext ?_
    show lev (B' : Matrix (Fin 3) (Fin 3) K) =
      (s⁻¹ • lev Mg) * lev (B : Matrix (Fin 3) (Fin 3) K) * (s • lev Mg')
    rw [hB'mat, lev_mul hMB10 hMB20, lev_mul m10 m20, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hmem : B' * (B₀ * B * B₀⁻¹)⁻¹ ∈ rad1 K := by
    refine ⟨⟨B', hB'stab⟩ * ⟨B₀ * B * B₀⁻¹, hY⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hlevEq, mul_inv_cancel]
  refine ⟨B' * (B₀ * B * B₀⁻¹)⁻¹, hmem, ?_⟩
  rw [map_mul, map_inv, hB', map_mul, map_mul, map_inv]

end C11P9B

open C11P9B in
theorem factFieldAutPointSL3_holds : FactFieldAutPointSL3 := by
  intro K _ _ hK W _ _ hW H Z π hπ _ P hP U₁ hU₁ D hD
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK'
  have hSL := commutator_SL2_eq_top (four_le_card le_rfl hK')
  obtain ⟨f, hf, g, rfl, hU1, -⟩ := exists_coord_torus3 le_rfl hK' hW hπ hP hD
  rw [hU1 U₁ (by rw [hK]; exact hU₁)]
  intro τ hτH hτZ hτU _ hout d hd
  have hτ : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (hτZ z).mp hz
  have hτ' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz => ((Subgroup.inv_mem _ hτZ) z).mp hz
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    (x₀ := ![1, 0, 0]) (fun h => by simpa using congrFun h 0) τ hτ hτ'
    (conj_inv_mem_of_conj_mem hτH)
  rcases ringHom_eq_id_or_sq hK σ with hid | hsq
  · exfalso
    have hT : ∀ (c : K) x, hf.autMap τ hτ (c • x) = c • hf.autMap τ hτ x := fun c x => by
      rw [hσ, hid]
    have hTT' : ∀ x, hf.autMap τ hτ (hf.autMap τ⁻¹ hτ' x) = x := fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hf.autMap_apply, hf.autMap_apply, MulAut.apply_inv_self]
    have hT'T : ∀ x, hf.autMap τ⁻¹ hτ' (hf.autMap τ hτ x) = x := fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hf.autMap_apply, hf.autMap_apply, MulAut.inv_apply_self]
    have hT' : ∀ (c : K) x, hf.autMap τ⁻¹ hτ' (c • x) = c • hf.autMap τ⁻¹ hτ' x :=
      fun c x => by
        conv_lhs => rw [← hTT' x, ← hT, hT'T]
    obtain ⟨γ, hγ, hall⟩ := inner_of_linear hSL hf g hτH (hf.autMap_apply τ hτ)
      (hf.autMap_apply τ⁻¹ hτ') hT hT' hτU
    obtain ⟨x, hx, hnot⟩ := hout γ hγ
    exact hnot (hall x hx)
  · rw [centW_one_eq hSL hf g] at hd
    obtain ⟨_, ⟨⟨t, rfl⟩, hA⟩, rfl⟩ := hd
    have h3 : ∀ s : Kˣ, s ^ 3 = 1 := fun s => by
      have h := pow_card_eq_one' (G := Kˣ) (x := s)
      rw [Nat.card_units, hK] at h
      exact h
    have h1 := (tSL_mem_sc1_iff t).mp hA
    have hdact : ∀ w, f (psiW π g (tSL t) w) = (t.2 : K) • f w := fun w => by
      rw [psiW_apply, hf.act3, gconj_mulVec, tSL_mulVec_of_three h1 (h3 t.2), Matrix.mulVec_smul,
        g_ginv_mulVec]
    have hc3 : (t.2 : K) ^ 2 * t.2 = 1 := by
      have := congrArg Units.val (h3 t.2)
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      rw [← this]
      ring
    have hdH : psiW π g (tSL t) ∈ H := psiW_mem π g _
    have hkey : ∀ w, f ((τ * psiW π g (tSL t) * τ⁻¹ * psiW π g (tSL t)) w) = f w := fun w => by
      simp only [MulAut.mul_apply]
      rw [← hf.autMap_apply τ hτ, hdact, hσ, hf.autMap_apply, MulAut.apply_inv_self, hdact,
        smul_smul, hsq, hc3, one_smul]
    rw [eq_one_of_act_eq hf (H.mul_mem (hτH _ hdH) hdH) hkey]
    exact Subgroup.one_mem _

end CFSG.Quasithin.Vol2.Ch11.SecA
