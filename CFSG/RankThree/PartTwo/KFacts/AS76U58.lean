module

public import CFSG.RankThree.PartTwo.KFacts.AS76Tools
public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenAllInvolutionFourGroup

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec21.AS76.U58

open CFSG.RankThree.PartTwo.Sec21.AS76

open Module Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K bar_eq ω3 orderOf_ω3 ω3_pow PU ePU
  equivSUI c5 c5_pow_three normOneScalars_eq_bot)

abbrev hF : ReflForm K (Fin 5 → K) := unitaryForm 2 3 card_K 5

theorem hF_σ (c : K) : hF.σ c = c ^ 8 := by
  rw [show hF.σ c = unitaryInvolution K 2 3 c from rfl, unitaryInvolution_apply]
  norm_num

theorem map_bar_eq (A : Matrix (Fin 5) (Fin 5) K) :
    A.map hK.bar = A.map (unitaryInvolution K 2 3) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, bar_eq]

theorem mem_gramSU_iff {g : GL (Fin 5) K} :
    g ∈ gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ↔
      (∀ u v, hF.β ((g : Matrix (Fin 5) (Fin 5) K) *ᵥ u) ((g : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
        hF.β u v) ∧ (g : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have hmem : g ∈ gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ↔
      ((g : Matrix (Fin 5) (Fin 5) K).map hK.bar)ᵀ * (g : Matrix (Fin 5) (Fin 5) K) = 1 ∧
        (g : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    change (((g : Matrix (Fin 5) (Fin 5) K).map hK.bar)ᵀ *
      ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * (g : Matrix (Fin 5) (Fin 5) K) =
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ∧ _) ↔ _
    rw [Units.val_one, Matrix.mul_one]
  rw [hmem, unitaryForm_preserves_iff card_K, map_bar_eq]

theorem totallyIsotropic_of_isotropic (W : Submodule K (Fin 5 → K))
    (hW : ∀ x ∈ W, hF.β x x = 0) : W ≤ hF.perp W := by
  intro y hy x hx
  by_contra hd
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq card_K (a := 1) (map_one _)
  set t := c * (hF.β x y)⁻¹ with ht
  have h1 := hW (x + t • y) (W.add_mem hx (W.smul_mem t hy))
  rw [ReflForm.β_add_smul_add_smul, hW x hx, hW y hy, unitaryForm_symm card_K x y] at h1
  have hσ : hF.σ = unitaryInvolution K 2 3 := rfl
  rw [hσ] at h1
  have h2 : t * hF.β x y = c := by rw [ht, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have h3 : unitaryInvolution K 2 3 t * unitaryInvolution K 2 3 (hF.β x y) =
      unitaryInvolution K 2 3 c := by rw [← map_mul, h2]
  have h4 : t * hF.β x y + unitaryInvolution K 2 3 t * unitaryInvolution K 2 3 (hF.β x y) = 0 := by
    linear_combination h1
  rw [h2, h3, hc] at h4
  exact one_ne_zero h4

theorem exists_fixed_anisotropic (S : Matrix (Fin 5) (Fin 5) K) (hSS : S * S = 1) :
    ∃ x, S *ᵥ x = x ∧ hF.β x x ≠ 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨N, hN⟩ : ∃ N : Module.End K (Fin 5 → K), N = Matrix.toLin' S - 1 := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ LinearMap.ker N ↔ S *ᵥ x = x := fun x => by
    rw [LinearMap.mem_ker, hN, LinearMap.sub_apply, Matrix.toLin'_apply, Module.End.one_apply,
      sub_eq_zero]
  have hW := totallyIsotropic_of_isotropic (LinearMap.ker N) fun x hx =>
    hne x ((hmem x).mp hx)
  have h1 := hF.finrank_perp (LinearMap.ker N)
  have h2 := Submodule.finrank_mono hW
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    have hS2 : ∀ w, S *ᵥ (S *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hSS, one_mulVec]
    rw [hN]
    simp only [LinearMap.sub_apply, Matrix.toLin'_apply, Module.End.one_apply, mulVec_sub, hS2]
    have h : v - S *ᵥ v - (S *ᵥ v - v) = (2 : K) • (v - S *ᵥ v) := by module
    rw [h, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  have h3 : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.mpr (hNN v)
  have h4 := Submodule.finrank_mono h3
  have h5 := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at h1 h5
  omega

@[expose] def yMap (ω c : K) (x : Fin 5 → K) : Module.End K (Fin 5 → K) where
  toFun v := ω • v + (c * hF.β x v) • x
  map_add' u v := by rw [hF.add_right, smul_add, mul_add, add_smul]; abel
  map_smul' a v := by
    rw [hF.smul_right, RingHom.id_apply]
    module

theorem yMap_apply (ω c : K) (x v : Fin 5 → K) : yMap ω c x v = ω • v + (c * hF.β x v) • x :=
  rfl

section YMap

variable {ω c : K} {x : Fin 5 → K}

theorem yMap_isometry (hω3 : ω ^ 3 = 1) (hωq : ω ^ 2 + ω + 1 = 0) (hσω : hF.σ ω = ω ^ 2)
    (hσc : hF.σ c = c) (hc : c * hF.β x x = 1) (u v : Fin 5 → K) :
    hF.β (yMap ω c x u) (yMap ω c x v) = hF.β u v := by
  simp only [yMap_apply, hF.add_left, hF.add_right, hF.smul_left, hF.smul_right, map_mul, hσω,
    hσc]
  rw [show hF.σ (hF.β x u) = hF.β u x from (unitaryForm_symm card_K x u).symm]
  linear_combination hF.β u v * hω3 + (c * hF.β u x * hF.β x v) * hωq +
    (c * hF.β u x * hF.β x v) * hc

theorem yMap_x (hc : c * hF.β x x = 1) : yMap ω c x x = (ω + 1) • x := by
  rw [yMap_apply, hc, add_smul, one_smul]

theorem β_yMap (hc : c * hF.β x x = 1) (v : Fin 5 → K) :
    hF.β x (yMap ω c x v) = (ω + 1) * hF.β x v := by
  rw [yMap_apply, hF.add_right, hF.smul_right, hF.smul_right,
    show c * hF.β x v * hF.β x x = (c * hF.β x x) * hF.β x v by ring, hc]
  ring

theorem yMap_cube [CharP K 2] (hω3 : ω ^ 3 = 1) (hωq : ω ^ 2 + ω + 1 = 0)
    (hc : c * hF.β x x = 1) : yMap ω c x ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hY2 : ∀ v, yMap ω c x (yMap ω c x v) = ω ^ 2 • v + (c * hF.β x v) • x := fun v => by
    rw [yMap_apply (v := yMap ω c x v), β_yMap hc, yMap_apply]
    have h : ω * (c * hF.β x v) + c * ((ω + 1) * hF.β x v) = c * hF.β x v := by
      linear_combination (ω * c * hF.β x v) * h2
    calc ω • (ω • v + (c * hF.β x v) • x) + (c * ((ω + 1) * hF.β x v)) • x =
        ω ^ 2 • v + (ω * (c * hF.β x v) + c * ((ω + 1) * hF.β x v)) • x := by module
      _ = ω ^ 2 • v + (c * hF.β x v) • x := by rw [h]
  refine LinearMap.ext fun v => ?_
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, hY2 v, map_add, map_smul, map_smul,
    yMap_apply, yMap_x hc, Module.End.one_apply]
  have h : ω ^ 2 * (c * hF.β x v) + c * hF.β x v * (ω + 1) = 0 := by
    linear_combination (c * hF.β x v) * hωq
  have h' : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]
  calc ω ^ 2 • (ω • v + (c * hF.β x v) • x) + (c * hF.β x v) • ((ω + 1) • x) =
      (ω ^ 2 * ω) • v + (ω ^ 2 * (c * hF.β x v) + c * hF.β x v * (ω + 1)) • x := by module
    _ = v := by rw [h, h', one_smul, zero_smul, add_zero]

theorem yMap_ne_one (hω0 : ω ≠ 0) (hc : c * hF.β x x = 1) : yMap ω c x ≠ 1 := by
  intro h
  have h1 := yMap_x (ω := ω) hc
  rw [h, Module.End.one_apply, add_smul, one_smul, eq_comm, add_eq_right, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact hω0 h1
  · rw [h1, hF.β_zero_left, mul_zero] at hc
    exact zero_ne_one hc

theorem yMap_commute {S : Matrix (Fin 5) (Fin 5) K} (hSx : S *ᵥ x = x)
    (hS : ∀ u v, hF.β (S *ᵥ u) (S *ᵥ v) = hF.β u v) (v : Fin 5 → K) :
    yMap ω c x (S *ᵥ v) = S *ᵥ (yMap ω c x v) := by
  have h : hF.β x (S *ᵥ v) = hF.β x v := by rw [← hS x v, hSx]
  rw [yMap_apply, yMap_apply, mulVec_add, mulVec_smul, mulVec_smul, hSx, h]

theorem toMatrix'_yMap :
    LinearMap.toMatrix' (yMap ω c x) =
      ω • (1 : Matrix (Fin 5) (Fin 5) K) + c • vecMulVec x (unitaryInvolution K 2 3 ∘ x) := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, yMap_apply, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  rfl

theorem det_yMap [CharP K 2] (hω3 : ω ^ 3 = 1) (hωq : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0)
    (hc : c * hF.β x x = 1) : (LinearMap.toMatrix' (yMap ω c x)).det = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [toMatrix'_yMap]
  have hsplit : ω • (1 : Matrix (Fin 5) (Fin 5) K) + c • vecMulVec x (unitaryInvolution K 2 3 ∘ x) =
      ω • (1 + vecMulVec x ((ω⁻¹ * c) • (unitaryInvolution K 2 3 ∘ x))) := by
    rw [smul_add, vecMulVec_smul, smul_smul, mul_inv_cancel_left₀ hω0]
  rw [hsplit, det_smul, Fintype.card_fin, vecMulVec_eq (Fin 1),
    det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, smul_eq_mul,
    show (unitaryInvolution K 2 3 ∘ x) ⬝ᵥ x = hF.β x x from rfl, mul_assoc, hc, mul_one]
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hω3])
  rw [hinv]
  linear_combination (ω ^ 2 + ω ^ 4 + ω) * hω3 + hωq - h2

end YMap

theorem invCentThree_gramSU :
    InvCentThree (gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hs
  set S : Matrix (Fin 5) (Fin 5) K := ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hSdef
  have hSS : S * S = 1 := by
    have h := congrArg (fun g : gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =>
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hs
    simpa using h
  have hSiso := (mem_gramSU_iff.mp s.2).1
  obtain ⟨x, hSx, hxx⟩ := exists_fixed_anisotropic S hSS
  set ω : K := (ω3 : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by rw [hωdef, ← Units.val_pow_eq_pow_val, ω3_pow, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : ω3 = 1 := Units.ext h
    have h2 := orderOf_ω3
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hω0 : ω ≠ 0 := Units.ne_zero ω3
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hσω : hF.σ ω = ω ^ 2 := by
    rw [hF_σ, show ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 by ring, hω3, one_pow, one_mul]
  set c := (hF.β x x)⁻¹ with hcdef
  have hc : c * hF.β x x = 1 := inv_mul_cancel₀ hxx
  have hσc : hF.σ c = c := by
    have h := unitaryForm_symm card_K x x
    rw [hcdef, map_inv₀]
    exact congrArg (·⁻¹) h.symm
  obtain ⟨Y, hY⟩ : ∃ Y : Module.End K (Fin 5 → K), Y = yMap ω c x := ⟨_, rfl⟩
  set E := LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin 5) with hE
  have hdet : (E Y).det = 1 := by
    rw [show E Y = LinearMap.toMatrix' Y from rfl, hY]
    exact det_yMap hω3 hωq hω0 hc
  have hYv : ∀ v, E Y *ᵥ v = Y v := fun v => LinearMap.toMatrix'_mulVec Y v
  set g : GL (Fin 5) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (E Y)
    (by rw [hdet]; exact one_ne_zero) with hgdef
  have hgc : (g : Matrix (Fin 5) (Fin 5) K) = E Y := rfl
  have hgmem : g ∈ gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    mem_gramSU_iff.mpr ⟨fun u v => by
      rw [hgc, hYv, hYv, hY]
      exact yMap_isometry hω3 hωq hσω hσc hc u v, by rw [hgc, hdet]⟩
  refine ⟨⟨g, hgmem⟩, orderOf_eq_prime ?_ ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mk, hgc, Subgroup.coe_one,
      Units.val_one, ← map_pow, hY, yMap_cube hω3 hωq hc, map_one]
  · intro h
    have h1 := congrArg (fun g : gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =>
      E.symm ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h
    simp only [hgc, AlgEquiv.symm_apply_apply, Subgroup.coe_one, Units.val_one, map_one] at h1
    rw [hY] at h1
    exact yMap_ne_one hω0 hc h1
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Subgroup.coe_mk, hgc,
      ← hSdef]
    refine ext_iff_mulVec.mpr fun v => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hYv, hYv, hY, yMap_commute hSx hSiso]

theorem mk_injective_PU : Function.Injective
    (QuotientGroup.mk' (normOneScalars hK
      (gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) 5)) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', normOneScalars_eq_bot])

theorem exists_orthogonal_order_three :
    ∃ y : matrixIsometryGroup ((1 : GL (Fin 5) hK.fixedField) :
      Matrix (Fin 5) (Fin 5) hK.fixedField), orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : GL (Fin 5) hK.fixedField := TauCeti.permutationGL c5 with hP
  have hPm : (P : Matrix (Fin 5) (Fin 5) hK.fixedField) = c5⁻¹.permMatrix hK.fixedField :=
    TauCeti.permutationGL_coe c5
  have hmem : P ∈ matrixIsometryGroup ((1 : GL (Fin 5) hK.fixedField) :
      Matrix (Fin 5) (Fin 5) hK.fixedField) := by
    change (P : Matrix (Fin 5) (Fin 5) hK.fixedField)ᵀ *
      ((1 : GL (Fin 5) hK.fixedField) : Matrix (Fin 5) (Fin 5) hK.fixedField) *
        (P : Matrix (Fin 5) (Fin 5) hK.fixedField) =
      ((1 : GL (Fin 5) hK.fixedField) : Matrix (Fin 5) (Fin 5) hK.fixedField)
    rw [Units.val_one, Matrix.mul_one, hPm, transpose_permMatrix, ← permMatrix_mul,
      mul_inv_cancel, permMatrix_one]
  refine ⟨⟨P, hmem⟩, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mk, hP, ← map_pow, c5_pow_three, map_one,
      Subgroup.coe_one]
  · intro h
    have h1 := congrArg (fun g : matrixIsometryGroup ((1 : GL (Fin 5) hK.fixedField) :
      Matrix (Fin 5) (Fin 5) hK.fixedField) =>
        ((g : GL (Fin 5) hK.fixedField) : Matrix (Fin 5) (Fin 5) hK.fixedField) 0 0) h
    simp only [hPm, Subgroup.coe_one, Units.val_one, one_apply_eq] at h1
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, c5] at h1

theorem invFixThree_PU : InvFixThree PU := by
  intro β hβ
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ 2 ^ 3 = 2) := by norm_num
  obtain ⟨hcases, hinner, -, -⟩ := even_unitary_involution_matrix_lifts hK hC hn hq β hβ
  rcases hcases with hid | hbar
  · obtain ⟨s, -, hs2, hβs⟩ := hinner hid
    obtain ⟨y, hy3, hys⟩ := invCentThree_gramSU s (Subtype.ext hs2)
    refine ⟨(y : PU), ?_, ?_⟩
    · rw [← QuotientGroup.mk'_apply, orderOf_injective _ mk_injective_PU y]
      exact hy3
    · rw [hβs, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      change (s : GL (Fin 5) K) * y * (s : GL (Fin 5) K)⁻¹ = y
      rw [← Subgroup.coe_mul, ← hys, Subgroup.coe_mul, mul_inv_cancel_right]
  · obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
      even_unitary_antiunitary_involution_descent hK hC hn hq β hβ hbar
    have hC1 : (C₀ : Matrix (Fin 5) (Fin 5) K) = 1 := by
      rcases hcase₀ with h | ⟨r, hr, -⟩
      · exact h
      · omega
    have hCl : ((1 : GL (Fin 5) hK.fixedField) : Matrix (Fin 5) (Fin 5) hK.fixedField).map
        hK.fixedField.subtype = C₀ := by
      rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), hC1]
    obtain ⟨y₀, hy₀⟩ := exists_orthogonal_order_three
    refine ⟨θ (fixedIsometryProj hK hCl y₀), ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq, orderOf_injective _ (fixedIsometryProj_injective hK hCl hn), hy₀]
    · rw [hθβ, MulEquiv.symm_apply_apply, primeFormFieldAut_fixedIsometryProj hK hCl hC₀ hbar]

theorem invFixThree_projSU : InvFixThree (CFSG.Assembly.RankThreeEven.projSU 5 2 3) :=
  invFixThree_PU.of_mulEquiv (equivSUI.trans ePU.symm)

end CFSG.RankThree.PartTwo.Sec21.AS76.U58
