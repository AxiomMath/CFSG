module

public import CFSG.RankThree.PartTwo.KFacts.KS21SylowMain
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U58

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts.KS21.DFT
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

abbrev PU := primeFormP hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem SUI_eq : SUI = gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  rw [Units.val_one]
  exact unitarySU_eq_gramSU hK 5

theorem normOneScalars_eq_bot :
    normOneScalars hK (gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) 5 = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, -, hc5, hg⟩
  have h63 : c ^ 63 = 1 := by rw [← card_units_K]; exact pow_card_eq_one'
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ Nat.gcd 5 63 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc5) (orderOf_dvd_of_pow_eq_one h63)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hdvd))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg, hc1, map_one]
  rfl

@[expose] def ePU : PU ≃* SUI :=
  ((QuotientGroup.quotientMulEquivOfEq normOneScalars_eq_bot).trans
    QuotientGroup.quotientBot).trans (MulEquiv.subgroupCongr SUI_eq.symm)

theorem coe_ePU_mk (g : gramSU hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :
    ((ePU (g : PU) : SUI) : GL (Fin 5) K) = g := rfl

@[expose] def fieldSUI (φ : K ≃+* K) : MulAut SUI :=
  (MulEquiv.subgroupCongr SUI_eq).trans
    ((primeFormFieldSU hK (isPrimeFormGram_one (n := 5)) φ).trans
      (MulEquiv.subgroupCongr SUI_eq.symm))

theorem coe_fieldSUI (φ : K ≃+* K) (g : SUI) :
    ((fieldSUI φ g : SUI) : GL (Fin 5) K) = glAut φ (g : GL (Fin 5) K) := rfl

theorem fieldSUI_mul (φ ψ : K ≃+* K) : fieldSUI (φ * ψ) = fieldSUI φ * fieldSUI ψ := by
  ext g : 2
  change glAut (φ * ψ) (g : GL (Fin 5) K) = glAut φ (glAut ψ (g : GL (Fin 5) K))
  rw [map_mul]
  rfl

theorem fieldSUI_one : fieldSUI 1 = 1 := by
  ext g : 2
  change glAut 1 (g : GL (Fin 5) K) = g
  rw [map_one]
  rfl

theorem fieldSUI_pow (φ : K ≃+* K) (m : ℕ) : fieldSUI φ ^ m = fieldSUI (φ ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, fieldSUI_one]
  | succ m ih => rw [pow_succ, ih, ← fieldSUI_mul, ← pow_succ]

theorem exists_unitary_field (α : MulAut SUI) :
    ∃ A ∈ primeFormUnitary hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K), ∃ φ : K ≃+* K,
      (∀ g : SUI, ((α g : SUI) : GL (Fin 5) K) = A * glAut φ (g : GL (Fin 5) K) * A⁻¹) ∧
      ∀ k : ℕ, α ^ 3 ^ k = 1 → φ ^ 3 ^ k = 1 := by
  have hC := isPrimeFormGram_one (n := 5) (K := K)
  obtain ⟨-, -, -, -, huniq, hff, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization hK hC (by norm_num) (by norm_num)
  set α' : MulAut PU := (MulAut.congr ePU.symm) α with hα'
  obtain ⟨φ, ⟨A, hαA⟩, -⟩ := huniq α'
  refine ⟨A, A.2, φ, fun g => ?_, fun k hk => ?_⟩
  · obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (ePU.symm g)
    have hgg' : (g : GL (Fin 5) K) = g' := by
      rw [← coe_ePU_mk, hg', MulEquiv.apply_symm_apply]
    have hα : α g = ePU (α' (ePU.symm g)) := by
      rw [hα', MulAut.congr_apply]
      simp
    rw [hα, ← hg', hαA, MulAut.mul_apply]
    change ((ePU (primeFormConjAut hK _ A (primeFormFieldAut hK hC φ (g' : PU))) : SUI) :
      GL (Fin 5) K) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk, coe_ePU_mk, hgg']
    rfl
  · have h1 : α' ^ 3 ^ k = 1 := by rw [hα', ← map_pow, hk, map_one]
    have := congrArg (primeFormFieldFactor hK hC (by norm_num) (by norm_num)) h1
    rwa [map_pow, hαA, hff, map_one] at this

theorem det_pow_nine_of_mem {A : GL (Fin 5) K}
    (hA : A ∈ primeFormUnitary hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :
    GeneralLinearGroup.det A ^ 9 = 1 := by
  have h := congrArg Matrix.det (mem_primeFormUnitary.mp hA)
  rw [Units.val_one, Matrix.mul_one, det_mul, det_transpose, det_one] at h
  have hmap : ((A : Matrix (Fin 5) (Fin 5) K).map hK.bar).det =
      (A : Matrix (Fin 5) (Fin 5) K).det ^ 8 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, UnitaryFieldData.bar_apply]
    norm_num
  rw [hmap] at h
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one, pow_succ]
  exact h

theorem exists_SUI_conj_eq {A : GL (Fin 5) K}
    (hA : A ∈ primeFormUnitary hK ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :
    ∃ g₀ : SUI, ∀ x : GL (Fin 5) K,
      A * x * A⁻¹ = (g₀ : GL (Fin 5) K) * x * (g₀ : GL (Fin 5) K)⁻¹ := by
  set d := GeneralLinearGroup.det A with hd
  have hd9 := det_pow_nine_of_mem hA
  set c : Kˣ := (d ^ 2)⁻¹ with hc
  have hc9 : c ^ 9 = 1 := by
    rw [hc, inv_pow, ← pow_mul, mul_comm 2 9, pow_mul, hd9, one_pow, inv_one]
  set A' := GeneralLinearGroup.scalar (Fin 5) c * A with hA'
  have hcoe : ((A' : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (c : K) • (A : Matrix (Fin 5) (Fin 5) K) := by
    rw [hA', Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, smul_eq_diagonal_mul]
  have hA'mem : A' ∈ SUI := by
    rw [mem_unitarySU_iff hK]
    constructor
    · rw [← GeneralLinearGroup.val_det_apply, hA', map_mul, GeneralLinearGroup.det_scalar,
        Fintype.card_fin, ← hd, hc, inv_pow, ← pow_mul,
        show d ^ (2 * 5) = d ^ 9 * d by rw [← pow_succ], hd9, one_mul, inv_mul_cancel,
        Units.val_one]
    · have hU : ((A : Matrix (Fin 5) (Fin 5) K).map hK.bar)ᵀ * (A : Matrix (Fin 5) (Fin 5) K) =
          1 := by
        have := mem_primeFormUnitary.mp hA
        rwa [Units.val_one, Matrix.mul_one] at this
      have hbar : ((c : K) • (A : Matrix (Fin 5) (Fin 5) K)).map hK.bar =
          hK.bar (c : K) • (A : Matrix (Fin 5) (Fin 5) K).map hK.bar := by
        ext i j
        simp [map_mul]
      have hcc : hK.bar (c : K) * c = 1 := by
        rw [UnitaryFieldData.bar_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
          show 2 ^ 3 + 1 = 9 from rfl, hc9, Units.val_one]
      rw [hcoe, hbar, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU, hcc,
        one_smul]
  refine ⟨⟨A', hA'mem⟩, fun x => ?_⟩
  have hcen : GeneralLinearGroup.scalar (Fin 5) c ∈ Subgroup.center (GL (Fin 5) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hcen
  change A * x * A⁻¹ = A' * x * A'⁻¹
  rw [hA', _root_.mul_inv_rev]
  calc A * x * A⁻¹ = A * x * A⁻¹ * GeneralLinearGroup.scalar (Fin 5) c *
        (GeneralLinearGroup.scalar (Fin 5) c)⁻¹ := by rw [mul_inv_cancel_right]
    _ = GeneralLinearGroup.scalar (Fin 5) c * (A * x * A⁻¹) *
        (GeneralLinearGroup.scalar (Fin 5) c)⁻¹ := by rw [hcomm (A * x * A⁻¹)]
    _ = _ := by simp only [mul_assoc]

theorem card_ringAut_K : Nat.card (K ≃+* K) = 6 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := K) Nat.prime_two (n := 6) (by norm_num) (by rw [card_K]; norm_num)
  exact hcard

theorem ringAut_pow_three {φ : K ≃+* K} {k : ℕ} (h : φ ^ 3 ^ k = 1) : φ ^ 3 = 1 := by
  have h6 : φ ^ 6 = 1 := by rw [← card_ringAut_K]; exact pow_card_eq_one'
  have hdvd : orderOf φ ∣ Nat.gcd (3 ^ k) 6 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h6)
  have hg : Nat.gcd (3 ^ k) 6 ∣ 3 := by
    have hcop : Nat.Coprime (Nat.gcd (3 ^ k) 6) 2 :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
        (Nat.Coprime.pow_left k (by norm_num))
    exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
  exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans hg)

theorem ringAut_fix_cube_root {φ : K ≃+* K} (h3 : φ ^ 3 = 1) {x : K} (hx : x ^ 3 = 1) :
    φ x = x := by
  by_cases h1 : x = 1
  · rw [h1, map_one]
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hq : x ^ 2 + x + 1 = 0 := by
    have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left hx1
  have hφq : (φ x) ^ 2 + φ x + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one φ, ← map_add, hq, map_zero]
  have hroots : (φ x - x) * (φ x - x ^ 2) = 0 := by linear_combination hφq - (φ x) * hq + hx
  rcases mul_eq_zero.mp hroots with h | h
  · linear_combination h
  · exfalso
    have h' : φ x = x ^ 2 := by linear_combination h
    have hφ3 : φ (φ (φ x)) = x := by
      have := congrArg (fun ψ : K ≃+* K => ψ x) h3
      simpa [pow_succ] using this
    have hφ2 : φ (φ x) = x := by
      rw [h', map_pow, h', ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx, one_mul]
    rw [hφ2, h'] at hφ3
    have : x * (x - 1) = 0 := by linear_combination hφ3
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [h0] at hx
      norm_num at hx
    · exact hx1 h0

@[expose] def ζ9 : Kˣ := exists_zeta_data.choose

theorem orderOf_ζ9 : orderOf ζ9 = 9 := exists_zeta_data.choose_spec.1

theorem ζ9_pow_nine : ζ9 ^ 9 = 1 := exists_zeta_data.choose_spec.2.1

@[expose] def τS : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* SUI :=
  (emb5.comp (tau9 ζ9_pow_nine)).codRestrict SUI (emb5_tau9_mem ζ9_pow_nine)

@[expose] def wS : SUI := ⟨emb5 (permGL3, 1), emb5_permGL3_mem⟩

theorem τS_injective : Function.Injective τS := fun _ _ h =>
  tau9_injective ζ9_pow_nine orderOf_ζ9 (emb5_injective (congrArg Subtype.val h))

theorem wS_pow_three : wS ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  change emb5 ((permGL3, 1) : GL (Fin 3) K × Kˣ) ^ 3 = 1
  rw [← map_pow, permGL3_one_pow_three, map_one])

theorem wS_mul_τS (v : (Fin 3 → ZMod 9) × ZMod 9) :
    wS * τS (.ofAdd v) = τS (.ofAdd (rot9 v)) * wS := Subtype.ext (by
  change emb5 ((permGL3, 1) : GL (Fin 3) K × Kˣ) * emb5 (tau9 ζ9_pow_nine (.ofAdd v)) =
    emb5 (tau9 ζ9_pow_nine (.ofAdd (rot9 v))) * emb5 ((permGL3, 1) : GL (Fin 3) K × Kˣ)
  rw [← map_mul, ← map_mul, permGL3_mul_tau9])

abbrev P₀ : Subgroup SUI := torusExt rot9 τS wS wS_pow_three wS_mul_τS

abbrev A₀ : Subgroup SUI := torusOmega τS

theorem exists_sylow_P₀ : ∃ P : Sylow 3 SUI, (P : Subgroup SUI) = P₀ :=
  exists_sylow_torusExt τS_injective wS_pow_three wS_mul_τS rot9_ne card_V9 card_SUI
    (by norm_num)

theorem card_A₀ : Nat.card A₀ = 3 ^ 4 := by
  rw [card_torusOmega τS_injective, card_V9_three]

theorem A₀_le_P₀ : A₀ ≤ P₀ := by
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, 0, by rw [pow_zero, mul_one]⟩

@[expose] def e5 (t : Fin 3 → Kˣ) (b : Kˣ) : Fin 5 → Kˣ :=
  ![t 0, t 1, t 2, b, (t 0 * t 1 * t 2 * b)⁻¹]

theorem det_diagGL3 (t : Fin 3 → Kˣ) :
    GeneralLinearGroup.det (TauCeti.diagGL t) = t 0 * t 1 * t 2 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_three]
  simp

theorem emb5_diagGL (t : Fin 3 → Kˣ) (b : Kˣ) :
    emb5 (TauCeti.diagGL t, b) = TauCeti.diagGL (e5 t b) := by
  apply Units.ext
  rw [coe_emb5, TauCeti.diagGL_coe, blk5]
  simp only [det_diagGL3, TauCeti.diagGL_coe]
  rw [fromBlocks_diagonal, reindex_apply, submatrix_diagonal_equiv]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem coe_τS (u : Fin 3 → ZMod 9) (d : ZMod 9) :
    ((τS (.ofAdd (u, d)) : SUI) : GL (Fin 5) K) =
      TauCeti.diagGL (e5 (fun i => ζ9 ^ (u i).val) (ζ9 ^ d.val)) := by
  change emb5 (tau9 ζ9_pow_nine (.ofAdd (u, d))) = _
  rw [tau9_apply, emb5_diagGL]

@[expose] def c5 : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩

theorem coe_wS : ((wS : SUI) : GL (Fin 5) K) = TauCeti.permutationGL c5 := by
  apply Units.ext
  rw [TauCeti.permutationGL_coe]
  change blk5 (permGL3, 1) = _
  have hdet : GeneralLinearGroup.det (permGL3 : GL (Fin 3) K) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_permGL3, det_permMat3, Units.val_one])
  rw [blk5]
  simp only [hdet, one_mul, inv_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reindex_apply, coe_permGL3, permMat3,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, c5] <;> rfl

theorem exists_pow_eq_of_pow_nine {t : Kˣ} (ht : t ^ 9 = 1) : ∃ i < 9, ζ9 ^ i = t := by
  have hprim : IsPrimitiveRoot (ζ9 : K) 9 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← orderOf_ζ9]
    exact IsPrimitiveRoot.orderOf ζ9
  obtain ⟨i, hi, hζ⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (t : K))
    (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])
  exact ⟨i, hi, Units.ext (by rw [Units.val_pow_eq_pow_val, hζ])⟩

theorem exists_τS_of_diag (x : SUI) {t : Fin 5 → Kˣ}
    (hx : (x : GL (Fin 5) K) = TauCeti.diagGL t) : ∃ v, τS v = x := by
  have hmem := (mem_unitarySU_iff hK).mp x.2
  rw [hx, TauCeti.diagGL_coe] at hmem
  obtain ⟨hdet, hunit⟩ := hmem
  rw [det_diagonal, Fin.prod_univ_five] at hdet
  have h9 : ∀ i, t i ^ 9 = 1 := by
    intro i
    have := congrFun₂ hunit i i
    rw [diagonal_map (map_zero hK.bar), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq, UnitaryFieldData.bar_apply] at this
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    simpa using this
  choose m hm hmt using fun i => exists_pow_eq_of_pow_nine (h9 i)
  refine ⟨.ofAdd (![(m 0 : ZMod 9), (m 1 : ZMod 9), (m 2 : ZMod 9)], (m 3 : ZMod 9)), ?_⟩
  apply Subtype.ext
  rw [coe_τS, hx]
  congr 1
  have hv : ∀ i, ζ9 ^ ((m i : ZMod 9)).val = t i := fun i => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hm i), hmt]
  funext i
  fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · show (ζ9 ^ ((m 0 : ZMod 9)).val * ζ9 ^ ((m 1 : ZMod 9)).val * ζ9 ^ ((m 2 : ZMod 9)).val *
      ζ9 ^ ((m 3 : ZMod 9)).val)⁻¹ = t 4
    rw [hv 0, hv 1, hv 2, hv 3, inv_eq_iff_mul_eq_one]
    apply Units.ext
    simpa [mul_assoc] using hdet

theorem glAut_diagGL (φ : K ≃+* K) (t : Fin 5 → Kˣ) :
    glAut φ (TauCeti.diagGL t) = TauCeti.diagGL (fun i => Units.map (φ : K →* K) (t i)) := by
  apply Units.ext
  rw [coe_glAut, TauCeti.diagGL_coe, TauCeti.diagGL_coe, diagonal_map (map_zero φ)]
  rfl

theorem glAut_permutationGL (φ : K ≃+* K) (σ : Equiv.Perm (Fin 5)) :
    glAut φ (TauCeti.permutationGL (k := K) σ) = TauCeti.permutationGL σ := by
  apply Units.ext
  rw [coe_glAut, TauCeti.permutationGL_coe]
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem fieldSUI_wS (φ : K ≃+* K) : fieldSUI φ wS = wS :=
  Subtype.ext (by rw [coe_fieldSUI, coe_wS, glAut_permutationGL])

theorem fieldSUI_τS (φ : K ≃+* K) (v) : ∃ v', τS v' = fieldSUI φ (τS v) := by
  obtain ⟨⟨u, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
  exact exists_τS_of_diag _ (by rw [coe_fieldSUI, coe_τS, glAut_diagGL])

theorem fieldSUI_P₀ (φ : K ≃+* K) : P₀.map (fieldSUI φ).toMonoidHom = P₀ := by
  have hle : P₀.map (fieldSUI φ).toMonoidHom ≤ P₀ := by
    rintro _ ⟨_, ⟨v, j, rfl⟩, rfl⟩
    obtain ⟨v', hv'⟩ := fieldSUI_τS φ (.ofAdd v)
    refine ⟨Multiplicative.toAdd v', j, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, map_mul, map_pow, fieldSUI_wS, ← hv']
    rfl
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (fieldSUI φ).injective).ge

theorem fieldSUI_A₀ {φ : K ≃+* K} (h3 : φ ^ 3 = 1) {a : SUI} (ha : a ∈ A₀) :
    fieldSUI φ a = a := by
  obtain ⟨⟨u, d⟩, hv3, rfl⟩ := ha
  apply Subtype.ext
  rw [coe_fieldSUI, coe_τS, glAut_diagGL]
  congr 1
  funext i
  have hcube : (τS (.ofAdd (u, d))) ^ 3 = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hv3, ofAdd_zero, map_one]
  have hcube' : TauCeti.diagGL (e5 (fun i => ζ9 ^ (u i).val) (ζ9 ^ d.val)) ^ 3 = 1 := by
    rw [← coe_τS, ← Subgroup.coe_pow, hcube, Subgroup.coe_one]
  rw [← map_pow] at hcube'
  have hi := congrFun (TauCeti.diagGL_injective (hcube'.trans (map_one _).symm)) i
  apply Units.ext
  rw [Units.coe_map]
  exact ringAut_fix_cube_root h3 (by
    rw [← Units.val_pow_eq_pow_val]
    simpa using congrArg Units.val hi)

instance nontrivial_units_K : Nontrivial Kˣ :=
  ⟨⟨ζ9, 1, fun h => by
    have := orderOf_ζ9
    rw [h, orderOf_one] at this
    norm_num at this⟩⟩

abbrev ND : Subgroup (GL (Fin 5) K) :=
  Subgroup.normalizer ((TauCeti.diagonalTorus K 5 : Subgroup (GL (Fin 5) K)) :
    Set (GL (Fin 5) K))

theorem diagGL_mul_perm_mem_ND (t : Fin 5 → Kˣ) (σ : Equiv.Perm (Fin 5)) :
    TauCeti.diagGL t * TauCeti.permutationGL (k := K) σ ∈ ND :=
  TauCeti.mem_normalizer_diagonalTorus_iff_exists.mpr ⟨t, σ, rfl⟩

theorem permOf_eq {x : ND} {t : Fin 5 → Kˣ} {σ : Equiv.Perm (Fin 5)}
    (h : (x : GL (Fin 5) K) = TauCeti.diagGL t * TauCeti.permutationGL (k := K) σ) :
    TauCeti.diagonalNormalizerPerm (k := K) (n := 5) x = σ :=
  TauCeti.diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL x t σ h

@[expose] def ev (v : (Fin 3 → ZMod 9) × ZMod 9) : Fin 5 → Kˣ :=
  e5 (fun i => ζ9 ^ (v.1 i).val) (ζ9 ^ v.2.val)

theorem coe_τS' (v : (Fin 3 → ZMod 9) × ZMod 9) :
    ((τS (.ofAdd v) : SUI) : GL (Fin 5) K) = TauCeti.diagGL (ev v) := by
  obtain ⟨u, d⟩ := v
  exact coe_τS u d

theorem ζ9_pow_three_ne_one : ζ9 ^ 3 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by rw [orderOf_ζ9]; norm_num)

theorem ζ9_pow_three_ne_inv : ζ9 ^ 3 ≠ (ζ9 ^ 3)⁻¹ := by
  intro h
  have : ζ9 ^ 6 = 1 := by
    rw [show 6 = 3 + 3 from rfl, pow_add]
    nth_rewrite 2 [h]
    exact mul_inv_cancel _
  exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [orderOf_ζ9]; norm_num) this

theorem exists_sep (i j : Fin 5) (hij : i ≠ j) :
    ∃ v : (Fin 3 → ZMod 9) × ZMod 9, 3 • v = 0 ∧ ev v i ≠ ev v j := by
  have h30 : (3 : ZMod 9).val = 3 := rfl
  have h00 : (0 : ZMod 9).val = 0 := rfl
  let v0 : (Fin 3 → ZMod 9) × ZMod 9 := (![3, 0, 0], 0)
  let v1 : (Fin 3 → ZMod 9) × ZMod 9 := (![0, 3, 0], 0)
  let v2 : (Fin 3 → ZMod 9) × ZMod 9 := (![0, 0, 3], 0)
  have h3v : ∀ v : (Fin 3 → ZMod 9) × ZMod 9, (∀ k, 3 • v.1 k = 0) → 3 • v.2 = 0 →
      3 • v = 0 := fun v h1 h2 => Prod.ext (funext h1) h2
  have hv0 : 3 • v0 = 0 := h3v _ (fun k => by fin_cases k <;> decide) (by decide)
  have hv1 : 3 • v1 = 0 := h3v _ (fun k => by fin_cases k <;> decide) (by decide)
  have hv2 : 3 • v2 = 0 := h3v _ (fun k => by fin_cases k <;> decide) (by decide)
  have e0 : ev v0 = ![ζ9 ^ 3, 1, 1, 1, (ζ9 ^ 3)⁻¹] := by
    funext k; fin_cases k <;> simp [ev, e5, v0, h30, h00]
  have e1 : ev v1 = ![1, ζ9 ^ 3, 1, 1, (ζ9 ^ 3)⁻¹] := by
    funext k; fin_cases k <;> simp [ev, e5, v1, h30, h00]
  have e2 : ev v2 = ![1, 1, ζ9 ^ 3, 1, (ζ9 ^ 3)⁻¹] := by
    funext k; fin_cases k <;> simp [ev, e5, v2, h30, h00]
  have hA := ζ9_pow_three_ne_one
  have hB := ζ9_pow_three_ne_inv
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact ⟨v0, hv0, by rw [e0]; simpa using hA⟩
    | exact ⟨v0, hv0, by rw [e0]; simpa using hA.symm⟩
    | exact ⟨v0, hv0, by rw [e0]; simpa using hB⟩
    | exact ⟨v0, hv0, by rw [e0]; simpa using hB.symm⟩
    | exact ⟨v1, hv1, by rw [e1]; simpa using hA⟩
    | exact ⟨v1, hv1, by rw [e1]; simpa using hA.symm⟩
    | exact ⟨v1, hv1, by rw [e1]; simpa using hB⟩
    | exact ⟨v1, hv1, by rw [e1]; simpa using hB.symm⟩
    | exact ⟨v2, hv2, by rw [e2]; simpa using hA⟩
    | exact ⟨v2, hv2, by rw [e2]; simpa using hA.symm⟩

theorem exists_monomial {g : SUI} (hg : ∀ a ∈ A₀, g * a * g⁻¹ ∈ A₀) :
    ∃ (d : Fin 5 → Kˣ) (σ : Equiv.Perm (Fin 5)),
      (g : GL (Fin 5) K) = TauCeti.diagGL d * TauCeti.permutationGL (k := K) σ := by
  refine TauCeti.exists_eq_diagGL_mul_permutationGL_of_forall_ne fun i j hij => ?_
  obtain ⟨v, hv3, hvij⟩ := exists_sep i j hij
  refine ⟨ev v, ?_, hvij⟩
  obtain ⟨b, -, hb⟩ := hg (τS (.ofAdd v)) ⟨v, hv3, rfl⟩
  have : (g : GL (Fin 5) K) * TauCeti.diagGL (ev v) * (g : GL (Fin 5) K)⁻¹ =
      TauCeti.diagGL (ev b) := by
    rw [← coe_τS', ← coe_τS', hb]
    rfl
  rw [this]
  exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨ev b, rfl⟩

theorem perm_check : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 →
    (σ * c5 * σ⁻¹ = c5 ∨ σ * c5 * σ⁻¹ = c5 ^ 2) → σ = 1 ∨ σ = c5 ∨ σ = c5 ^ 2 := by
  decide +kernel

theorem c5_ne_one : c5 ≠ 1 := by decide

theorem c5_pow_three : c5 ^ 3 = 1 := by decide

@[expose] def nprod (g : SUI) (F : MulAut SUI) : ℕ → SUI
  | 0 => 1
  | n + 1 => g * F (nprod g F n)

theorem conj_mul_pow (g : SUI) (F : MulAut SUI) (n : ℕ) :
    (MulAut.conj g * F) ^ n = MulAut.conj (nprod g F n) * F ^ n := by
  induction n with
  | zero => simp [nprod]
  | succ n ih =>
    have hF : F * MulAut.conj (nprod g F n) = MulAut.conj (F (nprod g F n)) * F := by
      rw [← mulAut_mul_conj_mul_inv F (nprod g F n), inv_mul_cancel_right]
    calc (MulAut.conj g * F) ^ (n + 1)
          = MulAut.conj g * F * (MulAut.conj (nprod g F n) * F ^ n) := by rw [pow_succ', ih]
      _ = MulAut.conj g * (F * MulAut.conj (nprod g F n)) * F ^ n := by simp only [mul_assoc]
      _ = MulAut.conj g * MulAut.conj (F (nprod g F n)) * (F * F ^ n) := by
          rw [hF]; simp only [mul_assoc]
      _ = MulAut.conj (nprod g F (n + 1)) * F ^ (n + 1) := by
          rw [nprod, map_mul, ← pow_succ']

theorem nprod_coe (g : SUI) (φ : K ≃+* K) {d : Fin 5 → Kˣ} {σ : Equiv.Perm (Fin 5)}
    (hg : (g : GL (Fin 5) K) = TauCeti.diagGL d * TauCeti.permutationGL (k := K) σ) (n : ℕ) :
    ∃ e : Fin 5 → Kˣ, ((nprod g (fieldSUI φ) n : SUI) : GL (Fin 5) K) =
      TauCeti.diagGL e * TauCeti.permutationGL (k := K) (σ ^ n) := by
  induction n with
  | zero => exact ⟨1, by rw [map_one, pow_zero, map_one, one_mul]; rfl⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨d * fun i => Units.map (φ : K →* K) (e (σ⁻¹ i)), ?_⟩
    have hperm : TauCeti.permutationGL (k := K) σ *
        TauCeti.diagGL (fun i => Units.map (φ : K →* K) (e i)) =
          TauCeti.diagGL (fun i => Units.map (φ : K →* K) (e (σ⁻¹ i))) *
            TauCeti.permutationGL (k := K) σ := by
      have h := TauCeti.permutationGL_mul_diagGL_mul_inv (k := K) σ
        (fun i => Units.map (φ : K →* K) (e i))
      rw [← h, inv_mul_cancel_right]
    change (g : GL (Fin 5) K) * glAut φ ((nprod g (fieldSUI φ) n : SUI) : GL (Fin 5) K) = _
    rw [hg, he, map_mul, glAut_diagGL, glAut_permutationGL, pow_succ', map_mul, map_mul]
    calc TauCeti.diagGL d * TauCeti.permutationGL σ *
          (TauCeti.diagGL (fun i => Units.map (φ : K →* K) (e i)) *
            TauCeti.permutationGL (σ ^ n))
        = TauCeti.diagGL d * (TauCeti.permutationGL σ *
            TauCeti.diagGL (fun i => Units.map (φ : K →* K) (e i))) *
              TauCeti.permutationGL (σ ^ n) := by simp only [mul_assoc]
      _ = _ := by rw [hperm]; simp only [mul_assoc]

theorem center_SUI : Subgroup.center SUI = ⊥ :=
  center_eq_bot_of_mulEquiv equivSUI center_projSU

theorem mem_P₀_of_conj_field {g : SUI} {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) {k : ℕ}
    (hk : (MulAut.conj g * fieldSUI φ) ^ 3 ^ (k + 1) = 1)
    (hP : P₀.map (MulAut.conj g * fieldSUI φ).toMonoidHom = P₀) : g ∈ P₀ := by
  have hFinv : (fieldSUI φ)⁻¹ = fieldSUI φ⁻¹ := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← fieldSUI_mul, inv_mul_cancel, fieldSUI_one]
  have hgP : P₀.map (MulAut.conj g).toMonoidHom = P₀ := by
    have h1 : MulAut.conj g = (MulAut.conj g * fieldSUI φ) * fieldSUI φ⁻¹ := by
      rw [← hFinv, mul_inv_cancel_right]
    rw [h1, show ((MulAut.conj g * fieldSUI φ) * fieldSUI φ⁻¹).toMonoidHom =
      (MulAut.conj g * fieldSUI φ).toMonoidHom.comp (fieldSUI φ⁻¹).toMonoidHom from rfl,
      ← Subgroup.map_map, fieldSUI_P₀, hP]
  obtain ⟨P0s, hP0s⟩ := exists_sylow_P₀
  have hA : A₀.map (MulAut.conj g).toMonoidHom = A₀ := by
    refine maxEA_SUI.2 P0s _ _ ?_ ?_ (isElemAbelian_map _ (isElemAbelian_torusOmega τS))
      (isElemAbelian_torusOmega τS) ?_ card_A₀
    · rw [hP0s, ← hgP]
      exact Subgroup.map_mono A₀_le_P₀
    · rw [hP0s]
      exact A₀_le_P₀
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_A₀]
  have hgA : ∀ a ∈ A₀, g * a * g⁻¹ ∈ A₀ := fun a ha => by
    rw [← hA]
    exact ⟨a, ha, rfl⟩
  obtain ⟨d, σ, hgdσ⟩ := exists_monomial hgA
  have hN : nprod g (fieldSUI φ) (3 ^ (k + 1)) = 1 := by
    have h1 := conj_mul_pow g (fieldSUI φ) (3 ^ (k + 1))
    have hF3 : fieldSUI φ ^ 3 ^ (k + 1) = 1 := by
      rw [fieldSUI_pow, pow_succ, mul_comm (3 ^ k) 3, pow_mul, hφ3, one_pow, fieldSUI_one]
    rw [hk, hF3, mul_one] at h1
    have hz : nprod g (fieldSUI φ) (3 ^ (k + 1)) ∈ Subgroup.center SUI := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun β : MulAut SUI => β y) h1
      simp only [MulAut.one_apply, MulAut.conj_apply] at this
      calc y * nprod g (fieldSUI φ) (3 ^ (k + 1)) =
          nprod g (fieldSUI φ) (3 ^ (k + 1)) * y * (nprod g (fieldSUI φ) (3 ^ (k + 1)))⁻¹ *
            nprod g (fieldSUI φ) (3 ^ (k + 1)) := by rw [← this]
        _ = _ := by rw [inv_mul_cancel_right]
    rw [center_SUI, Subgroup.mem_bot] at hz
    exact hz
  obtain ⟨e, he⟩ := nprod_coe g φ hgdσ (3 ^ (k + 1))
  have hσk : σ ^ 3 ^ (k + 1) = 1 := by
    rw [hN] at he
    have h1 := permOf_eq (x := (1 : ND)) (t := e) (σ := σ ^ 3 ^ (k + 1)) he
    rw [map_one] at h1
    exact h1.symm
  have hσ3 : σ ^ 3 = 1 := by
    have h120 : σ ^ 120 = 1 := by
      have := pow_card_eq_one' (G := Equiv.Perm (Fin 5)) (x := σ)
      rwa [Nat.card_perm, Nat.card_fin] at this
    have hdvd : orderOf σ ∣ Nat.gcd (3 ^ (k + 1)) 120 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one h120)
    have hg3 : Nat.gcd (3 ^ (k + 1)) 120 ∣ 3 := by
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (Nat.gcd_dvd_left _ _)
      rw [hjeq]
      have h120' : 3 ^ j ∣ 120 := hjeq ▸ Nat.gcd_dvd_right _ _
      have hj1 : j ≤ 1 := by
        by_contra hj1
        have : 3 ^ 2 ∣ 120 := (pow_dvd_pow 3 (by omega)).trans h120'
        norm_num at this
      exact (pow_dvd_pow 3 hj1).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans hg3)
  have hgw : g * wS * g⁻¹ ∈ P₀ := by
    rw [← hgP]
    exact ⟨wS, ⟨0, 1, by rw [ofAdd_zero, map_one, one_mul, pow_one]⟩, rfl⟩
  obtain ⟨v, j, hvj⟩ := hgw
  have hgN : (g : GL (Fin 5) K) ∈ ND := hgdσ ▸ diagGL_mul_perm_mem_ND d σ
  have hwN : (wS : GL (Fin 5) K) ∈ ND := coe_wS ▸ TauCeti.permutationGL_mem_normalizer c5
  set gN : ND := ⟨(g : GL (Fin 5) K), hgN⟩
  set wN : ND := ⟨(wS : GL (Fin 5) K), hwN⟩
  have hpg : TauCeti.diagonalNormalizerPerm (k := K) (n := 5) gN = σ := permOf_eq hgdσ
  have hpw : TauCeti.diagonalNormalizerPerm (k := K) (n := 5) wN = c5 :=
    permOf_eq (t := 1) (by rw [map_one, one_mul]; exact coe_wS)
  have hconj : TauCeti.diagonalNormalizerPerm (k := K) (n := 5) (gN * wN * gN⁻¹) = c5 ^ j := by
    apply permOf_eq (t := ev (Multiplicative.toAdd (Multiplicative.ofAdd v)))
    change ((g * wS * g⁻¹ : SUI) : GL (Fin 5) K) = _
    rw [hvj, Subgroup.coe_mul, Subgroup.coe_pow, coe_τS', coe_wS, ← map_pow]
    rfl
  rw [map_mul, map_mul, map_inv, hpg, hpw] at hconj
  have hj : σ * c5 * σ⁻¹ = c5 ∨ σ * c5 * σ⁻¹ = c5 ^ 2 := by
    have hjm : c5 ^ j = c5 ^ (j % 3) := pow_eq_pow_mod j c5_pow_three
    rw [hjm] at hconj
    have hj3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (j % 3)
    · exfalso
      rw [pow_zero, mul_inv_eq_one, mul_eq_left] at hconj
      exact c5_ne_one hconj
    · left; rw [hconj, pow_one]
    · right; exact hconj
  obtain ⟨m, hm⟩ : ∃ m : ℕ, σ = c5 ^ m := by
    rcases perm_check σ hσ3 hj with h | h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  have hdiag : ((g * (wS ^ m)⁻¹ : SUI) : GL (Fin 5) K) = TauCeti.diagGL d := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, coe_wS, hgdσ, hm, ← map_pow,
      mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨v', hv'⟩ := exists_τS_of_diag _ hdiag
  have : g = τS v' * wS ^ m := by rw [hv', inv_mul_cancel_right]
  rw [this]
  exact ⟨Multiplicative.toAdd v', m, rfl⟩

theorem autThree_of_sylow {M : Type} [Group M] [Finite M] {n : ℕ} (hmax : MaxEA M n)
    (P₀s : Sylow 3 M) (A₀ : Subgroup M) (hA₀P : A₀ ≤ P₀s) (hA₀ : IsElemAbelian 3 A₀)
    (hA₀c : Nat.card A₀ = 3 ^ n)
    (h₀ : ∀ α : MulAut M, (∃ k : ℕ, α ^ 3 ^ k = 1) →
      (P₀s : Subgroup M).map α.toMonoidHom = P₀s →
        ∃ p ∈ (P₀s : Subgroup M), ∃ φ : MulAut M, φ ^ 3 = 1 ∧ (∀ a ∈ A₀, φ a = a) ∧
          α = MulAut.conj p * φ) : AutThree M n := by
  intro P A hAP hA hAc α hα hαP
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M P₀s P
  have hPeq : (P : Subgroup M) = (P₀s : Subgroup M).map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨(MulAut.conj h)⁻¹ • x, hx, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
      exact hy
  have hAeq : A = A₀.map (MulAut.conj h).toMonoidHom := by
    refine hmax.2 P _ _ hAP ?_ hA (isElemAbelian_map _ hA₀) hAc ?_
    · rw [hPeq]
      exact Subgroup.map_mono hA₀P
    · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hA₀c]
  set β := (MulAut.conj h)⁻¹ * α * MulAut.conj h with hβ
  have hβk : ∃ k : ℕ, β ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hα
    refine ⟨k, ?_⟩
    have hβ' : β = MulAut.conj ((MulAut.conj h)⁻¹) α := by rw [hβ, MulAut.conj_apply, inv_inv]
    rw [hβ', ← map_pow, hk, map_one]
  have hβP : (P₀s : Subgroup M).map β.toMonoidHom = P₀s := by
    have h1 : (P₀s : Subgroup M).map β.toMonoidHom = (((P₀s : Subgroup M).map
        (MulAut.conj h).toMonoidHom).map α.toMonoidHom).map (MulAut.conj h)⁻¹.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, ← hPeq, hαP, hPeq, Subgroup.map_map]
    convert Subgroup.map_id (P₀s : Subgroup M)
    ext x
    simp [mul_assoc]
  obtain ⟨p, hp, φ, hφ3, hφA, hβφ⟩ := h₀ β hβk hβP
  refine ⟨h * p * h⁻¹, ?_, MulAut.conj h * φ * (MulAut.conj h)⁻¹, ?_, ?_, ?_⟩
  · rw [hPeq]
    exact ⟨p, hp, rfl⟩
  · rw [conj_pow, hφ3, mul_one, mul_inv_cancel]
  · intro a ha
    rw [hAeq] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    simp only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom]
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hφA a₀ ha₀]
  · have hα : α = MulAut.conj h * β * (MulAut.conj h)⁻¹ := by
      rw [hβ]
      group
    rw [hα, hβφ, map_mul, map_mul, map_inv]
    group

theorem autThree_SUI : AutThree SUI 4 := by
  obtain ⟨P0s, hP0s⟩ := exists_sylow_P₀
  refine autThree_of_sylow maxEA_SUI P0s A₀ (hP0s ▸ A₀_le_P₀) (isElemAbelian_torusOmega τS)
    card_A₀ fun α hα hαP => ?_
  rw [hP0s] at hαP ⊢
  obtain ⟨A, hA, φ, hαg, hφk⟩ := exists_unitary_field α
  obtain ⟨g₀, hg₀⟩ := exists_SUI_conj_eq hA
  have hαeq : α = MulAut.conj g₀ * fieldSUI φ := by
    ext x : 2
    rw [hαg, hg₀]
    rfl
  obtain ⟨k, hk⟩ := hα
  have hk' : α ^ 3 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  have hφ3 := ringAut_pow_three (hφk (k + 1) hk')
  rw [hαeq] at hk' hαP
  exact ⟨g₀, mem_P₀_of_conj_field hφ3 hk' hαP, fieldSUI φ,
    by rw [fieldSUI_pow, hφ3, fieldSUI_one], fun a ha => fieldSUI_A₀ hφ3 ha, hαeq⟩

theorem autThree_projSU : AutThree (projSU 5 2 3) 4 := autThree_SUI.of_mulEquiv equivSUI.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.U58
