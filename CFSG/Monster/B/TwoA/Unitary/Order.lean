module

public import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.Unitary.Simple
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  mul_bar_of_ne_zero)

theorem hF4 : UnitaryFieldData 2 1 F4 := CFSG.LinearGroups.unitaryFieldData_F4

theorem hF4_bar (c : F4) : hF4.bar c = bar c := by
  rw [UnitaryFieldData.bar_apply]
  rfl

abbrev SUI : Subgroup (GL (Fin 6) F4) := unitarySU 2 1 F4 6

theorem map_hF4_bar (A : Matrix (Fin 6) (Fin 6) F4) : A.map hF4.bar = barM A := by
  ext i j
  exact hF4_bar _

theorem mem_SUI_iff {A : GL (Fin 6) F4} :
    A ∈ SUI ↔ (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      (barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ * (A : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  rw [mem_unitarySU_iff hF4, map_hF4_bar]

theorem mem_SUI_iff' {A : GL (Fin 6) F4} :
    A ∈ SUI ↔ (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      (A : Matrix (Fin 6) (Fin 6) F4) * (barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ = 1 := by
  rw [mem_SUI_iff]
  exact and_congr_right fun _ => ⟨fun h => mul_eq_one_comm.1 h, fun h => mul_eq_one_comm.1 h⟩

@[expose] def w2 : F4 := ⟨3⟩

@[expose] def Bm : Matrix (Fin 6) (Fin 6) F4 :=
  !![1, 0, 0, F4.ω, 0, 0; 0, 1, 0, 0, F4.ω, 0; 0, 0, 1, 0, 0, F4.ω;
    1, 0, 0, w2, 0, 0; 0, 1, 0, 0, w2, 0; 0, 0, 1, 0, 0, w2]

@[expose] def Bminv : Matrix (Fin 6) (Fin 6) F4 :=
  !![w2, 0, 0, F4.ω, 0, 0; 0, w2, 0, 0, F4.ω, 0; 0, 0, w2, 0, 0, F4.ω;
    1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1]

@[expose] def Pim : Matrix (Fin 6) (Fin 6) F4 :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]

theorem Bm_mul_Bminv : Bm * Bminv = 1 := by decide +kernel

theorem Bminv_mul_Bm : Bminv * Bm = 1 := by decide +kernel

theorem Bm_gram : Bm * hGram * (barM Bm)ᵀ = 1 := by decide +kernel

theorem Bminv_gram : Bminv * (barM Bminv)ᵀ = hGram := by decide +kernel

theorem barM_Bm : barM Bm = Pim * Bm := by decide +kernel

theorem barM_Bminv : barM Bminv = Bminv * Pim := by decide +kernel

theorem Pim_mul_Pim : Pim * Pim = 1 := by decide +kernel

theorem barM_Pim : barM Pim = Pim := by decide +kernel

theorem Pim_transpose : Pimᵀ = Pim := by decide +kernel

theorem det_Pim : Pim.det = 1 := by decide +kernel

theorem det_Bm_mul : Bm.det * Bminv.det = 1 := by
  rw [← det_mul, Bm_mul_Bminv, det_one]

@[expose] def Bunit : GL (Fin 6) F4 := ⟨Bm, Bminv, Bm_mul_Bminv, Bminv_mul_Bm⟩

@[expose] def Piunit : GL (Fin 6) F4 := ⟨Pim, Pim, Pim_mul_Pim, Pim_mul_Pim⟩

theorem Piunit_mem : Piunit ∈ SUI := by
  rw [mem_SUI_iff']
  refine ⟨det_Pim, ?_⟩
  change Pim * (barM Pim)ᵀ = 1
  rw [barM_Pim, Pim_transpose, Pim_mul_Pim]

@[expose] def PiSU : SUI := ⟨Piunit, Piunit_mem⟩

theorem barM_transpose (A : Matrix (Fin 6) (Fin 6) F4) : barM Aᵀ = (barM A)ᵀ := rfl

theorem conj_mem_SUI {A : GL (Fin 6) F4} (hA : A ∈ SUh) : Bunit * A * Bunit⁻¹ ∈ SUI := by
  rw [mem_SUh_iff_gram] at hA
  rw [mem_SUI_iff']
  have hc : ((Bunit * A * Bunit⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Bm * (A : Matrix (Fin 6) (Fin 6) F4) * Bminv := rfl
  rw [hc]
  refine ⟨by rw [det_mul, det_mul, hA.1, mul_one, det_Bm_mul], ?_⟩
  rw [barM_mul, barM_mul, transpose_mul, transpose_mul]
  calc Bm * (A : Matrix (Fin 6) (Fin 6) F4) * Bminv *
        ((barM Bminv)ᵀ * ((barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ * (barM Bm)ᵀ))
      = Bm * ((A : Matrix (Fin 6) (Fin 6) F4) * (Bminv * (barM Bminv)ᵀ) *
          (barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ) * (barM Bm)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Bminv_gram, hA.2, Bm_gram]

theorem conj_inv_mem_SUh {A : GL (Fin 6) F4} (hA : A ∈ SUI) : Bunit⁻¹ * A * Bunit ∈ SUh := by
  rw [mem_SUI_iff'] at hA
  rw [mem_SUh_iff_gram]
  have hc : ((Bunit⁻¹ * A * Bunit : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Bminv * (A : Matrix (Fin 6) (Fin 6) F4) * Bm := rfl
  rw [hc]
  refine ⟨by rw [det_mul, det_mul, hA.1, mul_one, mul_comm, det_Bm_mul], ?_⟩
  rw [barM_mul, barM_mul, transpose_mul, transpose_mul]
  calc Bminv * (A : Matrix (Fin 6) (Fin 6) F4) * Bm * hGram *
        ((barM Bm)ᵀ * ((barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ * (barM Bminv)ᵀ))
      = Bminv * ((A : Matrix (Fin 6) (Fin 6) F4) * (Bm * hGram * (barM Bm)ᵀ) *
          (barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ) * (barM Bminv)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = hGram := by rw [Bm_gram, Matrix.mul_one, hA.2, Matrix.mul_one, Bminv_gram]

theorem map_SUh_conj : SUh.map (MulAut.conj Bunit).toMonoidHom = SUI := by
  ext A
  constructor
  · rintro ⟨N, hN, rfl⟩
    exact conj_mem_SUI hN
  · intro hA
    refine ⟨Bunit⁻¹ * A * Bunit, conj_inv_mem_SUh hA, ?_⟩
    change Bunit * (Bunit⁻¹ * A * Bunit) * Bunit⁻¹ = A
    group

@[expose] noncomputable def psiSU : SUh ≃* SUI :=
  ((MulAut.conj Bunit).subgroupMap SUh).trans (MulEquiv.subgroupCongr map_SUh_conj)

theorem coe_psiSU (g : SUh) :
    ((psiSU g : SUI) : GL (Fin 6) F4) = Bunit * (g : GL (Fin 6) F4) * Bunit⁻¹ := rfl

theorem scalar_conj (c : F4ˣ) :
    Bunit * GeneralLinearGroup.scalar (Fin 6) c * Bunit⁻¹ =
      GeneralLinearGroup.scalar (Fin 6) c := by
  rw [scalar_commute c Bunit, mul_inv_cancel_right]

theorem hF4_norm (c : F4ˣ) : hF4.norm (c : F4) = 1 := by
  rw [UnitaryFieldData.norm, hF4_bar]
  exact mul_bar_of_ne_zero c.ne_zero

theorem map_Zh : Zh.map psiSU.toMonoidHom = unitaryScalars hF4 6 := by
  ext g
  constructor
  · rintro ⟨z, ⟨c, hc⟩, rfl⟩
    refine ⟨c, hF4_norm c, ?_, ?_⟩
    · refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact pow_six_eq_one _ c.ne_zero
    · change ((psiSU z : SUI) : GL (Fin 6) F4) = _
      rw [coe_psiSU, hc, scalar_conj]
  · rintro ⟨c, -, -, hc⟩
    refine ⟨psiSU.symm g, ⟨c, ?_⟩, psiSU.apply_symm_apply g⟩
    have h1 : ((psiSU (psiSU.symm g) : SUI) : GL (Fin 6) F4) = (g : GL (Fin 6) F4) := by
      rw [psiSU.apply_symm_apply]
    rw [coe_psiSU, hc] at h1
    have h2 : ((psiSU.symm g : SUh) : GL (Fin 6) F4) =
        Bunit⁻¹ * GeneralLinearGroup.scalar (Fin 6) c * Bunit := by
      rw [← h1]
      group
    rw [h2, scalar_commute c Bunit⁻¹, inv_mul_cancel_right]

@[expose] noncomputable def psiQ : SUh ⧸ Zh ≃* unitaryPSU hF4 6 :=
  QuotientGroup.congr Zh (unitaryScalars hF4 6) psiSU map_Zh

theorem psiQ_mk (g : SUh) : psiQ (g : SUh ⧸ Zh) = (psiSU g : unitaryPSU hF4 6) := rfl

theorem natCard_F4 : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  norm_num

theorem hGram_hermitian : (hGram.map hF4.bar)ᵀ = hGram := by
  rw [map_hF4_bar]
  decide +kernel

theorem hGram_mul_self : hGram * hGram = 1 := by decide +kernel

theorem barM_hGram : barM hGram = hGram := by decide +kernel

theorem hGram_transpose : hGramᵀ = hGram := by decide +kernel

theorem det_hGram_ne_zero : hGram.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hGram_mul_self
  rw [det_mul, h0, zero_mul, det_one] at this
  exact zero_ne_one this

theorem natCard_gramSU : Nat.card (gramSU hF4 hGram) = 27590492160 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hF4 (gramForm_isSymm hF4 hGram_hermitian)
    (gramForm_separatingLeft hF4 det_hGram_ne_zero) (Module.finrank_fin_fun F4)
    (by norm_num)).2.1
  rw [card_gramSU]
  have e : ((2 ^ 1 : ℕ) : ℤ) ^ (6 * (6 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 27590492160 := by decide
  rw [e] at h
  exact_mod_cast h

@[expose] def trGL (A : GL (Fin 6) F4) : GL (Fin 6) F4 :=
  ⟨(A : Matrix (Fin 6) (Fin 6) F4)ᵀ, ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]⟩

theorem trGL_trGL (A : GL (Fin 6) F4) : trGL (trGL A) = A := Units.ext (transpose_transpose _)

theorem mem_SUh_iff_trGL (A : GL (Fin 6) F4) : A ∈ SUh ↔ trGL A ∈ gramSU hF4 hGram := by
  rw [mem_SUh_iff_gram, mem_gramSU]
  change _ ↔ (((A : Matrix (Fin 6) (Fin 6) F4)ᵀ.map hF4.bar)ᵀ * hGram *
    (A : Matrix (Fin 6) (Fin 6) F4)ᵀ = hGram ∧ ((A : Matrix (Fin 6) (Fin 6) F4)ᵀ).det = 1)
  rw [map_hF4_bar, det_transpose, and_comm]
  refine and_congr_left fun _ => ?_
  have key : ∀ X : Matrix (Fin 6) (Fin 6) F4, barM (X * hGram * (barM X)ᵀ) =
      (barM Xᵀ)ᵀ * hGram * Xᵀ := by
    intro X
    rw [barM_mul, barM_mul, barM_hGram, barM_transpose, barM_barM]
    rfl
  constructor
  · intro h
    rw [← key, h, barM_hGram]
  · intro h
    have := congrArg barM h
    rw [← key, barM_barM, barM_hGram] at this
    exact this

theorem natCard_SUh : Nat.card SUh = 27590492160 := by
  rw [← natCard_gramSU]
  refine Nat.card_congr (Equiv.subtypeEquiv ⟨trGL, trGL, trGL_trGL, trGL_trGL⟩ fun A => ?_)
  exact mem_SUh_iff_trGL A

@[expose] noncomputable def zhEquiv : F4ˣ ≃ Zh :=
  Equiv.ofBijective (fun c => ⟨⟨GeneralLinearGroup.scalar (Fin 6) c, scalar_mem_SUh c⟩, c, rfl⟩)
    ⟨fun c d h => by
      have h1 := congrArg (fun z : Zh => (((z : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
        0 0) h
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h1
      exact Units.ext h1,
    fun z => by
      obtain ⟨c, hc⟩ := z.2
      exact ⟨c, Subtype.ext (Subtype.ext hc.symm)⟩⟩

theorem natCard_Zh : Nat.card Zh = 3 := by
  rw [← Nat.card_congr zhEquiv, Nat.card_eq_fintype_card, Fintype.card_units, F4.card]

theorem natCard_quot : Nat.card (SUh ⧸ Zh) = 9196830720 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Zh
  rw [natCard_SUh, natCard_Zh] at h
  omega

theorem natCard_SigmaU6 : Nat.card SigmaU6 = 18393661440 := by
  rw [SemidirectProduct.card, natCard_quot, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))]
  rfl

theorem natCard_unitaryPSU : Nat.card (unitaryPSU hF4 6) = 9196830720 := by
  rw [← Nat.card_congr psiQ.toEquiv, natCard_quot]

theorem isSimpleGroup_unitaryPSU : IsSimpleGroup (unitaryPSU hF4 6) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 natCard_F4 6
    (by norm_num) (by decide)
  exact (unitaryPSUEquiv hF4 (n := 6) (by norm_num)).isSimpleGroup

theorem frobGL_mem_SUI {A : GL (Fin 6) F4} (hA : A ∈ SUI) : frobGL A ∈ SUI := by
  rw [mem_SUI_iff] at hA ⊢
  rw [coe_frobGL]
  refine ⟨by rw [det_barM, hA.1, bar_one], ?_⟩
  have := congrArg barM hA.2
  rw [barM_mul, barM_one, barM_transpose] at this
  exact this

@[expose] def frobSUI : SUI →* SUI where
  toFun g := ⟨frobGL g, frobGL_mem_SUI g.2⟩
  map_one' := Subtype.ext (map_one frobGL)
  map_mul' a b := Subtype.ext (map_mul frobGL (a : GL (Fin 6) F4) (b : GL (Fin 6) F4))

theorem frobSUI_frobSUI (g : SUI) : frobSUI (frobSUI g) = g := Subtype.ext (frobGL_frobGL _)

theorem unitaryScalars_le_comap : unitaryScalars hF4 6 ≤ (unitaryScalars hF4 6).comap frobSUI := by
  rintro g ⟨c, hc, hcn, hg⟩
  refine ⟨Units.map barHom.toMonoidHom c, ?_, ?_, ?_⟩
  · exact hF4_norm _
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_six_eq_one _ (Units.map barHom.toMonoidHom c).ne_zero
  · change frobGL (g : GL (Fin 6) F4) = _
    rw [hg, frobGL_scalar]

@[expose] def frobQI : MulAut (unitaryPSU hF4 6) where
  toFun := QuotientGroup.map _ _ frobSUI unitaryScalars_le_comap
  invFun := QuotientGroup.map _ _ frobSUI unitaryScalars_le_comap
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [QuotientGroup.map_mk, frobSUI_frobSUI]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [QuotientGroup.map_mk, frobSUI_frobSUI]
  map_mul' := map_mul _

theorem frobQI_mk (g : SUI) : frobQI (g : unitaryPSU hF4 6) = (frobSUI g : unitaryPSU hF4 6) := rfl

theorem frobQI_mul_self : frobQI * frobQI = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => simp [MulAut.mul_apply, frobQI_mk, frobSUI_frobSUI]

@[expose] def frobPowI (ε : ZMod 2) : MulAut (unitaryPSU hF4 6) := if ε = 0 then 1 else frobQI

theorem frobPowI_add (x y : ZMod 2) : frobPowI (x + y) = frobPowI x * frobPowI y := by
  rcases zmod2_cases' x with rfl | rfl <;> rcases zmod2_cases' y with rfl | rfl
  · simp [frobPowI]
  · simp [frobPowI]
  · simp [frobPowI]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
    simp only [frobPowI, ite_true, show ¬((1 : ZMod 2) = 0) by decide, ite_false,
      frobQI_mul_self]

@[expose] def frobHomI : Multiplicative (ZMod 2) →* MulAut (unitaryPSU hF4 6) where
  toFun ε := frobPowI (Multiplicative.toAdd ε)
  map_one' := ite_eq_left rfl
  map_mul' _ _ := frobPowI_add _ _

abbrev PSU62 : Type := unitaryPSU hF4 6 ⋊[frobHomI] Multiplicative (ZMod 2)

@[expose] noncomputable def tauI : PSU62 := ⟨(PiSU : unitaryPSU hF4 6), Multiplicative.ofAdd 1⟩

theorem frobSUI_PiSU : frobSUI PiSU = PiSU := Subtype.ext (Units.ext barM_Pim)

theorem PiSU_mul_self : PiSU * PiSU = 1 := Subtype.ext (Units.ext Pim_mul_Pim)

theorem tauI_mul_self : tauI * tauI = 1 := by
  refine SemidirectProduct.ext ?_ ?_
  · change (PiSU : unitaryPSU hF4 6) * frobPowI 1 (PiSU : unitaryPSU hF4 6) = 1
    rw [frobPowI, ite_eq_right (by decide), frobQI_mk, frobSUI_PiSU, ← QuotientGroup.mk_mul,
      PiSU_mul_self, QuotientGroup.mk_one]
  · rfl

@[expose] noncomputable def thetaG : Multiplicative (ZMod 2) →* PSU62 where
  toFun ε := if Multiplicative.toAdd ε = 0 then 1 else tauI
  map_one' := ite_eq_left rfl
  map_mul' a b := by
    induction a using Multiplicative.rec with
    | ofAdd x =>
    induction b using Multiplicative.rec with
    | ofAdd y =>
    rcases zmod2_cases' x with rfl | rfl <;> rcases zmod2_cases' y with rfl | rfl
    · simp
    · simp
    · simp
    · change (if (1 + 1 : ZMod 2) = 0 then 1 else tauI) =
        (if (1 : ZMod 2) = 0 then 1 else tauI) * (if (1 : ZMod 2) = 0 then 1 else tauI)
      rw [ite_eq_left (by decide : (1 + 1 : ZMod 2) = 0),
        ite_eq_right (by decide : ¬(1 : ZMod 2) = 0), tauI_mul_self]

@[expose] noncomputable def thetaN : SUh ⧸ Zh →* PSU62 :=
  SemidirectProduct.inl.comp psiQ.toMonoidHom

theorem Bunit_inv_val : ((Bunit⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Bminv := rfl

theorem psiSU_frobSU (g : SUh) :
    psiSU (frobSU g) = PiSU * frobSUI (psiSU g) * PiSU := by
  apply Subtype.ext
  apply Units.ext
  change Bm * barM (((g : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Bminv =
    Pim * barM (Bm * (((g : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Bminv) * Pim
  rw [barM_mul, barM_mul, barM_Bm, barM_Bminv]
  simp only [Matrix.mul_assoc]
  rw [Pim_mul_Pim, Matrix.mul_one, ← Matrix.mul_assoc Pim Pim, Pim_mul_Pim, Matrix.one_mul]

theorem theta_compat (g : Multiplicative (ZMod 2)) :
    thetaN.comp (frobHomU g).toMonoidHom = (MulAut.conj (thetaG g)).toMonoidHom.comp thetaN := by
  induction g using Multiplicative.rec with
  | ofAdd x =>
  refine MonoidHom.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
  rcases zmod2_cases' x with rfl | rfl
  · change thetaN (frobPowQ 0 (g : SUh ⧸ Zh)) =
      (if (0 : ZMod 2) = 0 then 1 else tauI) * thetaN (g : SUh ⧸ Zh) *
        (if (0 : ZMod 2) = 0 then 1 else tauI)⁻¹
    rw [frobPowQ_zero, ite_eq_left rfl, one_mul, inv_one, mul_one]
    rfl
  · change thetaN (frobPowQ 1 (g : SUh ⧸ Zh)) =
      (if (1 : ZMod 2) = 0 then 1 else tauI) * thetaN (g : SUh ⧸ Zh) *
        (if (1 : ZMod 2) = 0 then 1 else tauI)⁻¹
    rw [frobPowQ_one, ite_eq_right (by decide), frobQ_mk]
    have hinv : tauI⁻¹ = tauI := inv_eq_of_mul_eq_one_right tauI_mul_self
    rw [hinv]
    refine SemidirectProduct.ext ?_ ?_
    · change psiQ (frobSU g : SUh ⧸ Zh) =
        (PiSU : unitaryPSU hF4 6) * frobPowI 1 (psiQ (g : SUh ⧸ Zh)) *
          frobPowI 1 (PiSU : unitaryPSU hF4 6)
      rw [frobPowI, ite_eq_right (by decide), psiQ_mk, psiQ_mk, frobQI_mk, frobQI_mk,
        frobSUI_PiSU, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, psiSU_frobSU]
    · simp only [thetaN, MonoidHom.comp_apply, SemidirectProduct.mul_right,
        SemidirectProduct.right_inl, tauI]
      decide

@[expose] noncomputable def theta : SigmaU6 →* PSU62 :=
  SemidirectProduct.lift thetaN thetaG theta_compat

theorem theta_mk (q : SUh ⧸ Zh) (ε : ZMod 2) :
    theta ⟨q, Multiplicative.ofAdd ε⟩ =
      thetaN q * (if ε = 0 then 1 else tauI) := rfl

theorem theta_injective : Function.Injective theta := by
  rw [injective_iff_map_eq_one]
  rintro ⟨q, e⟩ h
  induction e using Multiplicative.rec with
  | ofAdd ε =>
  rw [theta_mk] at h
  rcases zmod2_cases' ε with rfl | rfl
  · rw [ite_eq_left rfl, mul_one] at h
    have h1 : psiQ q = 1 := congrArg SemidirectProduct.left h
    have hq : q = 1 := psiQ.injective (h1.trans (map_one psiQ).symm)
    rw [hq]
    rfl
  · rw [ite_eq_right (by decide)] at h
    have h2 := congrArg SemidirectProduct.right h
    simp only [thetaN, MonoidHom.comp_apply, SemidirectProduct.mul_right,
      SemidirectProduct.right_inl, tauI] at h2
    exact absurd h2 (by decide)

theorem natCard_PSU62 : Nat.card PSU62 = 18393661440 := by
  rw [SemidirectProduct.card, natCard_unitaryPSU, Nat.card_eq_fintype_card (α :=
    Multiplicative (ZMod 2))]
  rfl

instance finite_PSU62 : Finite PSU62 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_PSU62]; norm_num)

@[expose] noncomputable def thetaEquiv : SigmaU6 ≃* PSU62 :=
  MulEquiv.ofBijective theta (theta_injective.bijective_of_nat_card_le
    (by rw [natCard_PSU62, natCard_SigmaU6]))

end CFSG.Monster.B.TwoA.Unitary
