module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137Opp
public import CFSG.Quasithin.Vol2.Ch5Sec1L34U4Vertex
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

open scoped MatrixGroups

section T3

open CFSG.Quasithin.H13.U4Par CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

@[expose] def ixFour : Fin 4 ≃ Ix where
  toFun := ![ie1, if1, ie2, if2]
  invFun a := if a = ie1 then 0 else if a = if1 then 1 else if a = ie2 then 2 else 3
  left_inv i := by fin_cases i <;> decide
  right_inv a := by rcases ix_cases a with rfl | rfl | rfl | rfl <;> decide

theorem det_ix_of_col_row {K : Type} [Field K] {A : Matrix Ix Ix K}
    (hcol : ∀ a, a ≠ ie1 → A a ie1 = 0) (h11 : A ie1 ie1 = 1)
    (hrow : ∀ b, b ≠ if1 → A if1 b = 0) (h33 : A if1 if1 = 1) :
    A.det = A ie2 ie2 * A if2 if2 - A ie2 if2 * A if2 ie2 := by
  rw [← Matrix.det_submatrix_equiv_self ixFour, Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [ixFour, Fin.succAbove, hcol, hrow, h11, h33, Fin.lt_def]

theorem mem_parH_iff_fix {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (g : hypSU h 2 0) :
    g ∈ parH h ↔ ((g : GL Ix K) : Matrix Ix Ix K) *ᵥ Pi.single ie1 1 = Pi.single ie1 1 := by
  classical
  set A := ((g : GL Ix K) : Matrix Ix Ix K) with hA
  have hcolv : A *ᵥ Pi.single ie1 1 = fun a => A a ie1 := by
    funext a
    rw [Matrix.mulVec_single_one]
    rfl
  constructor
  · rintro ⟨hP, hχ, -⟩
    have hc := (mem_parP_iff h g).mp hP
    rw [hcolv]
    funext a
    by_cases ha : a = ie1
    · subst ha
      simpa [chi] using hχ
    · rw [Pi.single_eq_of_ne ha]
      exact hc a ha
  · intro hfix
    have hcol : ∀ a, a ≠ ie1 → A a ie1 = 0 := fun a ha => by
      have := congrFun hfix a
      rw [hcolv] at this
      simpa [Pi.single_eq_of_ne ha] using this
    have h11 : A ie1 ie1 = 1 := by
      have := congrFun hfix ie1
      rw [hcolv] at this
      simpa using this
    have hP : g ∈ parP h := (mem_parP_iff h g).mpr hcol
    obtain ⟨hrow, hdiag⟩ := row_if1_of_col h g hcol
    have h33 : A if1 if1 = 1 := by
      rw [← hA, h11, map_one, one_mul] at hdiag
      exact hdiag
    have hdet : A.det = 1 := (mem_gramSU.mp g.2).2
    refine ⟨hP, h11, ?_⟩
    rw [rho, Matrix.det_fin_two_of, ← hA, ← det_ix_of_col_row hcol h11 hrow h33]
    exact hdet

theorem rhoF_surjective {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) :
    Function.Surjective (rhoF h) := fun A =>
  ⟨⟨levHom h A, levHom_range_le_parH h ⟨A, rfl⟩⟩, rhoF_levHom h A⟩

theorem exists_vecStab_statedSU_four_equiv_hyp {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {w : Fin 4 → F} (hw0 : w ≠ 0)
    (hw : ∑ i, w i ^ (2 ^ n + 1) = 0) :
    ∃ h : UnitaryFieldData 2 n F,
      Nonempty (↥(KTabC.vecStab (StatedSU 4 (2 ^ n) F).subtype w) ≃*
        ↥(KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  have h : UnitaryFieldData 2 n F := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hF
  refine ⟨h, ?_⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 0)
  set e1 : Ix → F := Pi.single ie1 1 with he1
  set u : Fin (2 * 2 + 0) → F := R *ᵥ e1 with hu
  have hRinv : transportInv h R * R = 1 := transportInv_mul hR
  have hRinj : ∀ x y : Ix → F, R *ᵥ x = R *ᵥ y → x = y := by
    intro x y hxy
    have := congrArg (fun z => transportInv h R *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec] using this
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 : e1 = 0 := hRinj e1 0 (by rw [← hu, h0, Matrix.mulVec_zero])
    have := congrFun h1 ie1
    simp [he1] at this
  have huiso : CFSG.ComponentClassification.RankTwoClassical.hform h.bar u u = 0 := by
    have h1 := stdHermForm_transport hR e1 e1
    rw [hypForm_apply, sum_ix] at h1
    simp only [he1, hypPartner_ie1, hypPartner_ie2, hypPartner_if1, hypPartner_if2,
      Pi.single_eq_same, ne_eq, ie2_ne_ie1, if1_ne_ie1, if2_ne_ie1, not_false_eq_true,
      Pi.single_eq_of_ne, map_zero, map_one, zero_mul, mul_zero, add_zero] at h1
    have h2 : ∑ i, h.bar (u i) * u i = 0 := h1
    simpa [CFSG.ComponentClassification.RankTwoClassical.hform, dotProduct] using h2
  have hwiso : CFSG.ComponentClassification.RankTwoClassical.hform h.bar w w = 0 := by
    simp only [CFSG.ComponentClassification.RankTwoClassical.hform, dotProduct, Function.comp,
      h.bar_apply]
    rw [← hw]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g₀, hg₀⟩ := CFSG.ComponentClassification.RankTwoClassical.exists_statedSU_mulVec_eq h
    (by norm_num : 3 ≤ 4) hu0 huiso hw0 hwiso
  let φ := hypTransport h hR
  have e2 := vecStabEquivOfIff φ e1 u (fun g => by
    rw [coe_hypTransport, hu, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hRinv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    exact ⟨fun h1 => by rw [h1], fun h1 => hRinj _ _ h1⟩)
  have e3 := vecStabEquivOfIff (MulAut.conj g₀⁻¹) w u (fun g => by
    rw [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₀]
    constructor
    · intro h1
      rw [h1, ← hg₀, Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp
    · intro h1
      have := congrArg (fun z => ((g₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ z) h1
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left,
        hg₀] at this
      exact this)
  exact ⟨e3.trans e2.symm⟩

end T3

theorem exists_vecStab_SU4_iso_hom {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {w : Fin 4 → F} (hw0 : w ≠ 0)
    (hw : ∑ i, w i ^ (2 ^ n + 1) = 0) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Fintype K₀), Fintype.card K₀ = 2 ^ n ∧
      ∃ σ : ↥(KTabC.vecStab (StatedSU 4 (2 ^ n) F).subtype w) →* SL(2, K₀),
        Function.Surjective σ ∧ IsPGroup 2 σ.ker := by
  classical
  obtain ⟨h, ⟨e⟩⟩ := exists_vecStab_statedSU_four_equiv_hyp hF hw0 hw
  have hEq : KTabC.vecStab (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0).subtype
      (Pi.single CFSG.Quasithin.H13.U4Par.ie1 1) = CFSG.Quasithin.H13.U4Par.parH h := by
    ext g
    rw [mem_vecStab_subtype, mem_parH_iff_fix]
  have := h.finite
  haveI : Fintype h.fixedField := Fintype.ofFinite _
  refine ⟨h.fixedField, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, h.card_fixedField]
  let ι : ↥(KTabC.vecStab (StatedSU 4 (2 ^ n) F).subtype w) ≃* ↥(CFSG.Quasithin.H13.U4Par.parH h) :=
    e.trans (MulEquiv.subgroupCongr hEq)
  refine ⟨(CFSG.Quasithin.H13.U4Par.rhoF h).comp ι.toMonoidHom,
    (rhoF_surjective h).comp ι.surjective, ?_⟩
  have hk := (CFSG.Quasithin.H13.U4V.isPGroup_ker_rhoF h).comap_of_injective ι.toMonoidHom
    ι.injective
  rwa [MonoidHom.comap_ker] at hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
