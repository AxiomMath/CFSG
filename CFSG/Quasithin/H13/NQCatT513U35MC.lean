module

public import CFSG.Quasithin.H13.NQCatT513U35Dec
public import CFSG.Quasithin.Vol2.KGFactAutSylowU35Syl
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.Quasithin.H13.NQCat.T513.U35

open U35Perm HNUnitaryBridge CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (ent Good f25Data suMat suMat_apply suMat_injective mem_SU)
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (Rm Sm RR SS coe_RR coe_SS RR_pow SS_sq SS_RR)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

abbrev PU : Type := unitaryPSU f25Data 3

abbrev SU : Subgroup (GL (Fin 3) F25) := unitarySU 5 1 F25 3

noncomputable abbrev proj : ↥SU →* PU := unitaryProj f25Data 3

theorem decMat_rCode : decMat (ent rCode) = Rm := by decide +kernel

theorem decMat_sCode : decMat (ent sCode) = Sm := by decide +kernel

theorem mem_tList {t : Array ℕ} : t ∈ tList ↔ ∃ i < 8,
    t = CFSG.Quasithin.H13.KGU35.mPow rCode i ∨
      t = CFSG.Quasithin.H13.KGU35.mMul (CFSG.Quasithin.H13.KGU35.mPow rCode i) sCode := by
  simp [tList]

theorem suMat_RR_SS (i e : ℕ) : suMat (RR ^ i * SS ^ e) = Rm ^ i * Sm ^ e := by
  rw [map_mul, map_pow, map_pow, suMat_apply, suMat_apply, coe_RR, coe_SS]

theorem decMat_of_mem_tList {t : Array ℕ} (ht : t ∈ tList) :
    ∃ i < 8, ∃ e < 2, decMat (ent t) = suMat (RR ^ i * SS ^ e) := by
  obtain ⟨i, hi, rfl | rfl⟩ := mem_tList.mp ht
  · refine ⟨i, hi, 0, by norm_num, ?_⟩
    rw [suMat_RR_SS, CFSG.Quasithin.H13.KGU35.decMat_mPow, decMat_rCode, pow_zero, mul_one]
  · refine ⟨i, hi, 1, by norm_num, ?_⟩
    rw [suMat_RR_SS, CFSG.Quasithin.H13.KGU35.decMat_mMul, CFSG.Quasithin.H13.KGU35.decMat_mPow,
      decMat_rCode, decMat_sCode, pow_one]

theorem exists_lift (t : Array ℕ) : ∃ g : ↥SU, t ∈ tList → suMat g = decMat (ent t) := by
  by_cases ht : t ∈ tList
  · obtain ⟨i, -, e, -, he⟩ := decMat_of_mem_tList ht
    exact ⟨_, fun _ => he.symm⟩
  · exact ⟨1, fun h => absurd h ht⟩

@[expose] noncomputable def lift (t : Array ℕ) : ↥SU := (exists_lift t).choose

@[expose] noncomputable def tT0 : Subgroup ↥SU := Subgroup.closure {RR, SS}

@[expose] noncomputable def T0 : Subgroup PU := tT0.map proj

@[expose] noncomputable def z0 : PU := proj (RR ^ 4)

theorem RR_pow_mod (n : ℕ) : RR ^ n = RR ^ (n % 8) := by
  conv_lhs => rw [← Nat.mod_add_div n 8, pow_add, pow_mul, RR_pow, one_pow, mul_one]

theorem SS_pow_mod (n : ℕ) : SS ^ n = SS ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, SS_sq, one_pow, mul_one]

theorem SS_mul_RR_pow (i : ℕ) : SS * RR ^ i = RR ^ (3 * i) * SS := by
  have h := conj_pow (a := SS) (b := RR) (i := i)
  rw [SS_RR, ← pow_mul] at h
  rw [h]
  group

theorem mem_tT0 {g : ↥SU} (hg : g ∈ tT0) : ∃ i < 8, ∃ e < 2, g = RR ^ i * SS ^ e := by
  have hR : ∀ i e : ℕ, RR * (RR ^ i * SS ^ e) = RR ^ ((i + 1) % 8) * SS ^ (e % 2) := by
    intro i e
    rw [← mul_assoc, ← pow_succ', ← RR_pow_mod, ← SS_pow_mod]
  have hS : ∀ i e : ℕ, SS * (RR ^ i * SS ^ e) = RR ^ ((3 * i) % 8) * SS ^ ((e + 1) % 2) := by
    intro i e
    rw [← mul_assoc, SS_mul_RR_pow, mul_assoc, ← pow_succ', ← RR_pow_mod, ← SS_pow_mod]
  have hRi : RR⁻¹ = RR ^ 7 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', RR_pow]
  have hSi : SS⁻¹ = SS := by
    rw [inv_eq_iff_mul_eq_one, ← sq, SS_sq]
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, 0, by norm_num, by simp⟩
  | mul_left x hx g _ ih =>
    obtain ⟨i, -, e, -, rfl⟩ := ih
    rcases hx with rfl | hx
    · exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num), hR i e⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num), hS i e⟩
  | inv_mul_cancel x hx g _ ih =>
    obtain ⟨i, -, e, -, rfl⟩ := ih
    rcases hx with rfl | hx
    · refine ⟨(i + 7) % 8, Nat.mod_lt _ (by norm_num), e % 2, Nat.mod_lt _ (by norm_num), ?_⟩
      rw [hRi, ← mul_assoc, ← pow_add, ← RR_pow_mod, ← SS_pow_mod, add_comm]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hSi]
      exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num), hS i e⟩

theorem suMat_scalar (u : F25ˣ) {g : ↥SU}
    (hg : (g : GL (Fin 3) F25) = Matrix.GeneralLinearGroup.scalar (Fin 3) u) :
    suMat g = (u : F25) • (1 : Matrix (Fin 3) (Fin 3) F25) := by
  rw [suMat_apply, hg, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem proj_eq_iff {g g' : ↥SU} :
    proj g = proj g' ↔ ∃ c : F25, c ≠ 0 ∧ suMat g = c • suMat g' := by
  constructor
  · intro h
    have h1 : g'⁻¹ * g ∈ unitaryScalars f25Data 3 := by
      rw [← ker_unitaryProj f25Data 3, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    obtain ⟨c, -, -, hc⟩ := h1
    refine ⟨c, c.ne_zero, ?_⟩
    have e : g = g' * (g'⁻¹ * g) := by group
    rw [e, map_mul, suMat_scalar c hc, Matrix.mul_smul, mul_one]
  · rintro ⟨c, hc, h⟩
    have hdet : c ^ 3 = 1 := by
      have h1 := congrArg Matrix.det h
      rw [Matrix.det_smul, Fintype.card_fin, suMat_apply, suMat_apply, (mem_SU.mp g.2).1,
        (mem_SU.mp g'.2).1, mul_one] at h1
      exact h1.symm
    set u : F25ˣ := Units.mk0 c hc with hu
    have hmem : g'⁻¹ * g ∈ unitaryScalars f25Data 3 := by
      refine ⟨u, ?_, ?_, ?_⟩
      · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, f25_bar, hu,
          Units.val_mk0, show c * c ^ 5 = (c ^ 3) ^ 2 by ring, hdet, one_pow]
      · ext
        rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hdet, Units.val_one]
      · apply Units.ext
        have hg'1 : (((g' : GL (Fin 3) F25)⁻¹ : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) *
            suMat g' = 1 := by
          rw [suMat_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Subgroup.coe_mul,
          Subgroup.coe_inv, Units.val_mul, ← suMat_apply g, h, Matrix.mul_smul, hg'1,
          Matrix.smul_one_eq_diagonal, hu, Units.val_mk0]
    have hmem' := inv_mem hmem
    rw [_root_.mul_inv_rev, inv_inv] at hmem'
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hmem'

theorem card_PU : Nat.card PU = 126000 := by
  rw [Nat.card_congr (unitaryPSUEquiv f25Data (n := 3) (by norm_num)).toEquiv]
  exact CFSG.Quasithin.H13.KGAutSyl.U35Syl.card_PSU35

theorem RR_mem_T0 : proj RR ∈ T0 := ⟨RR, Subgroup.subset_closure (by simp), rfl⟩

theorem SS_mem_T0 : proj SS ∈ T0 := ⟨SS, Subgroup.subset_closure (by simp), rfl⟩

theorem psuConj_proj (A : unitaryIsom3 f25Data) (g : ↥SU) :
    psuConj f25Data A (proj g) = proj (suConj f25Data A g) :=
  psuConj_mk A g

theorem conj_proj (g : ↥SU) :
    MulAut.conj (proj g) = psuConj f25Data ⟨g, unitarySU_le_unitaryIsom3 g.2⟩ :=
  conj_mk_eq_psuConj g

theorem suMat_suConj (A : unitaryIsom3 f25Data) (g : ↥SU) :
    suMat (suConj f25Data A g) = ((A : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) * suMat g *
      (((A : GL (Fin 3) F25)⁻¹ : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := by
  rw [suMat_apply, coe_suConj, Units.val_mul, Units.val_mul, suMat_apply, Subgroup.coe_inv]

abbrev mat (A : unitaryIsom3 f25Data) : Matrix (Fin 3) (Fin 3) F25 :=
  ((A : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25)

theorem unitary_mat (A : unitaryIsom3 f25Data) : ((mat A).map (· ^ 5))ᵀ * mat A = 1 := by
  have h := mem_unitaryIsom3.mp A.2
  have hmap : (mat A).map (· ^ 5) = (mat A).map f25Data.bar := by
    ext i k
    simp [f25_bar]
  rw [hmap]
  exact h

theorem mat_pow (A : unitaryIsom3 f25Data) (n : ℕ) : mat (A ^ n) = mat A ^ n := by
  rw [mat, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem psuConj_pow_eq_one_iff (B : unitaryIsom3 f25Data) (n : ℕ) :
    psuConj f25Data B ^ n = 1 ↔ ∃ c : F25, mat B ^ n = Matrix.scalar (Fin 3) c := by
  rw [← map_pow]
  constructor
  · intro h
    obtain ⟨-, c, -, hc⟩ :=
      eq_one_of_psuConj_mul_psuField_eq_one (B ^ n) 1 (by rw [map_one, mul_one, h])
    refine ⟨c, ?_⟩
    rw [← mat_pow, mat, hc, Matrix.GeneralLinearGroup.coe_scalar]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := congrArg Matrix.det hc
      rw [map_zero, Matrix.det_zero, ← mat_pow, mat,
        ← Matrix.GeneralLinearGroup.val_det_apply] at h1
      exact Units.ne_zero _ h1
    have hBn : ((B ^ n : unitaryIsom3 f25Data) : GL (Fin 3) F25) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [← mat, mat_pow, hc, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) ∈ unitaryIsom3 f25Data :=
      hBn ▸ (B ^ n).2
    have : B ^ n = ⟨_, hmem⟩ := Subtype.ext hBn
    rw [this, psuConj_scalar hmem]

theorem scalar_mem_isom {l : F25} (hl : l ^ 6 = 1) (hl0 : l ≠ 0) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 l hl0) ∈ unitaryIsom3 f25Data := by
  rw [mem_unitaryIsom3, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Units.val_mk0, f25_bar, ← pow_succ, hl]

end CFSG.Quasithin.H13.NQCat.T513.U35
