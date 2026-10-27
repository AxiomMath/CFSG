module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofU4Syl
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Blocks
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

open Matrix CFSG
open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.RankThree.PartTwo.Sec21.U4Lines
open scoped commutatorElement

section Unitary

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem conjTr_one {n : ℕ} : conjTr σ (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [conjTr, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem isometry_inv {n : ℕ} {R : GL (Fin n) F}
    (hR : conjTr σ (R : Matrix (Fin n) (Fin n) F) * antidiag n * (R : Matrix (Fin n) (Fin n) F) =
      antidiag n) :
    conjTr σ ((R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
  set Ri := ((R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Rm := (R : Matrix (Fin n) (Fin n) F)
  have h1 : Rm * Ri = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : conjTr σ Ri * conjTr σ Rm = 1 := by rw [← conjTr_mul, h1, conjTr_one]
  calc conjTr σ Ri * antidiag n * Ri = conjTr σ Ri * (conjTr σ Rm * antidiag n * Rm) * Ri := by
        rw [hR]
    _ = (conjTr σ Ri * conjTr σ Rm) * antidiag n * (Rm * Ri) := by noncomm_ring
    _ = antidiag n := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem isometry_conj {n : ℕ} {R g : GL (Fin n) F}
    (hR : conjTr σ (R : Matrix (Fin n) (Fin n) F) * antidiag n * (R : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    (hg : conjTr σ (g : Matrix (Fin n) (Fin n) F) * antidiag n * (g : Matrix (Fin n) (Fin n) F) =
      antidiag n) :
    conjTr σ ((R * g * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((R * g * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
  have hRi := isometry_inv σ hR
  set Ri := ((R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Rm := (R : Matrix (Fin n) (Fin n) F)
  set gm := (g : Matrix (Fin n) (Fin n) F)
  rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul]
  calc conjTr σ Ri * (conjTr σ gm * conjTr σ Rm) * antidiag n * (Rm * gm * Ri) =
      conjTr σ Ri * (conjTr σ gm * (conjTr σ Rm * antidiag n * Rm) * gm) * Ri := by noncomm_ring
    _ = antidiag n := by rw [hR, hg, hRi]

theorem mem_SU_conj_iff {n : ℕ} {R : GL (Fin n) F}
    (hR : conjTr σ (R : Matrix (Fin n) (Fin n) F) * antidiag n * (R : Matrix (Fin n) (Fin n) F) =
      antidiag n) (g : GL (Fin n) F) : g ∈ SU σ n ↔ R * g * R⁻¹ ∈ SU σ n := by
  have hdet : ((R * g * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      (g : Matrix (Fin n) (Fin n) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  constructor
  · intro hg
    exact mem_SU.2 ⟨hdet.trans (mem_SU.1 hg).1, isometry_conj σ hR (mem_SU.1 hg).2⟩
  · intro hg
    refine mem_SU.2 ⟨hdet.symm.trans (mem_SU.1 hg).1, ?_⟩
    have e : g = R⁻¹ * (R * g * R⁻¹) * R⁻¹⁻¹ := by group
    rw [e]
    exact isometry_conj σ (isometry_inv σ hR) (mem_SU.1 hg).2

theorem mem_SUid_iff_conj {n : ℕ} {W : GL (Fin n) F}
    (hW : conjTr σ (W : Matrix (Fin n) (Fin n) F) * (W : Matrix (Fin n) (Fin n) F) = antidiag n)
    (g : GL (Fin n) F) : g ∈ SUid σ n ↔ W⁻¹ * g * W⁻¹⁻¹ ∈ SU σ n := by
  set Wi := ((W⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Wm := (W : Matrix (Fin n) (Fin n) F)
  set gm := (g : Matrix (Fin n) (Fin n) F)
  have h1 : Wm * Wi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1' : Wi * Wm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : conjTr σ Wi * conjTr σ Wm = 1 := by rw [← conjTr_mul, h1, conjTr_one]
  have h2' : conjTr σ Wm * conjTr σ Wi = 1 := by rw [← conjTr_mul, h1', conjTr_one]
  have hdet : ((W⁻¹ * g * W⁻¹⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = gm.det := by
    rw [inv_inv, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm,
      ← mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, one_mul]
  have hgram : conjTr σ ((W⁻¹ * g * W⁻¹⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      antidiag n * ((W⁻¹ * g * W⁻¹⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      conjTr σ Wm * (conjTr σ gm * gm) * Wm := by
    rw [inv_inv, Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul, ← hW]
    calc conjTr σ Wm * (conjTr σ gm * conjTr σ Wi) * (conjTr σ Wm * Wm) * (Wi * gm * Wm) =
        conjTr σ Wm * conjTr σ gm * (conjTr σ Wi * conjTr σ Wm) * Wm * Wi * gm * Wm := by
          noncomm_ring
      _ = conjTr σ Wm * (conjTr σ gm * gm) * Wm := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc _ Wm Wi, h1, Matrix.mul_one]; noncomm_ring
  constructor
  · intro hg
    obtain ⟨hd, hi⟩ := mem_SUid.1 hg
    exact mem_SU.2 ⟨hdet.trans hd, by rw [hgram, hi, Matrix.mul_one, hW]⟩
  · intro hg
    obtain ⟨hd, hi⟩ := mem_SU.1 hg
    refine mem_SUid.2 ⟨hdet.symm.trans hd, ?_⟩
    rw [hgram, ← hW] at hi
    have e := congrArg (fun M => conjTr σ Wi * M * Wi) hi
    calc conjTr σ gm * gm = (conjTr σ Wi * conjTr σ Wm) * (conjTr σ gm * gm) * (Wm * Wi) := by
          rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
      _ = conjTr σ Wi * (conjTr σ Wm * (conjTr σ gm * gm) * Wm) * Wi := by noncomm_ring
      _ = conjTr σ Wi * (conjTr σ Wm * Wm) * Wi := e
      _ = (conjTr σ Wi * conjTr σ Wm) * (Wm * Wi) := by noncomm_ring
      _ = 1 := by rw [h2, h1, Matrix.one_mul]

theorem mem_centralizer_zpowers_of_commute {G : Type*} [Group G] {g t : G} (h : g * t = t * g) :
    g ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact Commute.zpow_left (h.symm : Commute t g) k

theorem isCentData_long {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) : IsCentData (SU σ 4) t (iotaL σ) := by
  refine ⟨fun x => iotaL_mem_SU σ x, fun x => ?_, fun g hg h hh hgt hht => ?_⟩
  · have := longSL_le_centralizer σ ht ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this t (Subgroup.mem_zpowers t)).symm
  · obtain ⟨M, hM⟩ := commutator_mem_longSL σ ht hαβ hαγ hβγ
      ⟨hg, mem_centralizer_zpowers_of_commute hgt⟩ ⟨hh, mem_centralizer_zpowers_of_commute hht⟩
    exact ⟨M, by rw [hM, commutatorElement_def]⟩

theorem ker_mk_iotaL : (ProjGenLinGroup.mk.comp (iotaL σ)).ker = ⊥ := by
  rw [eq_bot_iff]
  intro M hM
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hM
  obtain ⟨u, hu⟩ := hM
  have e := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hu
  simp only [GeneralLinearGroup.coe_scalar, coe_iotaL] at e
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e12 := congrFun (congrFun e 1) 2
  have e21 := congrFun (congrFun e 2) 1
  have e22 := congrFun (congrFun e 2) 2
  simp [blkL, Matrix.scalar_apply] at e00 e11 e12 e21 e22
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← e11, ← e22, ← e12, ← e21, e00]

@[expose] def blkSo (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, σ (B 0 0), -σ (B 0 1);
    0, 0, -σ (B 1 0), σ (B 1 1)]

@[expose] def blkSoHom : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 4) (Fin 4) F where
  toFun := blkSo σ
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkSo]
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkSo, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

@[expose] noncomputable def iotaSo : SpecialLinearGroup (Fin 2) F →* GL (Fin 4) F :=
  (Units.map (blkSoHom σ)).comp SpecialLinearGroup.toGL

theorem coe_iotaSo (B : SpecialLinearGroup (Fin 2) F) :
    ((iotaSo σ B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkSo σ (B : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem iotaSo_mem_SU (hσ : ∀ c, σ (σ c) = c) (B : SpecialLinearGroup (Fin 2) F) :
    iotaSo σ B ∈ SU σ 4 := by
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  have hs : σ ((B : Matrix (Fin 2) (Fin 2) F) 0 0) * σ ((B : Matrix (Fin 2) (Fin 2) F) 1 1) -
      σ ((B : Matrix (Fin 2) (Fin 2) F) 0 1) * σ ((B : Matrix (Fin 2) (Fin 2) F) 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  refine mem_SU.2 ⟨?_, ?_⟩
  · have e : (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = 3 := rfl
    rw [coe_iotaSo]
    simp [blkSo, Matrix.det_succ_row_zero, Fin.sum_univ_succ, e]
    linear_combination (σ ((B : Matrix (Fin 2) (Fin 2) F) 0 0) *
      σ ((B : Matrix (Fin 2) (Fin 2) F) 1 1) - σ ((B : Matrix (Fin 2) (Fin 2) F) 0 1) *
      σ ((B : Matrix (Fin 2) (Fin 2) F) 1 0)) * hdet + hs
  · rw [coe_iotaSo, antidiag_four]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkSo, conjTr, Matrix.mul_apply, Fin.sum_univ_four, hσ] <;>
      first | linear_combination hdet | linear_combination hs | ring

theorem exists_iotaSo_eq {k : GL (Fin 4) F} (hk : k ∈ SU σ 4)
    (hpat : (k : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 1 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 2 1 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 3 1 = 0)
    (hdet : (k : Matrix (Fin 4) (Fin 4) F) 0 0 * (k : Matrix (Fin 4) (Fin 4) F) 1 1 -
      (k : Matrix (Fin 4) (Fin 4) F) 0 1 * (k : Matrix (Fin 4) (Fin 4) F) 1 0 = 1) :
    ∃ B : SpecialLinearGroup (Fin 2) F, iotaSo σ B = k := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := hpat
  obtain ⟨-, hiso⟩ := mem_SU.1 hk
  set m := (k : Matrix (Fin 4) (Fin 4) F) with hm
  have hs : σ (m 0 0) * σ (m 1 1) - σ (m 0 1) * σ (m 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  rw [antidiag_four] at hiso
  have e02 := congrFun (congrFun hiso 0) 2
  have e03 := congrFun (congrFun hiso 0) 3
  have e12 := congrFun (congrFun hiso 1) 2
  have e13 := congrFun (congrFun hiso 1) 3
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30,
    h31] at e02 e03 e12 e13
  have h22 : m 2 2 = σ (m 0 0) := by
    linear_combination σ (m 0 0) * e12 - σ (m 0 1) * e02 - m 2 2 * hs
  have h33 : m 3 3 = σ (m 1 1) := by
    linear_combination σ (m 1 1) * e03 - σ (m 1 0) * e13 - m 3 3 * hs
  have h23 : m 2 3 = -σ (m 0 1) := by
    linear_combination σ (m 0 0) * e13 - σ (m 0 1) * e03 - m 2 3 * hs
  have h32 : m 3 2 = -σ (m 1 0) := by
    linear_combination σ (m 1 1) * e02 - σ (m 1 0) * e12 - m 3 2 * hs
  refine ⟨⟨!![m 0 0, m 0 1; m 1 0, m 1 1], by rw [Matrix.det_fin_two]; simpa using hdet⟩,
    Units.ext ?_⟩
  show blkSo σ !![m 0 0, m 0 1; m 1 0, m 1 1] = m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkSo, h02, h03, h12, h13, h20, h21, h30, h31, h22, h33,
    h23, h32]

theorem isCentData_shortOdd (hσ : ∀ c, σ (σ c) = c) {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) (hαβ : α ≠ β) :
    IsCentData (SU σ 4) t (iotaSo σ) := by
  refine ⟨fun B => iotaSo_mem_SU σ hσ B, fun B => ?_, fun g hg h hh hgt hht => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_iotaSo, ht]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [blkSo, mul_comm]
  · set C := SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))
    have hgC : g ∈ C := ⟨hg, mem_centralizer_zpowers_of_commute hgt⟩
    have hhC : h ∈ C := ⟨hh, mem_centralizer_zpowers_of_commute hht⟩
    let χ : C →* F :=
      { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 *
          ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1 -
          ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1 *
          ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0
        map_one' := by simp
        map_mul' := fun x y => by
          obtain ⟨h02, h03, h12, h13, -⟩ := pattern_short_of_mem ht hαβ x.2.2
          simp [Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]
          ring }
    have hχ : χ.toHomUnits ⁅(⟨g, hgC⟩ : C), ⟨h, hhC⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hk : ⁅g, h⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hgC hhC) (C.inv_mem hgC)) (C.inv_mem hhC)
    obtain ⟨B, hB⟩ := exists_iotaSo_eq σ hk.1 (pattern_short_of_mem ht hαβ hk.2)
      (congrArg Units.val hχ)
    exact ⟨B, by rw [hB, commutatorElement_def]⟩

theorem ker_mk_iotaSo : (ProjGenLinGroup.mk.comp (iotaSo σ)).ker =
    Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  ext B
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar, Matrix.SpecialLinearGroup.mem_center_iff,
    Fintype.card_fin]
  constructor
  · rintro ⟨u, hu⟩
    have e := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hu
    simp only [GeneralLinearGroup.coe_scalar, coe_iotaSo] at e
    have e00 := congrFun (congrFun e 0) 0
    have e01 := congrFun (congrFun e 0) 1
    have e10 := congrFun (congrFun e 1) 0
    have e11 := congrFun (congrFun e 1) 1
    simp [blkSo, Matrix.scalar_apply] at e00 e01 e10 e11
    refine ⟨u, ?_, ?_⟩
    · have hdet := B.2
      rw [Matrix.det_fin_two, ← e00, ← e11, ← e01, ← e10] at hdet
      linear_combination hdet
    · ext i j
      fin_cases i <;> fin_cases j
      · simpa [Matrix.scalar_apply] using e00
      · simpa [Matrix.scalar_apply] using e01
      · simpa [Matrix.scalar_apply] using e10
      · simpa [Matrix.scalar_apply] using e11
  · rintro ⟨r, hr2, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr2
    have hσr : σ r = r := by
      have h' : (r - 1) * (r + 1) = 0 := by linear_combination hr2
      rcases mul_eq_zero.mp h' with h0 | h0
      · rw [show r = 1 by linear_combination h0, map_one]
      · rw [show r = -1 by linear_combination h0, map_neg, map_one]
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, coe_iotaSo, ← hr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkSo, Matrix.scalar_apply, hσr]

end Unitary

section Normal

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_inv_of_cube {F : Type} [Field F] {a b : Fˣ} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hba : b ≠ a) : b = a⁻¹ := by
  have ha3' : (a : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha3, Units.val_one]
  have hb3' : (b : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hb3, Units.val_one]
  have ha1' : (a : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h => ha1 (Units.ext h)
  have hq : (a : F) ^ 2 + a + 1 = 0 := by
    have : ((a : F) - 1) * ((a : F) ^ 2 + a + 1) = 0 := by linear_combination ha3'
    exact (mul_eq_zero.mp this).resolve_left ha1'
  have h : ((b : F) - 1) * (((b : F) - a) * ((b : F) - a ^ 2)) = 0 := by
    linear_combination hb3' - ha3' + (-(b : F) ^ 2 + (b : F) * a) * hq
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (Units.ext (sub_eq_zero.mp h1)) hb1
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact absurd (Units.ext (sub_eq_zero.mp h3)) hba
  · apply Units.ext
    rw [Units.val_inv_eq_inv_val, sub_eq_zero.mp h4]
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    field_simp
    linear_combination ha3'

theorem exists_normal_form_SU (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ∣ p ^ f - 1)
    {A : GL (Fin 4) K} (hA : A ∈ SU (unitaryInvolution K p f) 4) (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    ∃ (P : GL (Fin 4) K) (α : Kˣ),
      (∀ g, g ∈ SU (unitaryInvolution K p f) 4 ↔ P * g * P⁻¹ ∈ SU (unitaryInvolution K p f) 4) ∧
      α ^ 3 = 1 ∧ α ≠ 1 ∧
      (P * A * P⁻¹ = diagU ![α, 1, 1, α⁻¹] ∨ P * A * P⁻¹ = diagU ![α, α, α⁻¹, α⁻¹]) := by
  set σ := unitaryInvolution K p f with hσ
  let A' : SU σ 4 := ⟨A, hA⟩
  have hA'3 : A' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA3)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su_prime (n := 4) (Or.inl rfl) d8Comb_four hK
    Nat.prime_three (by norm_num) h3 (Subgroup.zpowers A') (by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hA'3,
        _root_.one_zpow])
  have hgA := hg A' (Subgroup.mem_zpowers A')
  rw [Subgroup.mem_subgroupOf] at hgA
  obtain ⟨v, hv⟩ := mem_d8Tor_iff.mp hgA
  rw [d8Vec_four] at hv
  set a : Kˣ := ((v.1 : rootsOfUnity 3 K) : Kˣ) with ha
  set b : Kˣ := ((v.2 : rootsOfUnity 3 K) : Kˣ) with hb
  have ha3 : a ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp v.1.2
  have hb3 : b ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp v.2.2
  have hconj : (g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ = diagU (dvec4 a b) := by
    rw [hv]
    rfl
  have hgS : ∀ h, h ∈ SU σ 4 ↔ (g : GL (Fin 4) K) * h * (g : GL (Fin 4) K)⁻¹ ∈ SU σ 4 :=
    mem_SU_conj_iff σ (mem_SU.1 g.2).2
  have hperm : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (∀ h, h ∈ SU σ 4 ↔ (permGL τ * (g : GL (Fin 4) K)) * h *
        (permGL τ * (g : GL (Fin 4) K))⁻¹ ∈ SU σ 4) ∧
      (permGL τ * (g : GL (Fin 4) K)) * A * (permGL τ * (g : GL (Fin 4) K))⁻¹ =
        diagU (dvec4 a b ∘ τ.symm) := by
    intro τ hτ
    refine ⟨fun h => ?_, ?_⟩
    · rw [hgS h, mem_SU_conj_iff σ (permGL_gram σ τ hτ)]
      constructor <;> intro hh <;> convert hh using 1 <;> group
    · rw [← permGL_conj_diagU, ← hconj]
      group
  have hA1' : a ≠ 1 ∨ b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hA1
    have : diagU (dvec4 a b) = (1 : GL (Fin 4) K) := by
      rw [hcon.1, hcon.2]
      rw [← diagU_one]
      congr 1
      funext i
      fin_cases i <;> simp [dvec4]
    rw [← hconj] at this
    rw [mul_inv_eq_one, mul_eq_left] at this
    exact this
  by_cases hb1 : b = 1
  · have ha1 : a ≠ 1 := hA1'.resolve_right (not_not.mpr hb1)
    refine ⟨g, a, hgS, ha3, ha1, Or.inl ?_⟩
    rw [hconj, hb1]
    congr 1
  by_cases ha1 : a = 1
  · obtain ⟨hP, hPA⟩ := hperm (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide)
    refine ⟨_, b, hP, hb3, hb1, Or.inl ?_⟩
    rw [hPA, ha1]
    congr 1
    all_goals funext i; fin_cases i <;> simp [dvec4] <;> rfl
  by_cases hba : b = a
  · refine ⟨g, a, hgS, ha3, ha1, Or.inr ?_⟩
    rw [hconj, hba]
    all_goals rfl
  · have hbi : b = a⁻¹ := eq_inv_of_cube ha3 ha1 hb3 hb1 hba
    obtain ⟨hP, hPA⟩ := hperm (Equiv.swap 1 2) (by decide)
    refine ⟨_, a, hP, ha3, ha1, Or.inr ?_⟩
    rw [hPA, hbi]
    congr 1
    all_goals funext i; fin_cases i <;> simp [dvec4] <;> rfl

theorem ne_inv_of_cube {F : Type} [Field F] {α : Fˣ} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) :
    (α : F) ≠ ((α⁻¹ : Fˣ) : F) := by
  intro h
  apply hα1
  have h2 : α * α = 1 := by
    have := congrArg (fun x : F => (α : F) * x) h
    simp only [Units.mul_inv] at this
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; exact this)
  calc α = α ^ 3 * (α * α)⁻¹ := by group
    _ = 1 := by rw [hα3, h2, inv_one, one_mul]

theorem centData_SU (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ∣ p ^ f - 1)
    {A : GL (Fin 4) K} (hA : A ∈ SU (unitaryInvolution K p f) 4) (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    (∃ φ : SU (unitaryInvolution K p f) 2 →* GL (Fin 4) K,
        IsCentData (SU (unitaryInvolution K p f) 4) A φ ∧
          (ProjGenLinGroup.mk.comp φ).ker = ⊥) ∨
      (∃ φ : SpecialLinearGroup (Fin 2) K →* GL (Fin 4) K,
        IsCentData (SU (unitaryInvolution K p f) 4) A φ ∧
          (ProjGenLinGroup.mk.comp φ).ker = Subgroup.center (SpecialLinearGroup (Fin 2) K)) := by
  set σ := unitaryInvolution K p f with hσdef
  have hσ : ∀ c, σ (σ c) = c :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK).invol
  obtain ⟨P, α, hP, hα3, hα1, hD | hD⟩ := exists_normal_form_SU hK h3 hA hA3 hA1
  · left
    have ht : ((P * A * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal ![(α : K), 1, 1, ((α⁻¹ : Kˣ) : K)] := by
      rw [hD, diagU_val]
      congr 1
      funext i
      fin_cases i <;> rfl
    have h1 : (α : K) ≠ 1 := fun h => hα1 (Units.ext h)
    have h2 : (1 : K) ≠ ((α⁻¹ : Kˣ) : K) := fun h => hα1 (by
      have : α⁻¹ = 1 := Units.ext h.symm
      rw [← inv_inv α, this, inv_one])
    refine ⟨_, (isCentData_long σ ht h1 (ne_inv_of_cube hα3 hα1) h2).conj hP rfl, ?_⟩
    rw [ker_mk_conj, ker_mk_iotaL]
  · right
    have ht : ((P * A * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal ![(α : K), α, ((α⁻¹ : Kˣ) : K), ((α⁻¹ : Kˣ) : K)] := by
      rw [hD, diagU_val]
      congr 1
      funext i
      fin_cases i <;> rfl
    refine ⟨_, (isCentData_shortOdd σ hσ ht (ne_inv_of_cube hα3 hα1)).conj hP rfl, ?_⟩
    rw [ker_mk_conj, ker_mk_iotaSo]

end Normal

end CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
