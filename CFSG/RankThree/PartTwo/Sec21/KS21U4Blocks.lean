module

public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec21.Item22L2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4Lines

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LieType.Steinberg (fixedSubfield hypEquiv card_fixedSubfield)
open scoped commutatorElement

variable {F : Type} [Field F]

theorem antidiag_four : (antidiag 4 : Matrix (Fin 4) (Fin 4) F) =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

theorem entry_eq_zero_of_commute {g : Matrix (Fin 4) (Fin 4) F} {d : Fin 4 → F}
    (h : g * diagonal d = diagonal d * g) {i j : Fin 4} (hij : d i ≠ d j) : g i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at e
  have e' : (d j - d i) * g i j = 0 := by linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hij
  · exact h0

theorem commute_of_mem_centralizer {g t : GL (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) :
    (g : Matrix (Fin 4) (Fin 4) F) * (t : Matrix (Fin 4) (Fin 4) F) =
      (t : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
  have h := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F))
    (Subgroup.mem_centralizer_iff.mp hg t (Subgroup.mem_zpowers t))
  simp only [Units.val_mul] at h
  exact h.symm

theorem inSubgroup_perfectResidual_le_commutator {G : Type} [Group G] (X : Subgroup G) :
    inSubgroup perfectResidual X ≤ ⁅X, X⁆ := by
  have h1 : perfectResidual X ≤ derivedSeries X 1 := iInf_le _ 1
  rw [derivedSeries_one] at h1
  calc inSubgroup perfectResidual X = (perfectResidual X).map X.subtype := rfl
    _ ≤ (commutator X).map X.subtype := Subgroup.map_mono h1
    _ = ⁅X, X⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]

@[expose] def blkL (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, M 0 0, M 0 1, 0; 0, M 1 0, M 1 1, 0; 0, 0, 0, 1]

@[expose] def blkLHom : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 4) (Fin 4) F where
  toFun := blkL
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkL]
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkL, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem det_blkL (M : Matrix (Fin 2) (Fin 2) F) : (blkL M).det = M.det := by
  simp [blkL, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def blkJ (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1; 0, X 0 0, X 0 1, 0; 0, X 1 0, X 1 1, 0; 1, 0, 0, 0]

theorem antidiag_four_eq_blkJ : (antidiag 4 : Matrix (Fin 4) (Fin 4) F) = blkJ (antidiag 2) := by
  rw [antidiag_four, CFSG.LieType.Steinberg.antidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkJ]

theorem blkJ_injective {X X' : Matrix (Fin 2) (Fin 2) F} (h : blkJ X = blkJ X') : X = X' := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkJ] using congrFun (congrFun h 1) 1
  · simpa [blkJ] using congrFun (congrFun h 1) 2
  · simpa [blkJ] using congrFun (congrFun h 2) 1
  · simpa [blkJ] using congrFun (congrFun h 2) 2

theorem isometry_blkL (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) :
    conjTr σ (blkL M) * antidiag 4 * blkL M = blkJ (conjTr σ M * antidiag 2 * M) := by
  rw [antidiag_four, CFSG.LieType.Steinberg.antidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkL, blkJ, conjTr, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

variable (σ : F ≃+* F)

@[expose] noncomputable def iotaL : SU σ 2 →* GL (Fin 4) F :=
  (Units.map blkLHom).comp (SU σ 2).subtype

theorem coe_iotaL (M : SU σ 2) :
    ((iotaL σ M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkL ((M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem iotaL_injective : Function.Injective (iotaL σ) := by
  intro M N h
  have h' := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h
  simp only [coe_iotaL] at h'
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkL] using congrFun (congrFun h' 1) 1
  · simpa [blkL] using congrFun (congrFun h' 1) 2
  · simpa [blkL] using congrFun (congrFun h' 2) 1
  · simpa [blkL] using congrFun (congrFun h' 2) 2

theorem iotaL_mem_SU (M : SU σ 2) : iotaL σ M ∈ SU σ 4 := by
  obtain ⟨hdet, hiso⟩ := mem_SU.1 M.2
  refine mem_SU.2 ⟨?_, ?_⟩
  · rw [coe_iotaL, det_blkL, hdet]
  · rw [coe_iotaL, isometry_blkL, hiso, antidiag_four_eq_blkJ]

@[expose] noncomputable def longSL : Subgroup (GL (Fin 4) F) := (iotaL σ).range

theorem longSL_le_SU : longSL σ ≤ SU σ 4 := by
  rintro _ ⟨M, rfl⟩
  exact iotaL_mem_SU σ M

theorem entry_zero_zero_of_mem_longSL {x : GL (Fin 4) F} (hx : x ∈ longSL σ) :
    (x : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
  obtain ⟨M, rfl⟩ := hx
  simp [coe_iotaL, blkL]

theorem longSL_le_centralizer {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) :
    longSL σ ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)) := by
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨M, rfl⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaL, ht]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blkL, mul_comm]

theorem pattern_long {g : Matrix (Fin 4) (Fin 4) F} {α β γ : F} (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) (h : g * diagonal ![α, β, β, γ] = diagonal ![α, β, β, γ] * g) :
    g 0 1 = 0 ∧ g 0 2 = 0 ∧ g 0 3 = 0 ∧ g 1 0 = 0 ∧ g 1 3 = 0 ∧ g 2 0 = 0 ∧ g 2 3 = 0 ∧
      g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 3 2 = 0 :=
  ⟨entry_eq_zero_of_commute h hαβ, entry_eq_zero_of_commute h hαβ,
    entry_eq_zero_of_commute h hαγ, entry_eq_zero_of_commute h hαβ.symm,
    entry_eq_zero_of_commute h hβγ, entry_eq_zero_of_commute h hαβ.symm,
    entry_eq_zero_of_commute h hβγ, entry_eq_zero_of_commute h hαγ.symm,
    entry_eq_zero_of_commute h hβγ.symm, entry_eq_zero_of_commute h hβγ.symm⟩

theorem pattern_long_of_mem {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) {x : GL (Fin 4) F}
    (hx : x ∈ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) :
    (x : Matrix (Fin 4) (Fin 4) F) 0 1 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 1 0 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 2 3 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 3 1 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 3 2 = 0 :=
  pattern_long hαβ hαγ hβγ (by rw [← ht]; exact commute_of_mem_centralizer hx)

theorem mem_longSL_of {k : GL (Fin 4) F} (hk : k ∈ SU σ 4)
    (hpat : (k : Matrix (Fin 4) (Fin 4) F) 0 1 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 1 0 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 2 3 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 3 1 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 3 2 = 0)
    (h00 : (k : Matrix (Fin 4) (Fin 4) F) 0 0 = 1) : k ∈ longSL σ := by
  obtain ⟨h01, h02, h03, h10, h13, h20, h23, h30, h31, h32⟩ := hpat
  obtain ⟨hdet, hiso⟩ := mem_SU.1 hk
  set m := (k : Matrix (Fin 4) (Fin 4) F) with hm
  have h33 : m 3 3 = 1 := by
    have e := congrFun (congrFun hiso 0) 3
    rw [antidiag_four] at e
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03, h10, h13, h20, h23, h30,
      h31, h32, h00] using e
  set M : Matrix (Fin 2) (Fin 2) F := !![m 1 1, m 1 2; m 2 1, m 2 2] with hM
  have hkM : m = blkL M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkL, M, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32, h00, h33]
  have hdetM : M.det = 1 := by rw [← det_blkL, ← hkM, hdet]
  have hisoM : conjTr σ M * antidiag 2 * M = antidiag 2 := by
    have e := hiso
    rw [hkM, isometry_blkL, antidiag_four_eq_blkJ] at e
    exact blkJ_injective e
  have hu : IsUnit M.det := by rw [hdetM]; exact isUnit_one
  refine ⟨⟨Matrix.nonsingInvUnit M hu, mem_SU.2 ⟨hdetM, hisoM⟩⟩, Units.ext ?_⟩
  rw [coe_iotaL]
  exact hkM.symm

theorem commutator_mem_longSL {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) {g h : GL (Fin 4) F}
    (hg : g ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)))
    (hh : h ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) :
    ⁅g, h⁆ ∈ longSL σ := by
  set C := SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))
  let χ : C →* F :=
    { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨h01, h02, h03, -⟩ := pattern_long_of_mem ht hαβ hαγ hβγ x.2.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03] }
  have hχ : χ.toHomUnits ⁅(⟨g, hg⟩ : C), ⟨h, hh⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hk : ⁅g, h⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  have h00 : ((⁅g, h⁆ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
    have e := congrArg Units.val hχ
    exact e
  exact mem_longSL_of σ hk.1 (pattern_long_of_mem ht hαβ hαγ hβγ hk.2) h00

theorem perfectResidual_long {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) (hperf : ⁅longSL σ, longSL σ⁆ = longSL σ) :
    inSubgroup perfectResidual
        (SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) =
      longSL σ := by
  apply le_antisymm
  · exact (inSubgroup_perfectResidual_le_commutator _).trans (Subgroup.commutator_le.mpr
      fun g hg h hh => commutator_mem_longSL σ ht hαβ hαγ hβγ hg hh)
  · exact Sec18.le_inSubgroup_perfectResidual hperf
      (le_inf (longSL_le_SU σ) (longSL_le_centralizer σ ht))

@[expose] def blkS (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, σ (B 0 0), σ (B 0 1);
    0, 0, σ (B 1 0), σ (B 1 1)]

@[expose] def blkSHom : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 4) (Fin 4) F where
  toFun := blkS σ
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkS]
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkS, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem det_blkS (B : Matrix (Fin 2) (Fin 2) F) : (blkS σ B).det = B.det * σ B.det := by
  have e : (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = 3 := rfl
  simp [blkS, Matrix.det_succ_row_zero, Fin.sum_univ_succ, map_mul, e]
  ring

@[expose] noncomputable def iotaS : SpecialLinearGroup (Fin 2) F →* GL (Fin 4) F :=
  (Units.map (blkSHom σ)).comp SpecialLinearGroup.toGL

theorem coe_iotaS (B : SpecialLinearGroup (Fin 2) F) :
    ((iotaS σ B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkS σ (B : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem iotaS_injective : Function.Injective (iotaS σ) := by
  intro B C h
  have h' := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h
  simp only [coe_iotaS] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkS] using congrFun (congrFun h' 0) 0
  · simpa [blkS] using congrFun (congrFun h' 0) 1
  · simpa [blkS] using congrFun (congrFun h' 1) 0
  · simpa [blkS] using congrFun (congrFun h' 1) 1

@[expose] noncomputable def shortSL : Subgroup (GL (Fin 4) F) := (iotaS σ).range

theorem det_block_of_mem_shortSL {x : GL (Fin 4) F} (hx : x ∈ shortSL σ) :
    (x : Matrix (Fin 4) (Fin 4) F) 0 0 * (x : Matrix (Fin 4) (Fin 4) F) 1 1 -
      (x : Matrix (Fin 4) (Fin 4) F) 0 1 * (x : Matrix (Fin 4) (Fin 4) F) 1 0 = 1 := by
  obtain ⟨B, rfl⟩ := hx
  have h := B.2
  rw [Matrix.det_fin_two] at h
  simpa [coe_iotaS, blkS] using h

theorem shortSL_le_centralizer {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) :
    shortSL σ ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)) := by
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨B, rfl⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaS, ht]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blkS, mul_comm]

theorem pattern_short {g : Matrix (Fin 4) (Fin 4) F} {α β : F} (hαβ : α ≠ β)
    (h : g * diagonal ![α, α, β, β] = diagonal ![α, α, β, β] * g) :
    g 0 2 = 0 ∧ g 0 3 = 0 ∧ g 1 2 = 0 ∧ g 1 3 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 3 0 = 0 ∧
      g 3 1 = 0 :=
  ⟨entry_eq_zero_of_commute h hαβ, entry_eq_zero_of_commute h hαβ,
    entry_eq_zero_of_commute h hαβ, entry_eq_zero_of_commute h hαβ,
    entry_eq_zero_of_commute h hαβ.symm, entry_eq_zero_of_commute h hαβ.symm,
    entry_eq_zero_of_commute h hαβ.symm, entry_eq_zero_of_commute h hαβ.symm⟩

variable [CharP F 2]

theorem iotaS_mem_SU (hσ : ∀ c, σ (σ c) = c) (B : SpecialLinearGroup (Fin 2) F) :
    iotaS σ B ∈ SU σ 4 := by
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet' : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 +
      (B : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← CharTwo.sub_eq_add]
    exact hdet
  have hs : σ ((B : Matrix (Fin 2) (Fin 2) F) 0 0) * σ ((B : Matrix (Fin 2) (Fin 2) F) 1 1) +
      σ ((B : Matrix (Fin 2) (Fin 2) F) 0 1) * σ ((B : Matrix (Fin 2) (Fin 2) F) 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, hdet', map_one]
  refine mem_SU.2 ⟨?_, ?_⟩
  · rw [coe_iotaS, det_blkS, B.2, map_one, one_mul]
  · rw [coe_iotaS, antidiag_four]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkS, conjTr, Matrix.mul_apply, Fin.sum_univ_four, hσ] <;>
      first | linear_combination hdet' | linear_combination hs | (ring_nf; simp [h2])

theorem shortSL_le_SU (hσ : ∀ c, σ (σ c) = c) : shortSL σ ≤ SU σ 4 := by
  rintro _ ⟨B, rfl⟩
  exact iotaS_mem_SU σ hσ B

omit [CharP F 2] in
theorem pattern_short_of_mem {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) (hαβ : α ≠ β)
    {x : GL (Fin 4) F}
    (hx : x ∈ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) :
    (x : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 1 2 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 2 1 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 3 1 = 0 :=
  pattern_short hαβ (by rw [← ht]; exact commute_of_mem_centralizer hx)

theorem mem_shortSL_of {k : GL (Fin 4) F} (hk : k ∈ SU σ 4)
    (hpat : (k : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 1 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 2 1 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 3 1 = 0)
    (hdet : (k : Matrix (Fin 4) (Fin 4) F) 0 0 * (k : Matrix (Fin 4) (Fin 4) F) 1 1 -
      (k : Matrix (Fin 4) (Fin 4) F) 0 1 * (k : Matrix (Fin 4) (Fin 4) F) 1 0 = 1) :
    k ∈ shortSL σ := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := hpat
  obtain ⟨-, hiso⟩ := mem_SU.1 hk
  set m := (k : Matrix (Fin 4) (Fin 4) F) with hm
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
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
  have h23 : m 2 3 = σ (m 0 1) := by
    linear_combination σ (m 0 0) * e13 - σ (m 0 1) * e03 - m 2 3 * hs - σ (m 0 1) * h2
  have h32 : m 3 2 = σ (m 1 0) := by
    linear_combination σ (m 1 1) * e02 - σ (m 1 0) * e12 - m 3 2 * hs - σ (m 1 0) * h2
  refine ⟨⟨!![m 0 0, m 0 1; m 1 0, m 1 1], by rw [Matrix.det_fin_two]; simpa using hdet⟩,
    Units.ext ?_⟩
  show blkS σ !![m 0 0, m 0 1; m 1 0, m 1 1] = m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkS, h02, h03, h12, h13, h20, h21, h30, h31, h22, h33,
    h23, h32]

theorem commutator_mem_shortSL {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) (hαβ : α ≠ β)
    {g h : GL (Fin 4) F}
    (hg : g ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)))
    (hh : h ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) :
    ⁅g, h⁆ ∈ shortSL σ := by
  set C := SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))
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
  have hχ : χ.toHomUnits ⁅(⟨g, hg⟩ : C), ⟨h, hh⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hk : ⁅g, h⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  exact mem_shortSL_of σ hk.1 (pattern_short_of_mem ht hαβ hk.2) (congrArg Units.val hχ)

theorem perfectResidual_short (hσ : ∀ c, σ (σ c) = c) {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) (hαβ : α ≠ β)
    (hperf : ⁅shortSL σ, shortSL σ⁆ = shortSL σ) :
    inSubgroup perfectResidual
        (SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) =
      shortSL σ := by
  apply le_antisymm
  · exact (inSubgroup_perfectResidual_le_commutator _).trans (Subgroup.commutator_le.mpr
      fun g hg h hh => commutator_mem_shortSL σ ht hαβ hg hh)
  · exact Sec18.le_inSubgroup_perfectResidual hperf
      (le_inf (shortSL_le_SU σ hσ) (shortSL_le_centralizer σ ht))

theorem nonempty_longSL_mulEquiv [Finite F] {b : ℕ} (hb : 0 < b)
    (hF : Nat.card F = (2 ^ b) ^ 2) :
    Nonempty (longSL (unitaryInvolution F 2 b) ≃* projSL 2 (GaloisField 2 b)) := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h1' : unitaryInvolution F 2 b 1 = -1 := by rw [map_one, CharTwo.neg_eq]
  have := Fintype.ofFinite (fixedSubfield F 2 b)
  have := Fintype.ofFinite (GaloisField 2 b)
  have hcard : Fintype.card (fixedSubfield F 2 b) = Fintype.card (GaloisField 2 b) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_fixedSubfield hF,
      GaloisField.card 2 b hb.ne']
  exact ⟨(MonoidHom.ofInjective (iotaL_injective _)).symm.trans ((hypEquiv h1 h1').symm.trans
    ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans (projSLTwoEquivSL (GaloisField 2 b)).symm))⟩

end CFSG.RankThree.PartTwo.Sec21.U4Lines
