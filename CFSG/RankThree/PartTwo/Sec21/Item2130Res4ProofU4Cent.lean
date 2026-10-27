module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4Blocks
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUModel
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof

open Matrix CFSG CFSG.RankThree CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
open CFSG.Assembly.LowTwoRank (StatedSU)
open scoped commutatorElement

section Blocks

variable {F : Type} [Field F]

@[expose] def blk3 (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, A 0 2, 0; A 1 0, A 1 1, A 1 2, 0; A 2 0, A 2 1, A 2 2, 0; 0, 0, 0, 1]

@[expose] def blk3Hom : Matrix (Fin 3) (Fin 3) F →* Matrix (Fin 4) (Fin 4) F where
  toFun := blk3
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk3]
  map_mul' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk3, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem det_blk3 (A : Matrix (Fin 3) (Fin 3) F) : (blk3 A).det = A.det := by
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_four]
  have h1 : (blk3 A).submatrix (Fin.succAbove 3) (Fin.succAbove 3) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e0 : blk3 A 3 0 = 0 := rfl
  have e1 : blk3 A 3 1 = 0 := rfl
  have e2 : blk3 A 3 2 = 0 := rfl
  have e3 : blk3 A 3 3 = 1 := rfl
  rw [e0, e1, e2, e3, h1]
  norm_num

theorem blk3_injective {A B : Matrix (Fin 3) (Fin 3) F} (h : blk3 A = blk3 B) : A = B := by
  ext i j
  have e := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [blk3] using e

theorem gram_blk3 (σ : F →+* F) (A : Matrix (Fin 3) (Fin 3) F) :
    ((blk3 A).map σ)ᵀ * blk3 A = blk3 ((A.map σ)ᵀ * A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem blk3_mul_diagonal (A : Matrix (Fin 3) (Fin 3) F) (ω : F) :
    blk3 A * diagonal ![ω, ω, ω, 1] = diagonal ![ω, ω, ω, 1] * blk3 A := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blk3, mul_comm]

theorem pattern_of_commute {g : Matrix (Fin 4) (Fin 4) F} {ω : F} (hω : ω ≠ 1)
    (h : g * diagonal ![ω, ω, ω, 1] = diagonal ![ω, ω, ω, 1] * g) :
    g 0 3 = 0 ∧ g 1 3 = 0 ∧ g 2 3 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 3 2 = 0 :=
  ⟨U4Lines.entry_eq_zero_of_commute h hω, U4Lines.entry_eq_zero_of_commute h hω,
    U4Lines.entry_eq_zero_of_commute h hω, U4Lines.entry_eq_zero_of_commute h hω.symm,
    U4Lines.entry_eq_zero_of_commute h hω.symm, U4Lines.entry_eq_zero_of_commute h hω.symm⟩

theorem eq_blk3_of_pattern {g : Matrix (Fin 4) (Fin 4) F}
    (hpat : g 0 3 = 0 ∧ g 1 3 = 0 ∧ g 2 3 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 3 2 = 0)
    (h33 : g 3 3 = 1) :
    g = blk3 !![g 0 0, g 0 1, g 0 2; g 1 0, g 1 1, g 1 2; g 2 0, g 2 1, g 2 2] := by
  obtain ⟨h03, h13, h23, h30, h31, h32⟩ := hpat
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3, h03, h13, h23, h30, h31, h32, h33]

end Blocks

section Unitary

variable {f : ℕ} {K : Type} [Field K]
variable (h : UnitaryFieldData 2 f K)

theorem statedSU_eq_uS (n : ℕ) : StatedSU n (2 ^ f) K = uS h n := by
  show StatedSU n (2 ^ f) K = gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Units.val_one]
  exact unitarySU_eq_gramSU h n

@[expose] noncomputable def iota3 : uS h 3 →* GL (Fin 4) K :=
  (Units.map blk3Hom).comp (uS h 3).subtype

theorem coe_iota3 (A : uS h 3) :
    ((iota3 h A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk3 ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem iota3_injective : Function.Injective (iota3 h) := by
  intro A B hAB
  have e := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hAB
  simp only [coe_iota3] at e
  exact Subtype.ext (Units.ext (blk3_injective e))

theorem iota3_mem (A : uS h 3) : iota3 h A ∈ uS h 4 := by
  obtain ⟨hiso, hdet⟩ := mem_gramSU.mp A.2
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one] at hiso ⊢
    rw [coe_iota3, gram_blk3, hiso]
    exact map_one blk3Hom
  · rw [coe_iota3, det_blk3, hdet]

@[expose] noncomputable def blk3SU : Subgroup (GL (Fin 4) K) := (iota3 h).range

theorem blk3SU_le_uS : blk3SU h ≤ uS h 4 := by
  rintro _ ⟨A, rfl⟩
  exact iota3_mem h A

noncomputable def blk3SUEquiv : blk3SU h ≃* uS h 3 :=
  (MonoidHom.ofInjective (iota3_injective h)).symm

theorem blk3SU_le_centralizer {D : GL (Fin 4) K} {ω : K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1]) :
    blk3SU h ≤ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iota3, hD]
  exact blk3_mul_diagonal _ ω

theorem mem_blk3SU_of {k : GL (Fin 4) K} (hk : k ∈ uS h 4)
    (hpat : (k : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 ∧
      (k : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) K) 3 2 = 0)
    (h33 : (k : Matrix (Fin 4) (Fin 4) K) 3 3 = 1) : k ∈ blk3SU h := by
  obtain ⟨hiso, hdet⟩ := mem_gramSU.mp hk
  set m := (k : Matrix (Fin 4) (Fin 4) K) with hm
  set A : Matrix (Fin 3) (Fin 3) K :=
    !![m 0 0, m 0 1, m 0 2; m 1 0, m 1 1, m 1 2; m 2 0, m 2 1, m 2 2] with hA
  have hkA : m = blk3 A := eq_blk3_of_pattern hpat h33
  have hdetA : A.det = 1 := by rw [← det_blk3, ← hkA, hdet]
  have hisoA : (A.map h.bar)ᵀ * A = 1 := by
    rw [Units.val_one, Matrix.mul_one] at hiso
    rw [hkA, gram_blk3] at hiso
    have h1 : blk3 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := map_one blk3Hom
    exact blk3_injective (hiso.trans h1.symm)
  have hu : IsUnit A.det := by rw [hdetA]; exact isUnit_one
  refine ⟨⟨Matrix.nonsingInvUnit A hu, mem_gramSU.mpr ⟨?_, hdetA⟩⟩, Units.ext ?_⟩
  · rw [Units.val_one, Matrix.mul_one]
    exact hisoA
  · rw [coe_iota3]
    exact hkA.symm

theorem commutator_mem_blk3SU {D : GL (Fin 4) K} {ω : K} (hω : ω ≠ 1)
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1]) {g k : GL (Fin 4) K}
    (hg : g ∈ uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)))
    (hk : k ∈ uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K))) :
    ⁅g, k⁆ ∈ blk3SU h := by
  set C := uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K))
  have hpat : ∀ x ∈ C, (x : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := by
    intro x hx
    apply pattern_of_commute hω
    have e := congrArg (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K))
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
    simp only [Units.val_mul, hD] at e
    exact e
  let χ : C →* K :=
    { toFun := fun x => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨-, -, -, h30, h31, h32⟩ := hpat x x.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h30, h31, h32] }
  have hχ : χ.toHomUnits ⁅(⟨g, hg⟩ : C), ⟨k, hk⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hgk : ⁅g, k⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hk) (C.inv_mem hg)) (C.inv_mem hk)
  have h33 : ((⁅g, k⁆ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
    have e := congrArg Units.val hχ
    exact e
  exact mem_blk3SU_of h hgk.1 (hpat _ hgk) h33

theorem commutator_blk3SU [Finite K] [Fact (Nat.Prime 2)] (hf : 1 < f) :
    ⁅blk3SU h, blk3SU h⁆ = blk3SU h := by
  have hK := card_sq_of_unitary h
  have hq : (3, 2 ^ f) ≠ (3, 2) := by
    intro he
    have h2 : 2 ^ f = 2 ^ 1 := by simpa using he
    have := Nat.pow_right_injective le_rfl h2
    omega
  have hperf : Group.IsPerfect (StatedSU 3 (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl hq
  have e := statedSU_eq_uS h 3
  have hperf' : Group.IsPerfect (uS h 3) := by
    have : Group.IsPerfect (StatedSU 3 (2 ^ f) K) := hperf
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr e).toMonoidHom)
      (MulEquiv.surjective _)
  have : Group.IsPerfect (blk3SU h) :=
    Group.IsPerfect.ofSurjective (f := (blk3SUEquiv h).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Subgroup.isPerfect_iff.mp this

theorem perfectResidual_blk3SU [Finite K] [Fact (Nat.Prime 2)] (hf : 1 < f) {D : GL (Fin 4) K}
    {ω : K} (hω : ω ≠ 1)
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1]) :
    inSubgroup perfectResidual (uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K))) =
      blk3SU h := by
  apply le_antisymm
  · exact (U4Lines.inSubgroup_perfectResidual_le_commutator _).trans (Subgroup.commutator_le.mpr
      fun g hg k hk => commutator_mem_blk3SU h hω hD hg hk)
  · exact Sec18.le_inSubgroup_perfectResidual (commutator_blk3SU h hf)
      (le_inf (blk3SU_le_uS h) (blk3SU_le_centralizer h hD))

theorem isSLThreePiAt_blk3SU [Finite K] (hf : Odd f) : Sec4.IsSLThreePiAt (blk3SU h) (2 ^ f) := by
  have e := statedSU_eq_uS h 3
  refine ⟨K, inferInstance, inferInstance, Or.inr ⟨card_sq_of_unitary h, ?_,
    ⟨(blk3SUEquiv h).trans (MulEquiv.subgroupCongr e.symm)⟩⟩⟩
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem mem_blk3SU_diagonal {D : GL (Fin 4) K} {ω : K} (hω3 : ω ^ 3 = 1)
    (hωbar : h.bar ω * ω = 1) (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1]) :
    D ∈ blk3SU h := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hdet : (ω • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hω3]
  have hu : IsUnit (ω • (1 : Matrix (Fin 3) (Fin 3) K)).det := by rw [hdet]; exact isUnit_one
  refine ⟨⟨Matrix.nonsingInvUnit _ hu, mem_gramSU.mpr ⟨?_, hdet⟩⟩, Units.ext ?_⟩
  · rw [Units.val_one, Matrix.mul_one]
    change ((ω • (1 : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ * (ω • 1) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hωbar]
  · rw [coe_iota3, hD]
    change blk3 (ω • (1 : Matrix (Fin 3) (Fin 3) K)) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk3]

end Unitary

end CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof
