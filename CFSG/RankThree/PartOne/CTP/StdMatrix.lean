module

public import CFSG.RankThree.PartOne.KF.U4Su3
public import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne.EmbeddingTransport CFSG.RankThree.PartOne.EmbeddingFixedResidual
open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {F : Type} [Field F]

theorem coordEmbed_zero_one (X : Matrix (Fin 2) (Fin 2) F) :
    coordEmbed F (0 : Fin 3) 1 X = !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1] := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem mul_diagU_eq_iff {d : Fin 3 → Fˣ} {g : GL (Fin 3) F} :
    g * diagU d = diagU d * g ↔
      ∀ i j, (g : Matrix (Fin 3) (Fin 3) F) i j * (d j : F) = (d i : F) * g i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun (congrArg (fun x : GL (Fin 3) F =>
      (x : Matrix (Fin 3) (Fin 3) F)) h) i) j
    simpa [diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    apply Units.ext
    ext i j
    simpa [diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

theorem mem_centralizer_diagU_iff {d : Fin 3 → Fˣ} (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2)
    {g : GL (Fin 3) F} :
    g ∈ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F)) ↔
      (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_diagU_eq_iff]
  have hne : ((d 0 : Fˣ) : F) - (d 2 : F) ≠ 0 := sub_ne_zero.mpr (fun h => h02 (Units.ext h))
  have h1 : ((d 1 : Fˣ) : F) = d 0 := by rw [h01]
  constructor
  · intro h
    have e02 := h 0 2
    have e12 := h 1 2
    have e20 := h 2 0
    have e21 := h 2 1
    rw [h1] at e12 e21
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (g : Matrix (Fin 3) (Fin 3) F) 0 2 * ((d 2 : F) - d 0) = 0 := by linear_combination e02
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd (by linear_combination -h') hne
    · have : (g : Matrix (Fin 3) (Fin 3) F) 1 2 * ((d 2 : F) - d 0) = 0 := by linear_combination e12
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd (by linear_combination -h') hne
    · have : (g : Matrix (Fin 3) (Fin 3) F) 2 0 * ((d 0 : F) - d 2) = 0 := by linear_combination e20
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hne
    · have : (g : Matrix (Fin 3) (Fin 3) F) 2 1 * ((d 0 : F) - d 2) = 0 := by linear_combination e21
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hne
  · rintro ⟨a, b, c, e⟩ i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, e, h1] <;> ring

theorem mem_blk_zero_one_of_block (hF : UnitaryFieldData 2 f F) {g : GL (Fin 3) F}
    (hg : g ∈ unitarySU 2 f F 3)
    (h02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) :
    g ∈ blk hF (show (0 : Fin 3) ≠ 1 by decide) := by
  obtain ⟨hdet, hunit⟩ := (mem_unitarySU_iff hF).mp hg
  set A : Matrix (Fin 2) (Fin 2) F :=
    !![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
      (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1] with hA
  have hgm : (g : Matrix (Fin 3) (Fin 3) F) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, h02, h12, h20, h21, h22]
  have hdetA : A.det = 1 := by
    have := hdet
    rw [hgm] at this
    simpa [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two] using this
  have hAu : (A.map hF.bar)ᵀ * A = 1 := by
    have h := hunit
    rw [hgm] at h
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.sum_univ_two] using e00
    · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.sum_univ_two] using e01
    · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.sum_univ_two] using e10
    · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.sum_univ_two] using e11
  have hne : A.det ≠ 0 := by rw [hdetA]; exact one_ne_zero
  refine (mem_blk_iff _).mpr ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, ?_⟩
  · refine (mem_gramSU_iff_unitary hF).mpr ⟨?_, ?_⟩
    · rw [mem_primeFormUnitary]
      simpa [idGram] using hAu
    · simpa using hdetA
  · rw [hgm, coordEmbed_zero_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem hom_trivial_of_perfect {P A : Type*} [Group P] [CommGroup A] (hP : Group.IsPerfect P)
    (φ : P →* A) : φ = 1 := by
  have h : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro g _ k _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have htop : φ.ker = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup P) = ⁅(⊤ : Subgroup P), ⊤⁆ := hP.commutator_eq_top.symm
      _ ≤ φ.ker := h
  ext x
  have : x ∈ φ.ker := by rw [htop]; trivial
  simpa using this

theorem blk_zero_one_le (hF : UnitaryFieldData 2 f F) {d : Fin 3 → Fˣ} (h01 : d 0 = d 1) :
    blk hF (show (0 : Fin 3) ≠ 1 by decide) ≤
      unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F)) := by
  intro g hg
  refine ⟨blk_le_unitarySU _ hg, ?_⟩
  obtain ⟨X, -, hX⟩ := (mem_blk_iff _).mp hg
  refine Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, hX, diagU_val]
  exact (diagonal_mul_coordEmbed (fun i => (d i : F)) (by simp [h01]) _).symm

noncomputable def ent22 {d : Fin 3 → Fˣ} (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2) :
    ↥(unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F))) →* F where
  toFun g := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_centralizer_diagU_iff h01 h02).mp g.2.2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.2.2.1, hg.2.2.2]

theorem residual_centralizer_diagU_zero_one [Finite F] (hF : UnitaryFieldData 2 f F)
    (hq : 4 ≤ 2 ^ f) {d : Fin 3 → Fˣ} (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2) :
    inSubgroup perfectResidual
        (unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F))) =
      blk hF (show (0 : Fin 3) ≠ 1 by decide) := by
  set C := unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F)) with hC
  apply le_antisymm
  ·
    intro g hg
    have hRC : inSubgroup perfectResidual C ≤ C := Subgroup.map_subtype_le _
    have hperf := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual C
    have hδ := hom_trivial_of_perfect (A := Fˣ) (P := ↥(inSubgroup perfectResidual C)) hperf
      ((MonoidHom.toHomUnits (ent22 (f := f) (F := F) h01 h02)).comp
        (Subgroup.inclusion hRC))
    have hg22 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      have := congrArg (fun φ : ↥(inSubgroup perfectResidual C) →* Fˣ =>
        ((φ ⟨g, hg⟩ : Fˣ) : F)) hδ
      simpa [ent22] using this
    have hgC := hRC hg
    have hblock := (mem_centralizer_diagU_iff h01 h02).mp hgC.2
    exact mem_blk_zero_one_of_block hF hgC.1 hblock.1 hblock.2.1 hblock.2.2.1 hblock.2.2.2 hg22
  ·
    have hle := blk_zero_one_le hF h01
    have hperf : Group.IsPerfect ↥(blk hF (show (0 : Fin 3) ≠ 1 by decide)) := by
      have := isPerfect_coordSU hF hq (show (0 : Fin 3) ≠ 1 by decide)
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.equivMapOfInjective _
        (primeFormUnitary hF (idGram F 3)).subtype (Subgroup.subtype_injective _)).toMonoidHom)
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).surjective
    exact le_inSubgroup_perfectResidual_of_isPerfect hle hperf

theorem coordPerm_diagU {n : ℕ} (σ : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) :
    coordPerm F σ (diagU d) = diagU (d ∘ σ.symm) := by
  apply Units.ext
  rw [coe_coordPerm, diagU_val, diagU_val]
  exact Matrix.submatrix_diagonal_equiv _ _

theorem coordPerm_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (coordPerm F σ).symm = coordPerm F σ.symm := by
  refine MulEquiv.ext fun g => ?_
  rw [MulEquiv.symm_apply_eq]
  apply Units.ext
  rw [coe_coordPerm, coe_coordPerm]
  ext i j
  simp

theorem coordPerm_mem_unitarySU (hF : UnitaryFieldData 2 f F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    {g : GL (Fin n) F} (hg : g ∈ unitarySU 2 f F n) : coordPerm F σ g ∈ unitarySU 2 f F n := by
  rw [mem_unitarySU_iff hF] at hg ⊢
  obtain ⟨hdet, hu⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [coe_coordPerm, Matrix.det_submatrix_equiv_self]
    exact hdet
  · rw [coe_coordPerm]
    have h : (((g : Matrix (Fin n) (Fin n) F).submatrix σ.symm σ.symm).map hF.bar)ᵀ *
        (g : Matrix (Fin n) (Fin n) F).submatrix σ.symm σ.symm =
        (((g : Matrix (Fin n) (Fin n) F).map hF.bar)ᵀ * (g : Matrix (Fin n) (Fin n) F)).submatrix
          σ.symm σ.symm := by
      rw [← Matrix.submatrix_mul_equiv _ _ σ.symm σ.symm σ.symm, ← Matrix.submatrix_map,
        Matrix.transpose_submatrix]
    rw [h, hu, Matrix.submatrix_one_equiv]

theorem map_coordPerm_inf_centralizer (hF : UnitaryFieldData 2 f F) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : GL (Fin n) F) :
    (unitarySU 2 f F n ⊓ Subgroup.centralizer ({x} : Set (GL (Fin n) F))).map
        (coordPerm F σ).toMonoidHom =
      unitarySU 2 f F n ⊓ Subgroup.centralizer ({coordPerm F σ x} : Set (GL (Fin n) F)) := by
  ext y
  constructor
  · rintro ⟨g, ⟨hgS, hgC⟩, rfl⟩
    refine ⟨coordPerm_mem_unitarySU hF σ hgS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hgC' := Subgroup.mem_centralizer_singleton_iff.mp hgC
    show coordPerm F σ g * coordPerm F σ x = coordPerm F σ x * coordPerm F σ g
    rw [← map_mul, ← map_mul, hgC']
  · rintro ⟨hyS, hyC⟩
    have hsymm : (coordPerm F σ).symm y = coordPerm F σ.symm y := by rw [coordPerm_symm]
    refine ⟨coordPerm F σ.symm y, ⟨coordPerm_mem_unitarySU hF σ.symm hyS,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · have hyC' := Subgroup.mem_centralizer_singleton_iff.mp hyC
      rw [← hsymm]
      apply (coordPerm F σ).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hyC'
    · rw [MulEquiv.coe_toMonoidHom, ← hsymm, MulEquiv.apply_symm_apply]

theorem exists_perm_three : ∀ a b e : Fin 3, a ≠ b → a ≠ e → b ≠ e →
    ∃ σ : Equiv.Perm (Fin 3), σ a = 0 ∧ σ b = 1 ∧ σ e = 2 := by
  decide

theorem residual_centralizer_diagU [Finite F] (hF : UnitaryFieldData 2 f F) (hq : 4 ≤ 2 ^ f)
    {a b e : Fin 3} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e) {d : Fin 3 → Fˣ} (hd : d a = d b)
    (hd' : d a ≠ d e) :
    inSubgroup perfectResidual
        (unitarySU 2 f F 3 ⊓ Subgroup.centralizer ({diagU d} : Set (GL (Fin 3) F))) =
      blk hF hab := by
  obtain ⟨σ, ha, hb, he⟩ := exists_perm_three a b e hab hae hbe
  set ρ := coordPerm F σ with hρ
  have h01 : (d ∘ σ.symm) 0 = (d ∘ σ.symm) 1 := by
    simp only [Function.comp_apply]
    rw [← ha, ← hb, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hd
  have h02 : (d ∘ σ.symm) 0 ≠ (d ∘ σ.symm) 2 := by
    simp only [Function.comp_apply]
    rw [← ha, ← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hd'
  have key := residual_centralizer_diagU_zero_one hF hq h01 h02
  rw [← coordPerm_diagU σ d] at key
  rw [← map_coordPerm_inf_centralizer hF σ (diagU d), ← map_inSubgroup_perfectResidual] at key
  have hmap : (blk hF hab).map ρ.toMonoidHom = blk hF (show (0 : Fin 3) ≠ 1 by decide) :=
    map_blk_coordPerm_of_eq hF σ hab ha hb (by decide)
  exact Subgroup.map_injective ρ.injective (key.trans hmap.symm)

end CFSG.RankThree.PartOne.CTP
