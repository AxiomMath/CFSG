module

public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.CTP.StdMatrix

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL subfieldGL_mem_gramSU coe_subfieldGL)
open CFSG.ClassicalInvolution.Phan (blockEmb blockEmb2 iSup_range_blockEmb2)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {f : ℕ} {F : Type} [Field F] {n : ℕ}

theorem coordEmbed_swap (i j : Fin n) (hij : i ≠ j) (Y : Matrix (Fin 2) (Fin 2) F) :
    coordEmbed F j i Y = coordEmbed F i j !![Y 1 1, Y 1 0; Y 0 1, Y 0 0] := by
  ext k l
  simp only [coordEmbed, coordIncl, coordProj, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply,
    Fin.sum_univ_two]
  by_cases hk : k = i <;> by_cases hk' : k = j <;> by_cases hl : l = i <;> by_cases hl' : l = j <;>
    simp_all [hij.symm]

theorem blk_le_swap (h : UnitaryFieldData 2 f F) {i j : Fin n} (hij : i ≠ j) :
    blk h hij ≤ blk h hij.symm := by
  intro g hg
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hij).mp hg
  obtain ⟨hXu, hXd⟩ := (mem_gramSU_iff_unitary h).mp hX
  have hu : ((X : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (X : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := mem_primeFormUnitary.mp hXu
    simpa [idGram] using this
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  have e10 := congrFun (congrFun hu 1) 0
  have e11 := congrFun (congrFun hu 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
  set X' : Matrix (Fin 2) (Fin 2) F :=
    !![(X : Matrix (Fin 2) (Fin 2) F) 1 1, (X : Matrix (Fin 2) (Fin 2) F) 1 0;
      (X : Matrix (Fin 2) (Fin 2) F) 0 1, (X : Matrix (Fin 2) (Fin 2) F) 0 0] with hX'
  have hdet : X'.det = 1 := by
    rw [← hXd, Matrix.det_fin_two, Matrix.det_fin_two]
    simp [hX']
    ring
  have hne : X'.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine (mem_blk_iff hij.symm).mpr ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X' hne, ?_, ?_⟩
  · refine (mem_gramSU_iff_unitary h).mpr ⟨?_, ?_⟩
    · rw [mem_primeFormUnitary]
      simp only [idGram, Units.val_one, Matrix.mul_one]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hX', Matrix.GeneralLinearGroup.mkOfDetNeZero]
      · linear_combination e11
      · linear_combination e10
      · linear_combination e01
      · linear_combination e00
    · simpa using hdet
  · rw [hgX]
    simpa [hX'] using coordEmbed_swap j i hij.symm (X : Matrix (Fin 2) (Fin 2) F)

theorem blk_swap (h : UnitaryFieldData 2 f F) {i j : Fin n} (hij : i ≠ j) :
    blk h hij = blk h hij.symm :=
  le_antisymm (blk_le_swap h hij) (blk_le_swap h hij.symm)


theorem blk_zero_one_sup_blk_one_two_eq (h : UnitaryFieldData 2 f F) (hf : 2 ≤ f) :
    blk h (show (0 : Fin 3) ≠ 1 by decide) ⊔ blk h (show (1 : Fin 3) ≠ 2 by decide) =
      unitarySU 2 f F 3 := by
  have hfin := h.finite
  have hch := h.charP
  have hK : Nat.card F = (2 ^ f) ^ 2 := h.card_eq_sq
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  rw [blk_eq_map_blockEmb_adjacent h (m := 3) (i := 0) (by omega) (a := 0) (b := 1) rfl rfl
    (by decide), blk_eq_map_blockEmb_adjacent h (m := 3) (i := 1) (by omega) (a := 1) (b := 2)
    rfl rfl (by decide), ← Subgroup.map_sup]
  have htop : (blockEmb F 2 f 3 2 0 (by omega)).range ⊔ (blockEmb F 2 f 3 2 1 (by omega)).range =
      ⊤ := by
    rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq 2]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype, SUid_eq_statedSU hK 3]

theorem map_coordPerm_unitarySU (hF : UnitaryFieldData 2 f F) (σ : Equiv.Perm (Fin n)) :
    (unitarySU 2 f F n).map (coordPerm F σ).toMonoidHom = unitarySU 2 f F n := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact coordPerm_mem_unitarySU hF σ hg
  · intro y hy
    refine ⟨coordPerm F σ.symm y, coordPerm_mem_unitarySU hF σ.symm hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← coordPerm_symm, MulEquiv.apply_symm_apply]

theorem exists_perm_three_shared : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
    ∃ σ : Equiv.Perm (Fin 3), σ b = 0 ∧ σ a = 1 ∧ σ d = 2 := by
  decide

theorem blk_sup_blk_eq_unitarySU (h : UnitaryFieldData 2 f F) (hf : 2 ≤ f) {a b d : Fin 3}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    blk h hab ⊔ blk h had = unitarySU 2 f F 3 := by
  obtain ⟨σ, hb, ha, hd⟩ := exists_perm_three_shared a b d hab had hbd
  set ρ := coordPerm F σ with hρ
  have h1 : (blk h hab).map ρ.toMonoidHom = blk h (show (1 : Fin 3) ≠ 0 by decide) :=
    map_blk_coordPerm_of_eq h σ hab ha hb (by decide)
  have h2 : (blk h had).map ρ.toMonoidHom = blk h (show (1 : Fin 3) ≠ 2 by decide) :=
    map_blk_coordPerm_of_eq h σ had ha hd (by decide)
  have h3 : blk h (show (1 : Fin 3) ≠ 0 by decide) = blk h (show (0 : Fin 3) ≠ 1 by decide) :=
    (blk_swap h (show (0 : Fin 3) ≠ 1 by decide)).symm
  have key : (blk h hab ⊔ blk h had).map ρ.toMonoidHom =
      (unitarySU 2 f F 3).map ρ.toMonoidHom := by
    rw [Subgroup.map_sup, h1, h2, h3, blk_zero_one_sup_blk_one_two_eq h hf,
      map_coordPerm_unitarySU h σ]
  exact Subgroup.map_injective ρ.injective key

theorem coordPerm_eq_conj_permGL (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) F) :
    coordPerm F σ g = permGL σ * g * (permGL σ)⁻¹ := by
  apply Units.ext
  rw [coe_coordPerm, Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv]
  have h1 : (σ⁻¹.permMatrix F) * (g : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((g : Matrix (Fin n) (Fin n) F).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id) *
      σ.permMatrix F = ((g : Matrix (Fin n) (Fin n) F).submatrix
        (σ⁻¹ : Equiv.Perm (Fin n)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext k l
  simp [Equiv.Perm.inv_def]

section KstSup

variable {e : ℕ} (K₀ : Subfield F)

theorem subfieldGL_permGL (σ : Equiv.Perm (Fin n)) :
    subfieldGL K₀ n (permGL σ) = permGL σ := by
  apply Units.ext
  rw [coe_subfieldGL, coe_permGL, coe_permGL]
  ext k l
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply, Equiv.Perm.permMatrix]
  split_ifs <;> simp

theorem permGL_mem_Kst (h₀ : UnitaryFieldData 2 e K₀) (σ : Equiv.Perm (Fin 3)) :
    (permGL σ : GL (Fin 3) F) ∈ (unitarySU 2 e K₀ 3).map (subfieldGL K₀ 3) :=
  ⟨permGL σ, permGL_mem_unitarySU h₀ σ, subfieldGL_permGL K₀ σ⟩

variable (hF : UnitaryFieldData 2 f F) (h₀ : UnitaryFieldData 2 e K₀)
  (hbar : ∀ c : K₀, (h₀.bar c : F) = hF.bar c)

include hbar in
theorem Kst_sup_blk_eq (hf : 2 ≤ f) {a b : Fin 3} (hab : a ≠ b) :
    (unitarySU 2 e K₀ 3).map (subfieldGL K₀ 3) ⊔ blk hF hab = unitarySU 2 f F 3 := by
  obtain ⟨d, hda, hdb⟩ := CFSG.RankThree.Classical.exists_fin_ne_ne (by norm_num : 3 ≤ 3) a b
  have had : a ≠ d := hda.symm
  have hbd : b ≠ d := hdb.symm
  apply le_antisymm
  · refine sup_le ?_ (blk_le_unitarySU hab)
    rintro _ ⟨g, hg, rfl⟩
    rw [unitarySU_eq_gramSU h₀] at hg
    have := subfieldGL_mem_gramSU hF h₀ hbar 3 hg
    rwa [unitarySU_eq_gramSU hF 3]
  · rw [← blk_sup_blk_eq_unitarySU hF hf hab had hbd]
    refine sup_le le_sup_right ?_
    set τ : Equiv.Perm (Fin 3) := Equiv.swap b d with hτ
    have hπ := permGL_mem_Kst K₀ h₀ τ
    have hmap : (blk hF hab).map (coordPerm F τ).toMonoidHom = blk hF had :=
      map_blk_coordPerm_of_eq hF τ hab (Equiv.swap_apply_of_ne_of_ne hab had)
        (Equiv.swap_apply_left b d) had
    intro y hy
    rw [← hmap] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [MulEquiv.coe_toMonoidHom, coordPerm_eq_conj_permGL]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hπ) (Subgroup.mem_sup_right hg))
      (inv_mem (Subgroup.mem_sup_left hπ))

end KstSup

end CFSG.RankThree.PartOne.CTP
