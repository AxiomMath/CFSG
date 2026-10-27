module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofParab
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open ProofKS1623Parab
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem mem_radU_two_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ radU F (flagSpace 3 F 2) ↔ g.val 0 0 = 1 ∧ g.val 0 1 = 0 ∧ g.val 1 0 = 0 ∧
      g.val 1 1 = 1 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 := by
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  have he1 : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  constructor
  · intro hu
    have h0 := hu.2 _ he0
    have h1 := hu.2 _ he1
    have h2 := (mem_flagSpace_two).mp (hu.1 (Pi.single 2 1))
    have h00 := congrFun h0 0
    have h10 := congrFun h0 1
    have h20 := congrFun h0 2
    have h01 := congrFun h1 0
    have h11 := congrFun h1 1
    have h21 := congrFun h1 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h00 h10 h20 h01 h11 h21 h2
    exact ⟨h00, h01, h10, h11, h20, h21, sub_eq_zero.mp h2⟩
  · rintro ⟨h00, h01, h10, h11, h20, h21, h22⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [mem_flagSpace_two]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22]
    · rw [mem_flagSpace_two] at hw
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22,
          hw]

@[expose] def uMat (w : Fin 2 → F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, w 0; 0, 1, w 1; 0, 0, 1]

@[expose] def uVec (w : Fin 2 → F) : SpecialLinearGroup (Fin 3) F :=
  ⟨uMat w, by simp [uMat, Matrix.det_fin_three]⟩

theorem uVec_mem_radU (w : Fin 2 → F) : uVec w ∈ radU F (flagSpace 3 F 2) := by
  rw [mem_radU_two_iff]
  simp [uVec, uMat]

theorem uVec_add (v w : Fin 2 → F) : uVec (v + w) = uVec v * uVec w := by
  apply Subtype.ext
  show uMat (v + w) = uMat v * uMat w
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uVec_zero : uVec (0 : Fin 2 → F) = 1 := by
  apply Subtype.ext
  show uMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

@[expose] def radCoord (g : SpecialLinearGroup (Fin 3) F) : Fin 2 → F :=
  ![g.val 0 2, g.val 1 2]

theorem radCoord_uVec (w : Fin 2 → F) : radCoord (uVec w) = w := by
  ext i
  fin_cases i <;> simp [radCoord, uVec, uMat]

theorem uVec_radCoord {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ radU F (flagSpace 3 F 2)) :
    uVec (radCoord g) = g := by
  obtain ⟨h00, h01, h10, h11, h20, h21, h22⟩ := mem_radU_two_iff.mp hg
  apply Subtype.ext
  show uMat (radCoord g) = g.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, radCoord, h00, h01, h10, h11, h20, h21, h22]

theorem radCoord_mul {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ radU F (flagSpace 3 F 2))
    (hh : h ∈ radU F (flagSpace 3 F 2)) : radCoord (g * h) = radCoord g + radCoord h := by
  rw [← uVec_radCoord hg, ← uVec_radCoord hh, ← uVec_add, radCoord_uVec, radCoord_uVec,
    radCoord_uVec]

@[expose] def parK (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1}
  mul_mem' {g h} hg hh := by
    obtain ⟨g0, g1, g2⟩ := hg
    obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, g0, g1, g2, h0, h1, h2]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  inv_mem' {g} hg := by
    obtain ⟨g0, g1, g2⟩ := hg
    have hdet : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
      have h := g.prop
      rw [Matrix.det_fin_three, g0, g1, g2] at h
      linear_combination h
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.adjugate_fin_three, g0, g1, g2, hdet]

theorem mem_parK {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ parK F ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 :=
  Iff.rfl

theorem radU_le_parK : radU F (flagSpace 3 F 2) ≤ parK F := fun g hg => by
  obtain ⟨-, -, -, -, h20, h21, h22⟩ := mem_radU_two_iff.mp hg
  exact ⟨h20, h21, h22⟩

theorem lev_mem_parK (A : SpecialLinearGroup (Fin 2) F) : lev F A ∈ parK F := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [lev_val, levMat]

theorem parK_le_stabilizer : parK F ≤ stabilizer (flagSpace 3 F 2) := by
  intro g hg
  rw [mem_stabilizer_flagSpace_iff]
  intro i j hi hj
  have hi2 : i = 2 := by
    ext
    have := i.2
    simp only [Fin.val_two]
    omega
  subst hi2
  obtain ⟨g0, g1, -⟩ := hg
  fin_cases j
  · exact g0
  · exact g1
  · exact absurd hj (by decide)

theorem eq_one_of_mem_parK_of_proj_eq_one {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ parK F)
    (h1 : proj 3 F g = 1) : g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h1)
  have h22 : (c : F) = 1 := by
    have := hg.2.2
    rw [hc, scalar_apply, diagonal_apply_eq] at this
    exact this
  apply Subtype.ext
  rw [hc, h22, map_one]
  rfl

theorem injOn_proj_parK :
    Set.InjOn (proj 3 F) (parK F : Set (SpecialLinearGroup (Fin 3) F)) := by
  intro g hg h hh hgh
  have h1 : proj 3 F (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
  have := eq_one_of_mem_parK_of_proj_eq_one (mul_mem (inv_mem hg) hh) h1
  rw [inv_mul_eq_one] at this
  exact this

@[expose] def blockAMat (g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![g.val 0 0, g.val 0 1; g.val 1 0, g.val 1 1]

theorem det_blockAMat {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ parK F) :
    (blockAMat g).det = 1 := by
  obtain ⟨g0, g1, g2⟩ := hg
  have h := g.prop
  rw [Matrix.det_fin_three, g0, g1, g2] at h
  rw [blockAMat, Matrix.det_fin_two_of]
  linear_combination h

@[expose] def blockA (F : Type) [Field F] : parK F →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨blockAMat g.1, det_blockAMat g.2⟩
  map_one' := by
    apply Subtype.ext
    show blockAMat 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockAMat]
  map_mul' g h := by
    apply Subtype.ext
    show blockAMat (g.1 * h.1) = blockAMat g.1 * blockAMat h.1
    obtain ⟨h0, h1, -⟩ := h.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockAMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

theorem blockA_val (g : parK F) : (blockA F g).val = blockAMat g.1 :=
  rfl

theorem blockA_lev (A : SpecialLinearGroup (Fin 2) F) :
    blockA F ⟨lev F A, lev_mem_parK A⟩ = A := by
  apply Subtype.ext
  show blockAMat (lev F A) = A.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockAMat, lev_val, levMat]

theorem blockA_surjective : Function.Surjective (blockA F) :=
  fun A => ⟨⟨lev F A, lev_mem_parK A⟩, blockA_lev A⟩

theorem blockA_eq_one_iff (g : parK F) :
    blockA F g = 1 ↔ g.1 ∈ radU F (flagSpace 3 F 2) := by
  obtain ⟨g0, g1, g2⟩ := g.2
  constructor
  · intro h
    have h' := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val) h
    simp only [blockA_val] at h'
    have e00 := congrFun (congrFun h' 0) 0
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    have e11 := congrFun (congrFun h' 1) 1
    simp [blockAMat] at e00 e01 e10 e11
    exact mem_radU_two_iff.mpr ⟨e00, e01, e10, e11, g0, g1, g2⟩
  · intro hu
    obtain ⟨h00, h01, h10, h11, -, -, -⟩ := mem_radU_two_iff.mp hu
    apply Subtype.ext
    show blockAMat g.1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockAMat, h00, h01, h10, h11]

theorem radCoord_conj {M u : SpecialLinearGroup (Fin 3) F} (hM : M ∈ parK F)
    (hu : u ∈ radU F (flagSpace 3 F 2)) :
    radCoord (M * u * M⁻¹) = (blockAMat M) *ᵥ radCoord u := by
  have hc := conj_mem_radU (parK_le_stabilizer hM) hu
  obtain ⟨c00, c01, c10, c11, c20, c21, c22⟩ := mem_radU_two_iff.mp hc
  obtain ⟨u00, u01, u10, u11, u20, u21, u22⟩ := mem_radU_two_iff.mp hu
  obtain ⟨m0, m1, m2⟩ := hM
  set C := M * u * M⁻¹ with hCdef
  have heq : C.val * M.val = M.val * u.val := by
    have : C * M = M * u := by rw [hCdef, inv_mul_cancel_right]
    exact congrArg Subtype.val this
  have e0 := congrFun (congrFun heq 0) 2
  have e1 := congrFun (congrFun heq 1) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e0 e1
  rw [c00, c01, m2] at e0
  rw [c10, c11, m2] at e1
  have h0 : (blockAMat M *ᵥ radCoord u) 0 = M.val 0 0 * u.val 0 2 + M.val 0 1 * u.val 1 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, blockAMat, radCoord]
  have h1 : (blockAMat M *ᵥ radCoord u) 1 = M.val 1 0 * u.val 0 2 + M.val 1 1 * u.val 1 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, blockAMat, radCoord]
  ext i
  fin_cases i
  · show radCoord C 0 = (blockAMat M *ᵥ radCoord u) 0
    rw [h0]
    show C.val 0 2 = _
    rw [u22] at e0
    linear_combination e0
  · show radCoord C 1 = (blockAMat M *ᵥ radCoord u) 1
    rw [h1]
    show C.val 1 2 = _
    rw [u22] at e1
    linear_combination e1

theorem blockAMat_lev (A : SpecialLinearGroup (Fin 2) F) : blockAMat (lev F A) = A.val :=
  congrArg Subtype.val (blockA_lev A)

theorem radCoord_inv {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ radU F (flagSpace 3 F 2)) :
    radCoord u⁻¹ = -radCoord u := by
  have h := radCoord_mul hu (inv_mem hu)
  rw [mul_inv_cancel] at h
  have h1 : radCoord (1 : SpecialLinearGroup (Fin 3) F) = 0 := by
    rw [← uVec_zero, radCoord_uVec]
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem commutator_lev_uVec (D : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    lev F D * uVec w * (lev F D)⁻¹ * (uVec w)⁻¹ = uVec ((D.val - 1) *ᵥ w) := by
  have hc := conj_mem_radU (parK_le_stabilizer (lev_mem_parK D)) (uVec_mem_radU w)
  have hmem : lev F D * uVec w * (lev F D)⁻¹ * (uVec w)⁻¹ ∈ radU F (flagSpace 3 F 2) :=
    mul_mem hc (inv_mem (uVec_mem_radU w))
  rw [← uVec_radCoord hmem, radCoord_mul hc (inv_mem (uVec_mem_radU w)),
    radCoord_conj (lev_mem_parK D) (uVec_mem_radU w), radCoord_inv (uVec_mem_radU w),
    radCoord_uVec, blockAMat_lev, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg]

@[expose] def diagT (t : F) (ht : t ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨diagonal ![t, t⁻¹], by
    rw [det_diagonal, Fin.prod_univ_two]
    simp [ht]⟩

theorem radU_le_commutator {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    radU F (flagSpace 3 F 2) ≤ ⁅parK F, parK F⁆ := by
  intro u hu
  have hs1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hs2 : t⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact ht1 (inv_eq_one.mp h)
  set w : Fin 2 → F := radCoord u with hw
  set w' : Fin 2 → F := ![(t - 1)⁻¹ * w 0, (t⁻¹ - 1)⁻¹ * w 1] with hw'
  have hDw : ((diagT t ht0).val - 1) *ᵥ w' = w := by
    ext i
    fin_cases i
    · simp [diagT, hw', Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.diagonal_apply]
      field_simp
    · simp [diagT, hw', Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.diagonal_apply]
      field_simp
  rw [← uVec_radCoord hu, ← hw, ← hDw, ← commutator_lev_uVec]
  exact Subgroup.commutator_mem_commutator (lev_mem_parK _) (radU_le_parK (uVec_mem_radU w'))

theorem isPerfect_parK [Finite F] (hF4 : 4 ≤ Nat.card F) : Group.IsPerfect (parK F) := by
  classical
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have hSL := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  obtain ⟨t, ht0, ht1⟩ : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.ofFinite F
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun g hg h hh =>
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)) ?_
  · intro g hg
    set A := blockA F ⟨g, hg⟩ with hA
    have hu : g * (lev F A)⁻¹ ∈ radU F (flagSpace 3 F 2) := by
      have h1 : blockA F (⟨g, hg⟩ * ⟨lev F A, lev_mem_parK A⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, blockA_lev, ← hA, mul_inv_cancel]
      exact (blockA_eq_one_iff _).mp h1
    have hlev : lev F A ∈ ⁅parK F, parK F⁆ := by
      have hAc : A ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
        rw [hSL.commutator_eq_top]
        exact Subgroup.mem_top A
      have h2 : lev F A ∈ (commutator (SpecialLinearGroup (Fin 2) F)).map (lev F) := ⟨A, hAc, rfl⟩
      rw [commutator_def, Subgroup.map_commutator] at h2
      have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)).map (lev F) ≤ parK F := by
        rintro _ ⟨B, -, rfl⟩
        exact lev_mem_parK B
      exact Subgroup.commutator_mono hle hle h2
    have : g = g * (lev F A)⁻¹ * lev F A := by group
    rw [this]
    exact mul_mem (radU_le_commutator ht0 ht1 hu) hlev

theorem mul_apply_two_two {g h : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ stabilizer (flagSpace 3 F 2)) :
    (g * h).val 2 2 = g.val 2 2 * h.val 2 2 := by
  rw [mem_stabilizer_flagSpace_iff] at hg
  have h20 := hg 2 0 (by norm_num) (by norm_num)
  have h21 := hg 2 1 (by norm_num) (by norm_num)
  show (g.val * h.val) 2 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
  ring

theorem commutator_stabilizer_le_parK :
    ⁅stabilizer (flagSpace 3 F 2), stabilizer (flagSpace 3 F 2)⁆ ≤ parK F := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hc : ⁅g, h⁆ ∈ stabilizer (flagSpace 3 F 2) :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hc' := hc
  rw [mem_stabilizer_flagSpace_iff] at hc'
  have hinv : ∀ x ∈ stabilizer (flagSpace 3 F 2), x.val 2 2 * (x⁻¹).val 2 2 = 1 := by
    intro x hx
    rw [← mul_apply_two_two hx, mul_inv_cancel]
    rfl
  refine ⟨hc' 2 0 (by norm_num) (by norm_num), hc' 2 1 (by norm_num) (by norm_num), ?_⟩
  rw [commutatorElement_def, mul_apply_two_two (mul_mem (mul_mem hg hh) (inv_mem hg)),
    mul_apply_two_two (mul_mem hg hh), mul_apply_two_two hg]
  calc g.val 2 2 * h.val 2 2 * (g⁻¹).val 2 2 * (h⁻¹).val 2 2 =
      (g.val 2 2 * (g⁻¹).val 2 2) * (h.val 2 2 * (h⁻¹).val 2 2) := by ring
    _ = 1 := by rw [hinv g hg, hinv h hh, one_mul]

theorem perfectResidual_stabilizer_eq [Finite F] (hF4 : 4 ≤ Nat.card F) :
    inSubgroup perfectResidual ((stabilizer (flagSpace 3 F 2)).map (proj 3 F)) =
      (parK F).map (proj 3 F) := by
  set P := (stabilizer (flagSpace 3 F 2)).map (proj 3 F) with hP
  apply le_antisymm
  · have h1 : perfectResidual P ≤ commutator P := by
      rw [← derivedSeries_one]
      exact iInf_le _ 1
    have h2 : (commutator P).map P.subtype = ⁅P, P⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    calc inSubgroup perfectResidual P = (perfectResidual P).map P.subtype := rfl
      _ ≤ (commutator P).map P.subtype := Subgroup.map_mono h1
      _ = ⁅P, P⁆ := h2
      _ = (⁅stabilizer (flagSpace 3 F 2), stabilizer (flagSpace 3 F 2)⁆).map (proj 3 F) := by
          rw [hP, Subgroup.map_commutator]
      _ ≤ (parK F).map (proj 3 F) := Subgroup.map_mono commutator_stabilizer_le_parK
  · have hperf : Group.IsPerfect ((parK F).map (proj 3 F)) := by
      have := isPerfect_parK hF4
      exact Group.IsPerfect.ofSurjective (f := (proj 3 F).subgroupMap (parK F))
        ((proj 3 F).subgroupMap_surjective (parK F))
    exact CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
      (Subgroup.map_mono parK_le_stabilizer) hperf

end ProofKS1624KP1

end CFSG.RankThree.PartTwo.Sec16
