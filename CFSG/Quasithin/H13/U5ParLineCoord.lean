module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylC
public import CFSG.Milestones.ASVolI.F429.aC8U5
public import CFSG.Quasithin.Vol2.Ch6OrthIrred

public section

namespace CFSG.Quasithin.H13.U5Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5

variable {f : ℕ} {K : Type} [Field K]

section Block

variable {h : UnitaryFieldData 2 f K}

private theorem blkA_mul_of_mem_u5LnStab {g g' : hypSU h 2 1} (hg' : g' ∈ u5LnStab h) :
    blkA (mat (g * g')) = blkA (mat g) * blkA (mat g') := by
  ext i j
  change (mat (g * g')) (.inl i) (.inl j) = (blkA (mat g) * blkA (mat g')) i j
  rw [mat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Matrix.mul_apply]
  have hz : ∀ k : Fin 1, mat g' (.inr (.inl k)) (.inl j) = 0 := fun k =>
    CFSG.ASVolI.burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg' _ _
      (by simp [CFSG.ASVolI.burnsideF429a_lev])
  have hf : ∀ a : Fin 2, mat g' (.inr (.inr a)) (.inl j) = 0 := fun a =>
    CFSG.ASVolI.burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg' _ _
      (by simp [CFSG.ASVolI.burnsideF429a_lev])
  simp only [hz, hf, mul_zero, Finset.sum_const_zero, zero_add, add_zero, blkA,
    Matrix.of_apply]

private theorem blkA_one :
    blkA (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkA]

private theorem blkA_oddUni (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) :
    blkA (oddUni h x C) = 1 := by
  ext i j
  rfl

private theorem blkA_oddDiag (A : Matrix (Fin 2) (Fin 2) K) (d : K) :
    blkA (oddDiag h A d) = A := by
  ext i j
  rfl

private theorem blkA_lev (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    blkA (mat (lev (hK := h) A hA)) = A := by
  rw [mat_lev]
  exact blkA_oddDiag A _

private theorem lev_mem_u5LnStab (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    lev A hA ∈ u5LnStab h := by
  rw [mem_u5LnStab_iff]
  intro a b hb ha
  rw [mat_lev]
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
    simp [oddDiag]

end Block

@[expose] noncomputable def lnBlk (h : UnitaryFieldData 2 f K) :
    ↥(u5LnStab h) →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => blkA (mat (g : hypSU h 2 1))
      map_one' := by
        rw [Subgroup.coe_one, mat_one]
        exact blkA_one
      map_mul' := fun g g' => by
        rw [Subgroup.coe_mul]
        exact blkA_mul_of_mem_u5LnStab g'.2 }

theorem lnBlk_coe {h : UnitaryFieldData 2 f K} (g : ↥(u5LnStab h)) :
    ((lnBlk h g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkA (mat (g : hypSU h 2 1)) :=
  rfl

section Kernel

variable {h : UnitaryFieldData 2 f K}

private theorem syl_decomp_of_mem_u5LnStab {g : hypSU h 2 1} (hg : g ∈ u5LnStab h) :
    ∃ (A C : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) (d : K), IsUnit A.det ∧
      C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
      d = h.bar A.det / A.det ∧ A = blkA (mat g) ∧
      mat g = oddDiag h A d * oddUni h x C := by
  obtain ⟨A, C, x, d, hA, hC, hd, hAeq, -, hmat⟩ :=
    CFSG.Quasithin.H13.F431.Un.L5.syl_decomp (g := g)
      (fun i => CFSG.ASVolI.burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg _ _
        (by simp [CFSG.ASVolI.burnsideF429a_lev]))
      (fun j i => CFSG.ASVolI.burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg _ _
        (by simp [CFSG.ASVolI.burnsideF429a_lev]))
      (fun j => CFSG.ASVolI.burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg _ _
        (by simp [CFSG.ASVolI.burnsideF429a_lev]))
  exact ⟨A, C, x, d, hA, hC, hd, hAeq, hmat⟩

theorem lnBlk_eq_one_iff {h : UnitaryFieldData 2 f K} (g : ↥(u5LnStab h)) :
    lnBlk h g = 1 ↔ (g : hypSU h 2 1) ∈ Ssub h := by
  constructor
  · intro hg
    have hblk : blkA (mat (g : hypSU h 2 1)) = 1 := by
      have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hg
      simpa [lnBlk_coe] using h
    obtain ⟨A, C, x, d, hA, hC, hd, hAeq, hmat⟩ := syl_decomp_of_mem_u5LnStab g.2
    have hA1 : A = 1 := by rw [hAeq]; exact hblk
    have hd1 : d = 1 := by
      rw [hd, hA1]
      simp
    refine mem_Ssub_of_mat (x := x) (C := C) ?_
    rw [hmat, hA1, hd1, oddDiag_one, one_mul]
  · intro hg
    obtain ⟨-, x, C, hx⟩ := hg
    apply Units.ext
    rw [lnBlk_coe, hx]
    exact blkA_oddUni x C

end Kernel

section Action

variable {h : UnitaryFieldData 2 f K}

private theorem Yof_one : Yof (1 : hypSU h 2 1) = 0 :=
  Yof_eq (by rw [mat_one, oddUni_zero])

private theorem eq_of_Yof_eq {v w : hypSU h 2 1} (hv : v ∈ Vsub h) (hw : w ∈ Vsub h)
    (h : Yof v = Yof w) : v = w :=
  Yof_ext hv hw (by rw [h]) (by rw [h]) (by rw [h])

theorem Yof_conj_of_mem_u5LnStab {g v : hypSU h 2 1} (hg : g ∈ u5LnStab h)
    (hv : v ∈ Vsub h) :
    Yof (g * v * g⁻¹) = blkA (mat g) * Yof v * ((blkA (mat g)).map h.bar)ᵀ := by
  obtain ⟨A, C, x, d, hA, hC, hd, hAeq, hmat⟩ := syl_decomp_of_mem_u5LnStab hg
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (x := x) (C := C) hC
  have hlev : mat (lev (hK := h) A hA) = oddDiag h A d := by
    rw [mat_lev, ← hd]
  have hgs : g = lev (hK := h) A hA * s := by
    apply mat_injective
    rw [mat_mul, hmat, hlev, hsm]
  have hcomm : s * v = v * s :=
    (commute_Vsub_iff (Ssub_le_Usub hs)).2 hs v hv
  have hconj : g * v * g⁻¹ = lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ := by
    rw [hgs]
    calc (lev (hK := h) A hA * s) * v * (lev (hK := h) A hA * s)⁻¹
        = lev (hK := h) A hA * (s * v * s⁻¹) * (lev (hK := h) A hA)⁻¹ := by group
      _ = lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ := by
          rw [hcomm, mul_inv_cancel_right]
  rw [hconj]
  obtain ⟨-, Y, hY⟩ := hv
  have hlc := lev_conj A hA hY
  simp only [mulVec_zero, smul_zero] at hlc
  rw [Yof_eq hlc, hAeq, Yof_eq hY]

theorem isHerm_iff_map_frob {h : UnitaryFieldData 2 f K}
    (Y : Matrix (Fin 2) (Fin 2) K) :
    IsHerm h Y ↔ Y.map (· ^ 2 ^ f) = Y.transpose := by
  haveI := h.charP
  have hmap : Y.map h.bar = Y.map (· ^ 2 ^ f) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]
  rw [IsHerm, ← hmap]
  constructor
  · intro hY
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hY
    have h' : Y.map h.bar = Y.transpose := by
      have := congrArg Matrix.transpose hY
      simpa using this.symm
    exact h'
  · intro hY
    rw [hY, Matrix.transpose_transpose, CharTwo.add_self_eq_zero]

private theorem frobPow_transpose_of_isHerm {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : IsHerm h Y) : (frobPow f Y)ᵀ = Y := by
  rw [frobPow, (isHerm_iff_map_frob Y).1 hY, Matrix.transpose_transpose]

private theorem frobPow_transpose_Yof {v : hypSU h 2 1} (hv : v ∈ Vsub h) :
    (frobPow f (Yof v))ᵀ = Yof v :=
  frobPow_transpose_of_isHerm (herm_Yof hv)

end Action

section Irreducible

variable {h : UnitaryFieldData 2 f K}

theorem Vsub_irreducible (R : Subgroup (hypSU h 2 1)) (hR : R ≤ Vsub h)
    (hL : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ r ∈ R,
      lev (A : Matrix (Fin 2) (Fin 2) K) (by simp) * r *
        (lev (A : Matrix (Fin 2) (Fin 2) K) (by simp))⁻¹ ∈ R) :
    R = ⊥ ∨ R = Vsub h := by
  haveI := h.charP
  haveI := h.finite
  letI : Fintype K := Fintype.ofFinite K
  by_cases hbot : R = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hrV : (r : hypSU h 2 1) ∈ Vsub h := hR r.2
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {Y | ∃ v : R, Yof (v : hypSU h 2 1) = Y}
      add_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
        exact ⟨v * v', by rw [Subgroup.coe_mul]; exact Yof_mul (hR v.2) (hR v'.2)⟩
      zero_mem' := ⟨1, Yof_one⟩
      neg_mem' := by
        rintro _ ⟨v, rfl⟩
        refine ⟨v⁻¹, ?_⟩
        have h := Yof_mul (hR (v⁻¹).2) (hR v.2)
        rw [Subgroup.coe_inv, inv_mul_cancel, Yof_one] at h
        exact eq_neg_of_add_eq_zero_left h.symm }
  have hS_le : S ≤ hermA f K := by
    rintro Y ⟨v, rfl⟩
    rw [mem_hermA]
    exact frobPow_transpose_Yof (hR v.2)
  have hS_inv : ∀ A : SL2 K, ∀ X ∈ S, twistActCh6 f A X ∈ S := by
    rintro A X ⟨v, rfl⟩
    have hmem := hL A v v.2
    refine ⟨⟨lev (A : Matrix (Fin 2) (Fin 2) K) (by simp) * (v : hypSU h 2 1) *
      (lev (A : Matrix (Fin 2) (Fin 2) K) (by simp))⁻¹, hmem⟩, ?_⟩
    have hmain := Yof_conj_of_mem_u5LnStab
      (lev_mem_u5LnStab (A : Matrix (Fin 2) (Fin 2) K) (by simp)) (hR v.2)
    have hfrob : frobPow f (A : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K).map h.bar := by
      ext i j
      simp [frobPow, UnitaryFieldData.bar_apply]
    rw [twistActCh6, hfrob]
    simpa [blkA_lev] using hmain
  have hcard : Fintype.card K = 2 ^ (2 * f) := by
    rw [Fintype.card_eq_nat_card, h.card]
  have hf : 0 < f := by
    have := h.one_le
    omega
  have hX₀0 : Yof (r : hypSU h 2 1) ≠ 0 := by
    intro h0
    apply hr
    apply Subtype.ext
    apply mat_injective
    obtain ⟨-, Y, hY⟩ := hrV
    have hY0 : Y = 0 := by rw [← Yof_eq hY]; exact h0
    rw [hY, hY0, oddUni_zero, Subgroup.coe_one, mat_one]
  have hle : hermA f K ≤ S :=
    hermA_le_of_invariant_ch6 hcard hf S hS_le hS_inv
      (X₀ := Yof (r : hypSU h 2 1)) ⟨r, rfl⟩ hX₀0
  refine le_antisymm hR ?_
  intro v hv
  obtain ⟨w, hw⟩ := hle (mem_hermA.mpr (frobPow_transpose_Yof hv))
  have hveq : v = (w : hypSU h 2 1) := eq_of_Yof_eq hv (hR w.2) hw.symm
  rw [hveq]
  exact w.2

end Irreducible

end CFSG.Quasithin.H13.U5Par

end
