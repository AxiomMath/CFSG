module

public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndKFact

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1910Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Matrices

variable {F : Type} [Field F]

theorem eq_zero_of_mul_eq_mul {x a b : F} (h : x * a = b * x) (hab : a ≠ b) : x = 0 := by
  by_contra hx
  exact hab (mul_left_cancel₀ hx (by rw [h, mul_comm]))

theorem eq_of_mul_eq_mul {x a b : F} (h : x * a = b * x) (hx : x ≠ 0) : b = a :=
  (mul_left_cancel₀ hx (by rw [h, mul_comm])).symm

theorem sq_add_add_one_eq_zero {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

theorem cube_root_facts {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    ω ≠ 0 ∧ ω ^ 2 ≠ 1 ∧ ω ≠ ω ^ 2 := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  refine ⟨hω0, fun h => hω1 ?_, fun h => hω1 ?_⟩
  · calc ω = ω ^ 2 * ω := by rw [h, one_mul]
      _ = ω ^ 3 := (pow_succ ω 2).symm
      _ = 1 := hω3
  · have h2 : ω * ω = ω * 1 := by rw [mul_one]; rw [sq] at h; exact h.symm
    exact mul_left_cancel₀ hω0 h2

theorem false_of_mul_self_eq_diagonal {Y : Matrix (Fin 3) (Fin 3) F} {e : Fin 3 → F}
    (he : Y * Y = diagonal e) {i : Fin 3} (hi : Y i i = 0) {m : ℕ}
    (hm : Y ^ (2 * m + 1) = 1) : False := by
  have h1 : Y ^ (2 * m + 1) = Y * diagonal (e ^ m) := by
    rw [pow_succ', pow_mul, sq, he, diagonal_pow]
  have h2 := congrFun (congrFun h1 i) i
  rw [hm, mul_diagonal, hi, zero_mul, one_apply_eq] at h2
  exact one_ne_zero h2

theorem diagonal_of_conj_diagonal {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {Y : Matrix (Fin 3) (Fin 3) F} {δ : Fin 3 → F}
    (hcomm : Y * diagonal ![ω, ω ^ 2, 1] = diagonal δ * Y) (hdet : Y.det = 1)
    (hflag : (Y 1 0 = 0 ∧ Y 2 0 = 0) ∨ (Y 2 0 = 0 ∧ Y 2 1 = 0)) {m : ℕ}
    (hm : Y ^ (2 * m + 1) = 1) : ∀ i j, i ≠ j → Y i j = 0 := by
  obtain ⟨hω0, hω21, hωω2⟩ := cube_root_facts hω1 hω3
  have key : ∀ i j, Y i j * ![ω, ω ^ 2, 1] j = δ i * Y i j := fun i j => by
    have h := congrFun (congrFun hcomm i) j
    rwa [mul_diagonal, diagonal_mul] at h
  have k00 : Y 0 0 * ω = δ 0 * Y 0 0 := key 0 0
  have k01 : Y 0 1 * ω ^ 2 = δ 0 * Y 0 1 := key 0 1
  have k02 : Y 0 2 * 1 = δ 0 * Y 0 2 := key 0 2
  have k10 : Y 1 0 * ω = δ 1 * Y 1 0 := key 1 0
  have k11 : Y 1 1 * ω ^ 2 = δ 1 * Y 1 1 := key 1 1
  have k12 : Y 1 2 * 1 = δ 1 * Y 1 2 := key 1 2
  have k21 : Y 2 1 * ω ^ 2 = δ 2 * Y 2 1 := key 2 1
  have k22 : Y 2 2 * 1 = δ 2 * Y 2 2 := key 2 2
  have k20 : Y 2 0 * ω = δ 2 * Y 2 0 := key 2 0
  rw [det_fin_three] at hdet
  have hw1 : (1 : F) ≠ ω := Ne.symm hω1
  have hw21 : (1 : F) ≠ ω ^ 2 := Ne.symm hω21
  rcases hflag with ⟨h10, h20⟩ | ⟨h20, h21⟩
  ·
    rw [h10, h20] at hdet
    have hY00 : Y 0 0 ≠ 0 := by
      rintro h
      rw [h] at hdet
      simp at hdet
    have hδ0 : δ 0 = ω := eq_of_mul_eq_mul k00 hY00
    rw [hδ0] at k01 k02
    have h01 : Y 0 1 = 0 := eq_zero_of_mul_eq_mul k01 (Ne.symm hωω2)
    have h02 : Y 0 2 = 0 := eq_zero_of_mul_eq_mul k02 hw1
    by_cases h12 : Y 1 2 = 0
    · rw [h12] at hdet
      have hY11 : Y 1 1 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hY22 : Y 2 2 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hδ2 : δ 2 = 1 := eq_of_mul_eq_mul k22 hY22
      rw [hδ2] at k21
      have h21 : Y 2 1 = 0 := eq_zero_of_mul_eq_mul k21 (Ne.symm hw21)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exfalso
      have hδ1 : δ 1 = 1 := eq_of_mul_eq_mul k12 h12
      rw [hδ1] at k11
      have h11 : Y 1 1 = 0 := eq_zero_of_mul_eq_mul k11 (Ne.symm hw21)
      rw [h11] at hdet
      have hY21 : Y 2 1 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hδ2 : δ 2 = ω ^ 2 := eq_of_mul_eq_mul k21 hY21
      rw [hδ2] at k22
      have h22 : Y 2 2 = 0 := eq_zero_of_mul_eq_mul k22 hw21
      refine false_of_mul_self_eq_diagonal (e := ![Y 0 0 * Y 0 0, Y 1 2 * Y 2 1,
        Y 2 1 * Y 1 2]) ?_ h11 hm
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h11, h20, h22]
  ·
    rw [h20, h21] at hdet
    have hY22 : Y 2 2 ≠ 0 := by
      rintro h
      rw [h] at hdet
      simp at hdet
    have hδ2 : δ 2 = 1 := eq_of_mul_eq_mul k22 hY22
    by_cases h01 : Y 0 1 = 0
    · rw [h01] at hdet
      have hY00 : Y 0 0 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hY11 : Y 1 1 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hδ0 : δ 0 = ω := eq_of_mul_eq_mul k00 hY00
      have hδ1 : δ 1 = ω ^ 2 := eq_of_mul_eq_mul k11 hY11
      rw [hδ0] at k02
      rw [hδ1] at k10 k12
      have h10 : Y 1 0 = 0 := eq_zero_of_mul_eq_mul k10 hωω2
      have h02 : Y 0 2 = 0 := eq_zero_of_mul_eq_mul k02 hw1
      have h12 : Y 1 2 = 0 := eq_zero_of_mul_eq_mul k12 hw21
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exfalso
      have hδ0 : δ 0 = ω ^ 2 := eq_of_mul_eq_mul k01 h01
      rw [hδ0] at k00 k02
      have h00 : Y 0 0 = 0 := eq_zero_of_mul_eq_mul k00 hωω2
      rw [h00] at hdet
      have hY10 : Y 1 0 ≠ 0 := by
        rintro h
        rw [h] at hdet
        simp at hdet
      have hδ1 : δ 1 = ω := eq_of_mul_eq_mul k10 hY10
      rw [hδ1] at k11 k12
      have h11 : Y 1 1 = 0 := eq_zero_of_mul_eq_mul k11 (Ne.symm hωω2)
      have h02 : Y 0 2 = 0 := eq_zero_of_mul_eq_mul k02 hw21
      have h12 : Y 1 2 = 0 := eq_zero_of_mul_eq_mul k12 hw1
      refine false_of_mul_self_eq_diagonal (e := ![Y 0 1 * Y 1 0, Y 1 0 * Y 0 1,
        Y 2 2 * Y 2 2]) ?_ h00 hm
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h02, h11, h12, h20, h21]

theorem pow_three_eq_one_of_diag {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {s : Matrix (Fin 3) (Fin 3) F} (hs : ∀ i j, j < i → s i j = 0) (h0 : s 0 0 = ω)
    (h1 : s 1 1 = ω ^ 2) (h2 : s 2 2 = 1) : s ^ 3 = 1 := by
  have hω := sq_add_add_one_eq_zero hω1 hω3
  have h10 : s 1 0 = 0 := hs 1 0 (by decide)
  have h20 : s 2 0 = 0 := hs 2 0 (by decide)
  have h21 : s 2 1 = 0 := hs 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, h10, h20, h21]
  · linear_combination hω3
  · linear_combination (s 0 1 * ω ^ 2) * hω
  · linear_combination (s 0 2 + s 0 1 * s 1 2) * hω
  · linear_combination (ω ^ 3 + 1) * hω3
  · linear_combination (s 1 2 * (ω ^ 2 - ω + 1)) * hω

end Matrices

section Flag

variable {F : Type} [Field F]

open CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

@[expose] def dZero {ω : F} (hω3 : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal ![ω, ω ^ 2, 1], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    linear_combination hω3⟩

theorem coe_dZero {ω : F} (hω3 : ω ^ 3 = 1) :
    ((dZero hω3 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![ω, ω ^ 2, 1] :=
  rfl

theorem dZero_mem_upperTriangular {ω : F} (hω3 : ω ^ 3 = 1) :
    dZero hω3 ∈ upperTriangular 3 F := fun i j hij => by
  rw [coe_dZero, diagonal_apply_ne _ (ne_of_gt hij)]

theorem lower_eq_zero_of_mulVec {g : Matrix (Fin 3) (Fin 3) F}
    (h1 : g *ᵥ Pi.single 0 1 ∈ flagSpace 3 F 1) (h2 : g *ᵥ Pi.single 1 1 ∈ flagSpace 3 F 2) :
    ∀ i j : Fin 3, j < i → g i j = 0 := by
  have e1 := mem_flagSpace.mp h1
  have e2 := mem_flagSpace.mp h2
  have h10 : g 1 0 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 1 (by decide)
  have h20 : g 2 0 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 2 (by decide)
  have h21 : g 2 1 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e2 2 (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem single_zero_mem_flagSpace_one : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 1 :=
  mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (by rintro rfl; simp at hj) _

theorem single_one_mem_flagSpace_two : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 :=
  mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (by rintro rfl; simp at hj) _

theorem upperTriangular_eq_flagStabilizer :
    upperTriangular 3 F = flagStabilizer 3 F {1, 2} := by
  refine le_antisymm (upperTriangular_le_flagStabilizer _) fun g hg => ?_
  have hst := mem_flagStabilizer.mp hg
  have hmv : ∀ i ∈ ({1, 2} : Set ℕ), ∀ v ∈ flagSpace 3 F i,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ flagSpace 3 F i := fun i hi v hv => by
    rw [← mem_stabilizer.mp (hst i hi)]
    exact ⟨v, hv, rfl⟩
  exact lower_eq_zero_of_mulVec (hmv 1 (by simp) _ single_zero_mem_flagSpace_one)
    (hmv 2 (by simp) _ single_one_mem_flagSpace_two)

theorem lower_eq_zero_of_glConj [Finite F] {g : GL (Fin 3) F}
    (hg : ∀ s ∈ upperTriangular 3 F, glConj g s ∈ upperTriangular 3 F) :
    ∀ i j : Fin 3, j < i → (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  rw [upperTriangular_eq_flagStabilizer] at hg
  have hg' := glConj_inv_mem hg
  have hI : ∀ j ∈ ({1, 2} : Set ℕ), j < 3 := by
    intro j hj
    rcases hj with rfl | rfl <;> norm_num
  exact lower_eq_zero_of_mulVec
    (mulVec_mem_flagSpace hI (by simp) le_rfl hg' _ single_zero_mem_flagSpace_one)
    (mulVec_mem_flagSpace hI (by simp) (by norm_num) hg' _ single_one_mem_flagSpace_two)

end Flag

section Aut

variable {F : Type} [Field F]

open CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

theorem two_lt_card {ω : F} [Fintype F] (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    2 < Fintype.card F := by
  classical
  obtain ⟨hω0, -, -⟩ := cube_root_facts hω1 hω3
  have h : ({0, 1, ω} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hω1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, Ne.symm hω0⟩
  have := Finset.card_le_univ ({0, 1, ω} : Finset F)
  omega

theorem exists_glConj_fieldAut [Finite F] [CharP F 2] {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {w : MulAut (SpecialLinearGroup (Fin 3) F)} (hw : w ^ 3 = 1) :
    ∃ τ : F ≃+* F, τ ω = ω ∧ ∃ g : GL (Fin 3) F, ∀ s : SpecialLinearGroup (Fin 3) F,
      w s = glConj g (slFieldAut (Fin 3) F τ s) := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hK : Sec4.PiField true 2 n F :=
    ⟨Nat.prime_two, n.pos, by rw [Nat.card_eq_fintype_card, hn]; rfl⟩
  have hq2 : 2 < 2 ^ (n : ℕ) := hn ▸ two_lt_card hω1 hω3
  set e := Sec4.slPiTrueEquiv (2 ^ (n : ℕ)) F with he
  set ζ := MulAut.congr e.symm w with hζdef
  have hζ : ζ ^ 3 = 1 := by rw [hζdef, ← map_pow, hw, map_one]
  obtain ⟨τ, hτ, g, hg⟩ := KFacts.exists_semiAct_of_pow_three_eq_one hK hq2 hζ
  refine ⟨τ, ?_, g, fun s => ?_⟩
  · rcases hτ with rfl | hτ3
    · rfl
    · obtain ⟨hω0, hω21, -⟩ := cube_root_facts hω1 hω3
      refine KFacts.ringAut_fixed_of_add_inv (Sec4.ringAut_apply_three hτ3) hω0 hω21 ?_
      have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hω3)
      rw [hinv, show ω + ω ^ 2 = -1 by linear_combination sq_add_add_one_eq_zero hω1 hω3,
        map_neg, map_one]
  · apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_glConj, Sec4.toGL_slFieldAut]
    have h1 := hg (e.symm s)
    have h2 : ζ (e.symm s) = e.symm (w s) := by
      rw [hζdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    have h3 : ∀ x : SpecialLinearGroup (Fin 3) F,
        ((e.symm x : Sec4.slPi true 3 (2 ^ (n : ℕ)) F) : GL (Fin 3) F) =
          Matrix.SpecialLinearGroup.toGL x := fun x => by
      rw [← Sec4.toGL_slPiTrueEquiv (e.symm x), he, MulEquiv.apply_symm_apply]
    rw [h2, h3, h3] at h1
    exact h1

end Aut

section Core

variable {F : Type} [Field F]

open CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

theorem coe_slFieldAut_apply (τ : F ≃+* F) (s : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    (slFieldAut (Fin 3) F τ s : Matrix (Fin 3) (Fin 3) F) i j =
      τ ((s : Matrix (Fin 3) (Fin 3) F) i j) :=
  rfl

theorem slFieldAut_mem_upperTriangular (τ : F ≃+* F) {s : SpecialLinearGroup (Fin 3) F}
    (hs : s ∈ upperTriangular 3 F) : slFieldAut (Fin 3) F τ s ∈ upperTriangular 3 F :=
  fun i j hij => by rw [coe_slFieldAut_apply, hs i j hij, map_zero]

@[expose] def diagSet (ω : F) : Set (SpecialLinearGroup (Fin 3) F) :=
  {s | s ∈ upperTriangular 3 F ∧ (s : Matrix (Fin 3) (Fin 3) F) 0 0 = ω ∧
    (s : Matrix (Fin 3) (Fin 3) F) 1 1 = ω ^ 2 ∧ (s : Matrix (Fin 3) (Fin 3) F) 2 2 = 1}

theorem card_diagSet {ω : F} (hω3 : ω ^ 3 = 1) :
    Nat.card (diagSet ω) = Nat.card (unitriangular 3 F) := by
  set d := dZero hω3 with hd
  have hdB := dZero_mem_upperTriangular hω3
  have hdT : (d : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hdB
  have hdii : ∀ i : Fin 3, (d : Matrix (Fin 3) (Fin 3) F) i i = ![ω, ω ^ 2, 1] i := fun i => by
    rw [hd, coe_dZero, diagonal_apply_eq]
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun u => ⟨d * u, (upperTriangular 3 F).mul_mem hdB u.2.1, ?_⟩
      invFun := fun s => ⟨d⁻¹ * s, (upperTriangular 3 F).mul_mem
        ((upperTriangular 3 F).inv_mem hdB) s.2.1, ?_⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  · have huT : (u : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.mp u.2.1
    have hm : ∀ i, ((d * u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
        ![ω, ω ^ 2, 1] i := fun i => by
      change ((d : Matrix (Fin 3) (Fin 3) F) * ((u : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)) i i = _
      rw [mul_apply_self_of_isUpperTriangular hdT huT, u.2.2 i, mul_one, hdii]
    exact ⟨hm 0, hm 1, hm 2⟩
  · have hsT : ((s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.mp s.2.1
    have hiT := coe_inv_isUpperTriangular hdT
    have hsii : ∀ i, ((s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
        (d : Matrix (Fin 3) (Fin 3) F) i i := by
      intro i
      rw [hdii]
      fin_cases i
      · exact s.2.2.1
      · exact s.2.2.2.1
      · exact s.2.2.2.2
    intro i
    change (((d⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i i = 1
    rw [mul_apply_self_of_isUpperTriangular hiT hsT, hsii, mul_comm]
    exact coe_inv_apply_self_of_isUpperTriangular hdT i

theorem exists_fixed_of_normalizes_unitriangular [Finite F] [CharP F 2] {ω : F} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) (W : Subgroup (MulAut (SpecialLinearGroup (Fin 3) F)))
    (hW : ∀ w ∈ W, w ^ 3 = 1)
    (hWU : ∀ w ∈ W, ∀ u ∈ unitriangular 3 F, w u ∈ unitriangular 3 F) :
    ∃ x : SpecialLinearGroup (Fin 3) F, x ^ 3 = 1 ∧
      x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) ∧ ∀ w ∈ W, w x = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWB : ∀ w ∈ W, ∀ b ∈ upperTriangular 3 F, w b ∈ upperTriangular 3 F := by
    intro w hw b hb
    rw [← normalizer_unitriangular] at hb ⊢
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hu' := hWU w⁻¹ (W.inv_mem hw) u hu
    have h1 := hWU w hw _ ((Subgroup.mem_normalizer_iff.mp hb _).mp hu')
    rwa [map_mul, map_mul, map_inv, MulAut.apply_inv_self] at h1
  have hWS : ∀ w ∈ W, ∀ s ∈ diagSet ω, w s ∈ diagSet ω := by
    intro w hw s hs
    obtain ⟨τ, hτω, g, hg⟩ := exists_glConj_fieldAut hω1 hω3 (hW w hw)
    have hgB : ∀ t ∈ upperTriangular 3 F, glConj g t ∈ upperTriangular 3 F := by
      intro t ht
      have h := hWB w hw _ (slFieldAut_mem_upperTriangular τ⁻¹ ht)
      rwa [hg, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h
    have hgT : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      fun i j hij => lower_eq_zero_of_glConj hgB i j hij
    have hwsT :
        ((w s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.mp (hWB w hw s hs.1)
    have hτsT : ((slFieldAut (Fin 3) F τ s : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.mp (slFieldAut_mem_upperTriangular τ hs.1)
    have hmat : ((w s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) *
          ((slFieldAut (Fin 3) F τ s : SpecialLinearGroup (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) := by
      rw [hg, coe_glConj, Matrix.mul_assoc _ (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)),
        Units.inv_mul, Matrix.mul_one]
    have hgii : ∀ i, (g : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
      intro i
      have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) F).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [det_of_isUpperTriangular hgT] at hu
      exact Finset.prod_ne_zero_iff.mp hu.ne_zero i (Finset.mem_univ i)
    have hdiag : ∀ i, ((w s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
        τ ((s : Matrix (Fin 3) (Fin 3) F) i i) := by
      intro i
      have h := congrFun (congrFun hmat i) i
      rw [mul_apply_self_of_isUpperTriangular hwsT hgT,
        mul_apply_self_of_isUpperTriangular hgT hτsT, coe_slFieldAut_apply, mul_comm] at h
      exact mul_left_cancel₀ (hgii i) h
    refine ⟨hWB w hw s hs.1, ?_, ?_, ?_⟩
    · rw [hdiag, hs.2.1, hτω]
    · rw [hdiag, hs.2.2.1, map_pow, hτω]
    · rw [hdiag, hs.2.2.2, map_one]
  have hWp : IsPGroup 3 W := fun w => ⟨1, Subtype.ext (by simpa using hW w w.2)⟩
  let act : MulAction W (diagSet ω) :=
    { smul := fun w s => ⟨(w : MulAut _) s, hWS w w.2 s s.2⟩
      one_smul := fun s => Subtype.ext rfl
      mul_smul := fun a b s => Subtype.ext rfl }
  have hcard : ¬ 3 ∣ Nat.card (diagSet ω) := by
    let _ := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [card_diagSet hω3, card_unitriangular, Nat.card_eq_fintype_card, hn]
    intro h
    have h2 := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h)
    norm_num at h2
  obtain ⟨⟨x, hx⟩, hfix⟩ := hWp.nonempty_fixed_point_of_prime_not_dvd_card (diagSet ω) hcard
  refine ⟨x, ?_, ?_, fun w hw => congrArg Subtype.val (hfix ⟨w, hw⟩)⟩
  · apply Subtype.ext
    change ((x : Matrix (Fin 3) (Fin 3) F) ^ 3) = 1
    exact pow_three_eq_one_of_diag hω1 hω3 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  · intro hxc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have h0 := congrFun (congrFun hr 0) 0
    have h2 := congrFun (congrFun hr 2) 2
    rw [hx.2.1] at h0
    rw [hx.2.2.2] at h2
    simp only [scalar_apply, diagonal_apply_eq] at h0 h2
    exact hω1 (h0.symm.trans h2)

end Core

section Index

variable {F : Type} [Field F]

theorem commutator_mem_unitriangular {r t : SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ upperTriangular 3 F) (ht : t ∈ upperTriangular 3 F) :
    r * t * r⁻¹ * t⁻¹ ∈ unitriangular 3 F := by
  have hrT := mem_upperTriangular_iff_isUpperTriangular.mp hr
  have htT := mem_upperTriangular_iff_isUpperTriangular.mp ht
  have hriT := coe_inv_isUpperTriangular hrT
  have htiT := coe_inv_isUpperTriangular htT
  refine ⟨(upperTriangular 3 F).mul_mem ((upperTriangular 3 F).mul_mem
    ((upperTriangular 3 F).mul_mem hr ht) ((upperTriangular 3 F).inv_mem hr))
    ((upperTriangular 3 F).inv_mem ht), fun i => ?_⟩
  change ((r : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
    ((r⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
    ((t⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i i = 1
  rw [mul_apply_self_of_isUpperTriangular ((hrT.mul htT).mul hriT) htiT,
    mul_apply_self_of_isUpperTriangular (hrT.mul htT) hriT,
    mul_apply_self_of_isUpperTriangular hrT htT]
  have h1 := coe_inv_apply_self_of_isUpperTriangular hrT i
  have h2 := coe_inv_apply_self_of_isUpperTriangular htT i
  calc (r : Matrix (Fin 3) (Fin 3) F) i i * (t : Matrix (Fin 3) (Fin 3) F) i i *
        ((r⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i *
        ((t⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
      ((r : Matrix (Fin 3) (Fin 3) F) i i *
        ((r⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) *
      ((t : Matrix (Fin 3) (Fin 3) F) i i *
        ((t⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

theorem not_three_dvd_relIndex [Finite F] [CharP F 2] {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hBP : upperTriangular 3 F ≤ P) (hP : P ≠ ⊤) :
    ¬ 3 ∣ (upperTriangular 3 F).relIndex P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h3
  obtain ⟨hω0, hω21, hωω2⟩ := cube_root_facts hω1 hω3
  set B := upperTriangular 3 F with hB
  have hQ : P = flagStabilizer 3 F (borelOvergroupCuts P) := (borel_overgroups P hBP).1
  obtain ⟨i, hi⟩ : (borelOvergroupCuts P).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    apply hP
    rw [hQ, hI, flagStabilizer_empty]
  obtain ⟨hi1, hi3, -⟩ := id hi
  set d := dZero hω3 with hd
  have hdB : d ∈ B := dZero_mem_upperTriangular hω3
  have hω6 : ω ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    change (diagonal ![ω, ω ^ 2, 1]) ^ 3 = 1
    rw [diagonal_pow]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hω3, hω6, ← pow_mul]
  have hz3 : IsPGroup 3 (Subgroup.zpowers (⟨d, hdB⟩ : B)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (Subtype.ext hd3) (fun h => hω1 (by
        have := congrArg (fun x : B => ((x : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 0) h
        simpa [hd, coe_dZero] using this)))
  obtain ⟨RB, hRB⟩ := hz3.exists_le_sylow
  set R := (RB : Subgroup B).map B.subtype with hR
  have hRB3 : IsPGroup 3 R := RB.isPGroup'.map _
  have hRle : R ≤ B := Subgroup.map_subtype_le _
  have hdR : d ∈ R := ⟨⟨d, hdB⟩, hRB (Subgroup.mem_zpowers _), rfl⟩
  have hU2 : IsPGroup 2 (unitriangular 3 F) := by
    let _ := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    refine IsPGroup.of_card (n := n * 3) ?_
    rw [card_unitriangular, Nat.card_eq_fintype_card, hn, ← pow_mul]
  have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hRB3 hU2
  have hRcomm : ∀ r ∈ R, ∀ t ∈ R, r * t = t * r := by
    intro r hr t ht
    have h1 : r * t * r⁻¹ * t⁻¹ ∈ R := R.mul_mem (R.mul_mem (R.mul_mem hr ht) (R.inv_mem hr))
      (R.inv_mem ht)
    have h2 := commutator_mem_unitriangular (hRle hr) (hRle ht)
    have h3' := Subgroup.disjoint_def.mp hdisj h1 h2
    calc r * t = r * t * r⁻¹ * t⁻¹ * (t * r) := by group
      _ = t * r := by rw [h3', one_mul]
  have hdiagR : ∀ r ∈ R, ∀ a b : Fin 3, a ≠ b → (r : Matrix (Fin 3) (Fin 3) F) a b = 0 := by
    intro r hr a b hab
    have hc : (r : Matrix (Fin 3) (Fin 3) F) * diagonal ![ω, ω ^ 2, 1] =
        diagonal ![ω, ω ^ 2, 1] * (r : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F))
        (hRcomm r hr d hdR)
      simpa [hd, coe_dZero] using this
    refine Sec4.entry_eq_zero_of_commute_diagonal hc ?_
    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;>
      first
      | exact hωω2 | exact hωω2.symm | exact hω1 | exact (Ne.symm hω1) | exact hω21
      | exact (Ne.symm hω21) | exact ⟨hω1, by rw [CharTwo.neg_eq]; exact hω1⟩
  have hRP : R ≤ P := hRle.trans hBP
  have hRP3 : IsPGroup 3 (R.subgroupOf P) := hRB3.comap_subtype
  obtain ⟨RP, hRPle⟩ := hRP3.exists_le_sylow
  set R' := (RP : Subgroup P).map P.subtype with hR'
  have hR'3 : IsPGroup 3 R' := RP.isPGroup'.map _
  have hRR' : R ≤ R' := fun r hr => ⟨⟨r, hRP hr⟩, hRPle (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hR'P : R' ≤ P := Subgroup.map_subtype_le _
  have hcardR : Nat.card R = 3 ^ (Nat.card B).factorization 3 := by
    rw [hR, Subgroup.card_map_of_injective B.subtype_injective, Sylow.card_eq_multiplicity]
  have hcardR' : Nat.card R' = 3 ^ (Nat.card P).factorization 3 := by
    rw [hR', Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity]
  have hP_card : Nat.card P = B.relIndex P * Nat.card B := by
    rw [← Subgroup.relIndex_mul_card, inf_eq_left.mpr hBP]
  have hrel0 : B.relIndex P ≠ 0 := by
    intro h0
    have := Nat.card_pos (α := P)
    rw [hP_card, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hlt : Nat.card R < Nat.card R' := by
    rw [hcardR, hcardR', hP_card, Nat.factorization_mul hrel0 Nat.card_pos.ne', Finsupp.add_apply]
    have h1 := Nat.prime_three.factorization_pos_of_dvd hrel0 h3
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  set H := R.subgroupOf R' with hH
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hle : R' ≤ R := fun r hr => by
      have : (⟨r, hr⟩ : R') ∈ H := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr hlt)
  have : Group.IsNilpotent R' := hR'3.isNilpotent
  obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hHtop))
  have hyR : (y : SpecialLinearGroup (Fin 3) F) ∉ R := fun h => hyH (Subgroup.mem_subgroupOf.mpr h)
  have hyP : (y : SpecialLinearGroup (Fin 3) F) ∈ P := hR'P y.2
  have hynorm : ∀ r ∈ R, (y : SpecialLinearGroup (Fin 3) F) * r * (y : SpecialLinearGroup
      (Fin 3) F)⁻¹ ∈ R := by
    intro r hr
    have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨r, hRR' hr⟩).mp
      (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨k, hk⟩ := hR'3 y
  have hyk : (y : SpecialLinearGroup (Fin 3) F) ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  set Y := ((y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hYdef
  have hconj := hdiagR _ (hynorm d hdR)
  set δ : Fin 3 → F := fun a => (((y : SpecialLinearGroup (Fin 3) F) * d *
    (y : SpecialLinearGroup (Fin 3) F)⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) a a with hδ
  have hD : (((y : SpecialLinearGroup (Fin 3) F) * d * (y : SpecialLinearGroup (Fin 3) F)⁻¹ :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal δ := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hab, hconj a b hab]
  have hcomm : Y * diagonal ![ω, ω ^ 2, 1] = diagonal δ * Y := by
    rw [← hD]
    change Y * (d : Matrix (Fin 3) (Fin 3) F) = (((y : SpecialLinearGroup (Fin 3) F) * d *
      (y : SpecialLinearGroup (Fin 3) F)⁻¹ * (y : SpecialLinearGroup (Fin 3) F) :
        SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [inv_mul_cancel_right]
    rfl
  have hyst : (y : SpecialLinearGroup (Fin 3) F) ∈ stabilizer (flagSpace 3 F i) :=
    mem_flagStabilizer.mp (hQ ▸ hyP) i hi
  have hmv : ∀ v ∈ flagSpace 3 F i, Y *ᵥ v ∈ flagSpace 3 F i := fun v hv => by
    rw [← mem_stabilizer.mp hyst]
    exact ⟨v, hv, rfl⟩
  have hflag : (Y 1 0 = 0 ∧ Y 2 0 = 0) ∨ (Y 2 0 = 0 ∧ Y 2 1 = 0) := by
    have hi12 : i = 1 ∨ i = 2 := by omega
    rcases hi12 with rfl | rfl
    · have e1 := mem_flagSpace.mp (hmv _ single_zero_mem_flagSpace_one)
      left
      exact ⟨by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 1 (by decide),
        by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 2 (by decide)⟩
    · have e0 := mem_flagSpace.mp (hmv (Pi.single 0 1) (mem_flagSpace.mpr fun j hj =>
        Pi.single_eq_of_ne (by rintro rfl; simp at hj) _))
      have e1 := mem_flagSpace.mp (hmv _ single_one_mem_flagSpace_two)
      right
      exact ⟨by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e0 2 (by decide),
        by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 2 (by decide)⟩
  have hYodd : Y ^ (2 * m + 1) = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F))
      hyk
    rw [hm] at h
    simpa [hYdef] using h
  have hYdiag := diagonal_of_conj_diagonal hω1 hω3 hcomm (y : SpecialLinearGroup (Fin 3) F).2
    hflag hYodd
  have hyB : (y : SpecialLinearGroup (Fin 3) F) ∈ B := fun a b hab => hYdiag a b (ne_of_gt hab)
  set yB : B := ⟨y, hyB⟩ with hyBdef
  have hzN : Subgroup.zpowers yB ≤ Subgroup.normalizer ((RB : Subgroup B) : Set B) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have h1 := hynorm (r : SpecialLinearGroup (Fin 3) F) ⟨r, hr, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := h1
    have : r' = yB * r * yB⁻¹ := Subtype.ext hr'e
    rw [← this]
    exact hr'
  have hz3' : IsPGroup 3 (Subgroup.zpowers yB) := by
    have hyBk : yB ^ 3 ^ k = 1 := Subtype.ext (by simpa [hyBdef] using hyk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyBk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hsup := RB.is_maximal' (hz3'.to_sup_of_normal_right' RB.isPGroup' hzN) le_sup_right
  apply hyR
  have hmem : yB ∈ (RB : Subgroup B) := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers yB)
  exact ⟨yB, hmem, rfl⟩

end Index

section Sylow

open scoped Pointwise

@[expose] def restrictAut {X : Type*} [Group X] (W : Subgroup (MulAut X)) (P : Subgroup X)
    (hWP : ∀ w ∈ W, ∀ p ∈ P, w p ∈ P) : W →* MulAut P where
  toFun w :=
    { toFun := fun q => ⟨(w : MulAut X) q, hWP w w.2 q q.2⟩
      invFun := fun q => ⟨((w : MulAut X)⁻¹) q, hWP _ (W.inv_mem w.2) q q.2⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp)
      map_mul' := fun q r => Subtype.ext (by simp) }
  map_one' := by
    ext q
    rfl
  map_mul' w v := by
    ext q
    rfl

variable {F : Type} [Field F]

theorem exists_conj_unitriangular_fixed [Finite F] [CharP F 2] {ω : F} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) (W : Subgroup (MulAut (SpecialLinearGroup (Fin 3) F)))
    (hW3 : IsPGroup 3 W) {P : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hBP : upperTriangular 3 F ≤ P) (hP : P ≠ ⊤) (hWP : ∀ w ∈ W, ∀ p ∈ P, w p ∈ P) :
    ∃ x : SpecialLinearGroup (Fin 3) F, ∀ w ∈ W, ∀ u ∈ unitriangular 3 F,
      x⁻¹ * w (x * u * x⁻¹) * x ∈ unitriangular 3 F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hUP : (SU : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ P :=
    hSU ▸ (unitriangular_le_upperTriangular 3 F).trans hBP
  set S0 := SU.subtype hUP with hS0
  have hS0U : (S0 : Subgroup P) = (unitriangular 3 F).subgroupOf P := by
    rw [hS0, Sylow.coe_subtype, hSU]
  let ρ := restrictAut W P hWP
  let act : MulAction W (Sylow 2 P) := MulAction.compHom _ ρ
  have hcard : ¬ 3 ∣ Nat.card (Sylow 2 P) := by
    rw [Sylow.card_eq_index_normalizer S0]
    intro h
    apply not_three_dvd_relIndex hω1 hω3 hBP hP
    refine h.trans (Subgroup.index_dvd_of_le fun b hb => ?_)
    have hbN : (b : SpecialLinearGroup (Fin 3) F) ∈
        Subgroup.normalizer (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F)) := by
      rw [normalizer_unitriangular]
      exact Subgroup.mem_subgroupOf.mp hb
    change b ∈ Subgroup.normalizer ((S0 : Subgroup P) : Set P)
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hS0U, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hbN q)
  obtain ⟨S, hS⟩ := hW3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 P) hcard
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P S0 S
  refine ⟨p, fun w hw u hu => ?_⟩
  have huP : u ∈ P := hBP ((unitriangular_le_upperTriangular 3 F) hu)
  set q : P := p * ⟨u, huP⟩ * p⁻¹ with hq
  have hqS : q ∈ (S : Subgroup P) := by
    rw [← hp, coe_sylow_smul]
    exact ⟨⟨u, huP⟩, by rw [hS0U]; exact Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hfix : (⟨w, hw⟩ : W) • S = S := hS ⟨w, hw⟩
  have h1 : ρ ⟨w, hw⟩ • q ∈ ρ ⟨w, hw⟩ • (S : Subgroup P) :=
    Subgroup.smul_mem_pointwise_smul q _ _ hqS
  rw [← Sylow.pointwise_smul_def] at h1
  change ρ ⟨w, hw⟩ q ∈ (((⟨w, hw⟩ : W) • S : Sylow 2 P) : Subgroup P) at h1
  rw [hfix, ← hp, coe_sylow_smul] at h1
  obtain ⟨y, hy, hye⟩ := h1
  rw [hS0U] at hy
  have hy' := Subgroup.mem_subgroupOf.mp hy
  have hye' : (p : SpecialLinearGroup (Fin 3) F) * y * (p : SpecialLinearGroup (Fin 3) F)⁻¹ =
      w ((p : SpecialLinearGroup (Fin 3) F) * u * (p : SpecialLinearGroup (Fin 3) F)⁻¹) :=
    congrArg Subtype.val hye
  have : (y : SpecialLinearGroup (Fin 3) F) =
      (p : SpecialLinearGroup (Fin 3) F)⁻¹ * w ((p : SpecialLinearGroup (Fin 3) F) * u *
        (p : SpecialLinearGroup (Fin 3) F)⁻¹) * (p : SpecialLinearGroup (Fin 3) F) := by
    rw [← hye']
    group
  rw [← this]
  exact hy'

end Sylow

section KFact

variable {F : Type} [Field F]

theorem exists_fixed_of_conj {X : Type*} [Group X] (σ : MulAut X) (W : Subgroup (MulAut X))
    (h : ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X ∧
      ∀ w ∈ W.map (MulAut.conj σ⁻¹).toMonoidHom, w x = x) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X ∧ ∀ w ∈ W, w x = x := by
  obtain ⟨x, h3, hc, hf⟩ := h
  refine ⟨σ x, by rw [← map_pow, h3, map_one], fun hσc => hc ?_, fun w hw => ?_⟩
  · rw [Subgroup.mem_center_iff] at hσc ⊢
    intro g
    apply σ.injective
    rw [map_mul, map_mul]
    exact hσc (σ g)
  · have h1 := hf _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.mul_apply] at h1
    calc w (σ x) = σ (σ⁻¹ (w (σ x))) := by rw [MulAut.apply_inv_self]
      _ = σ x := by rw [h1]

theorem pow_three_of_mem_map_conj {X : Type*} [Group X] (σ : MulAut X)
    {W : Subgroup (MulAut X)} (hW : ∀ w ∈ W, w ^ 3 = 1) :
    ∀ w ∈ W.map (MulAut.conj σ⁻¹).toMonoidHom, w ^ 3 = 1 := by
  rintro _ ⟨w, hw, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_pow, hW w hw, map_one]

theorem slThreeFixedOfParabolic :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ω : F), ω ≠ 1 → ω ^ 3 = 1 →
      ∀ W : Subgroup (MulAut (SpecialLinearGroup (Fin 3) F)), (∀ w ∈ W, w ^ 3 = 1) →
      ∀ P : Subgroup (SpecialLinearGroup (Fin 3) F), IsProperParabolic P →
        (∀ w ∈ W, ∀ p ∈ P, w p ∈ P) →
        ∃ x : SpecialLinearGroup (Fin 3) F, x ^ 3 = 1 ∧
          x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) ∧ ∀ w ∈ W, w x = x := by
  intro F _ _ _ ω hω1 hω3 W hW P hP hWP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hP
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x₀, hx₀⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) SU T
  set σ₀ := MulAut.conj x₀ with hσ₀
  set P₀ := P.comap (σ₀ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
    with hP₀
  have hN : Subgroup.normalizer ((T : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) =
      (upperTriangular 3 F).map (MulAut.conj x₀ : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) := by
    rw [← hx₀, coe_sylow_smul, hSU, normalizer_map_conj, normalizer_unitriangular]
  have hBP₀ : upperTriangular 3 F ≤ P₀ := fun b hb =>
    Subgroup.mem_comap.mpr (hT (hN ▸ Subgroup.mem_map_of_mem _ hb))
  have hP₀top : P₀ ≠ ⊤ := by
    intro htop
    apply hPtop
    rw [eq_top_iff]
    intro s _
    have hs : x₀⁻¹ * s * x₀ ∈ P₀ := by rw [htop]; exact Subgroup.mem_top _
    have := Subgroup.mem_comap.mp hs
    simpa [hσ₀, mul_assoc] using this
  set W₀ := W.map (MulAut.conj σ₀⁻¹).toMonoidHom with hW₀
  have hW₀3 := pow_three_of_mem_map_conj σ₀ hW
  have hW₀p : IsPGroup 3 W₀ := fun w => ⟨1, Subtype.ext (by simpa using hW₀3 w w.2)⟩
  have hW₀P : ∀ w ∈ W₀, ∀ p ∈ P₀, w p ∈ P₀ := by
    rintro _ ⟨w, hw, rfl⟩ p hp
    rw [hP₀, Subgroup.mem_comap] at hp ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.mul_apply,
      MonoidHom.coe_ofClass, MulAut.apply_inv_self]
    exact hWP w hw _ hp
  obtain ⟨x₁, hx₁⟩ := exists_conj_unitriangular_fixed hω1 hω3 W₀ hW₀p hBP₀ hP₀top hW₀P
  set σ₁ := MulAut.conj x₁ with hσ₁
  set W₁ := W₀.map (MulAut.conj σ₁⁻¹).toMonoidHom with hW₁
  have hW₁3 := pow_three_of_mem_map_conj σ₁ hW₀3
  have hW₁U : ∀ w ∈ W₁, ∀ u ∈ unitriangular 3 F, w u ∈ unitriangular 3 F := by
    rintro _ ⟨w, hw, rfl⟩ u hu
    have h := hx₁ w hw u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.mul_apply,
      hσ₁, MulAut.conj_inv_apply] at h ⊢
    exact h
  exact exists_fixed_of_conj σ₀ W (exists_fixed_of_conj σ₁ W₀
    (exists_fixed_of_normalizes_unitriangular hω1 hω3 W₁ hW₁3 hW₁U))

end KFact

end CFSG.RankThree.PartTwo.Sec19.Step1910Proof
