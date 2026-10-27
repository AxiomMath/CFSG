module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section JFacts

private lemma finProdFinEquiv_blk (k : Fin 3) (j : Fin 2) :
    finProdFinEquiv (k, j) = blk k j := by
  apply Fin.ext
  rw [finProdFinEquiv_apply_val]
  show (j : ℕ) + 2 * (k : ℕ) = 2 * (k : ℕ) + (j : ℕ)
  omega

private lemma blk_eq_blk_iff {k l : Fin 3} {j j' : Fin 2} :
    blk k j = blk l j' ↔ k = l ∧ j = j' := by
  constructor
  · intro h
    have hv : 2 * (k : ℕ) + (j : ℕ) = 2 * (l : ℕ) + (j' : ℕ) := by
      simpa [blk] using congrArg Fin.val h
    constructor
    · apply Fin.ext; omega
    · apply Fin.ext; omega
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma blk_ne_of_ne {k l : Fin 3} (h : k ≠ l) (j : Fin 2) : blk k j ≠ blk l j :=
  fun hh => h (blk_eq_blk_iff.mp hh).1

private lemma blk_ne_of_ne' {k l : Fin 3} (h : k ≠ l) (j j' : Fin 2) :
    blk k j ≠ blk l j' :=
  fun hh => h (blk_eq_blk_iff.mp hh).1

private lemma resMat_single (k l : Fin 3) (c : F4) :
    resMat 3 (Matrix.single k l c) =
      Matrix.single (blk k 0) (blk l 0) (f4Eps c 0 0) +
      Matrix.single (blk k 0) (blk l 1) (f4Eps c 0 1) +
      Matrix.single (blk k 1) (blk l 0) (f4Eps c 1 0) +
      Matrix.single (blk k 1) (blk l 1) (f4Eps c 1 1) := by
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [resMat_apply]
  simp only [Matrix.add_apply, Matrix.single_apply, finProdFinEquiv_blk, blk_eq_blk_iff]
  by_cases hk : k = i <;> by_cases hl : l = i'
  · fin_cases j <;> fin_cases j' <;> simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]

private lemma resMat_single_one (k l : Fin 3) :
    resMat 3 (Matrix.single k l (1 : F4)) =
      Matrix.single (blk k 0) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [resMat_single, map_one]
  have h01 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 1 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 0 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h00 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 0 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  have h11 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  rw [h00, h01, h10, h11, Matrix.single_zero, Matrix.single_zero]
  abel

private lemma resMat_single_omega (k l : Fin 3) :
    resMat 3 (Matrix.single k l f4Omega) =
      Matrix.single (blk k 0) (blk l 1) (1 : F2) +
      Matrix.single (blk k 1) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [resMat_single, f4Eps_omega]
  have h00 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 0 = 0 := by simp
  have h01 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 1 = 1 := by simp
  have h10 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 0 = 1 := by simp
  have h11 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by simp
  rw [h00, h01, h10, h11, Matrix.single_zero]
  abel

private lemma one_add_mul_one_add {A B : Matrix (Fin 6) (Fin 6) F2} (h : A * B = 0) :
    ((1 : Matrix (Fin 6) (Fin 6) F2) + A) * (1 + B) = 1 + (A + B) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h, add_zero]
  abel

private lemma one_add_single_mul_three {a b c d e f : Fin 6}
    (hbc : b ≠ c) (hbe : b ≠ e) (hde : d ≠ e) :
    ((1 + Matrix.single a b (1 : F2)) * (1 + Matrix.single c d (1 : F2))) *
        (1 + Matrix.single e f (1 : F2)) =
      1 + (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2) +
        Matrix.single e f (1 : F2)) := by
  have hAC : Matrix.single a b (1 : F2) * Matrix.single c d (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b c hbc (1 : F2)
  have hAE : Matrix.single a b (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b e hbe (1 : F2)
  have hCE : Matrix.single c d (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) c d e hde (1 : F2)
  have hACE : (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2)) *
      Matrix.single e f (1 : F2) = 0 := by
    rw [Matrix.add_mul, hAE, hCE, add_zero]
  rw [one_add_mul_one_add hAC, one_add_mul_one_add hACE]

private theorem resSL_transvection_one (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl (1 : F4)) =
      Matrix.SpecialLinearGroup.transvection (blk_ne_of_ne hkl 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, resMat_single_one]
  have hAB : Matrix.single (blk k 0) (blk l 0) (1 : F2) *
      Matrix.single (blk k 1) (blk l 1) (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) (blk k 0) (blk l 0) (blk k 1)
      (blk_ne_of_ne' hkl.symm 0 1) (1 : F2)
  rw [one_add_mul_one_add hAB]

private theorem resSL_transvection_omega (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl f4Omega) =
      Matrix.SpecialLinearGroup.transvection (blk_ne_of_ne' hkl 0 1) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (blk_ne_of_ne' hkl 1 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      map_add, map_one, resMat_single_omega]
  exact (one_add_single_mul_three (a := blk k 0) (b := blk l 1) (c := blk k 1)
    (d := blk l 0) (e := blk k 1) (f := blk l 1)
    (blk_ne_of_ne hkl.symm 1) (blk_ne_of_ne hkl.symm 1)
    (blk_ne_of_ne' hkl.symm 0 1)).symm

private lemma slToAdjointE6_transvection_one (a b : Fin 6) (hab : a ≠ b) :
    E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.transvection hab (1 : F2)) =
      xr (a5Root a b) := by
  apply Subtype.ext
  rw [E6Pilot.coe_slToAdjointE6_transvection]
  rfl

private lemma f4Omega_sq_add_one : f4Omega ^ 2 = f4Omega + 1 := by
  have h : f4Omega ^ 2 + (f4Omega + 1) = 0 := by
    rw [← add_assoc]; exact f4Omega_sq
  have h2 : f4Omega ^ 2 = -(f4Omega + 1) := add_eq_zero_iff_eq_neg.mp h
  rw [h2, neg_add, CharTwo.neg_eq, CharTwo.neg_eq]

private lemma Phi_transvection_one (k l : Fin 3) (hkl : k ≠ l) :
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
        (Matrix.SpecialLinearGroup.transvection hkl (1 : F4)) = rOne k l := by
  rw [MonoidHom.comp_apply, resSL_transvection_one k l hkl, map_mul,
      slToAdjointE6_transvection_one (blk k 0) (blk l 0) (blk_ne_of_ne hkl 0),
      slToAdjointE6_transvection_one (blk k 1) (blk l 1) (blk_ne_of_ne hkl 1)]
  rfl

private lemma Phi_transvection_omega (k l : Fin 3) (hkl : k ≠ l) :
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
        (Matrix.SpecialLinearGroup.transvection hkl f4Omega) = rOmega k l := by
  rw [MonoidHom.comp_apply, resSL_transvection_omega k l hkl, map_mul, map_mul,
      slToAdjointE6_transvection_one (blk k 0) (blk l 1) (blk_ne_of_ne' hkl 0 1),
      slToAdjointE6_transvection_one (blk k 1) (blk l 0) (blk_ne_of_ne' hkl 1 0),
      slToAdjointE6_transvection_one (blk k 1) (blk l 1) (blk_ne_of_ne hkl 1)]
  rfl

theorem iota_injective : Function.Injective (E6Pilot.slToAdjointE6 F2) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [E6Pilot.ker_slToAdjointE6]
  have hcard : Nat.card F2 = 2 := by simpa using GaloisField.card 2 1 (by norm_num)
  exact CFSG.Quasithin.S146zX.center_specialLinearGroup_eq_bot_of_card_two
    (K := F2) (n := 6) hcard (by norm_num)

theorem jE_eq : jE = sl3four.map (E6Pilot.slToAdjointE6 F2) := by
  rw [sl3four, MonoidHom.map_range]
  apply le_antisymm
  · rw [jE]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨k, l, hkl, hg | hg⟩
    · rw [hg, ← Phi_transvection_one k l hkl]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · rw [hg, ← Phi_transvection_omega k l hkl]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · let T : Set (Matrix.SpecialLinearGroup (Fin 3) F4) :=
      {g | ∃ (i j : Fin 3) (hij : i ≠ j) (c : F4),
        g = Matrix.SpecialLinearGroup.transvection hij c}
    have hT : Subgroup.closure T = ⊤ :=
      CFSG.ClassicalGroups.SpecialLinear.closure_transvection_eq_top
    have hrange : ((E6Pilot.slToAdjointE6 F2).comp (resSL 3)).range =
        Subgroup.closure (((E6Pilot.slToAdjointE6 F2).comp (resSL 3)) '' T) := by
      rw [MonoidHom.range_eq_map, ← hT, MonoidHom.map_closure]
    rw [hrange]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨x, hx, rfl⟩
    rcases hx with ⟨i, j, hij, c, rfl⟩
    rcases f4_cases c with rfl | rfl | rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero hij, map_one]
      exact jE.one_mem
    · rw [Phi_transvection_one i j hij]
      exact Subgroup.subset_closure ⟨i, j, hij, Or.inl rfl⟩
    · rw [Phi_transvection_omega i j hij]
      exact Subgroup.subset_closure ⟨i, j, hij, Or.inr rfl⟩
    · rw [f4Omega_sq_add_one, Matrix.SpecialLinearGroup.transvection_add, map_mul,
        Phi_transvection_omega i j hij, Phi_transvection_one i j hij]
      exact jE.mul_mem (Subgroup.subset_closure ⟨i, j, hij, Or.inr rfl⟩)
        (Subgroup.subset_closure ⟨i, j, hij, Or.inl rfl⟩)

theorem jE_le_lE : jE ≤ lE := by
  rw [jE_eq]
  change sl3four.map (E6Pilot.slToAdjointE6 F2) ≤ E6Pilot.a5Levi F2
  exact (Subgroup.map_le_range (E6Pilot.slToAdjointE6 F2) sl3four).trans
    (le_of_eq (E6Pilot.range_slToAdjointE6 (K := F2)))

end JFacts

end CFSG.StandardType.GGSixE6Two
