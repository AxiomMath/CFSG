module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2ProofWeyl

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.SEITZQ1
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

section Mono

variable {L : Type} [Field L]

@[expose] def mono (S1 S2 : Lˣ) (m1 m2 : Fin ReeTag.F4.tag.rank → ℤ) :
    Fin ReeTag.F4.tag.rank → Lˣ :=
  fun i => S1 ^ m1 i * S2 ^ m2 i

theorem rootChar_mono (S1 S2 : Lˣ) (m1 m2 v : Fin ReeTag.F4.tag.rank → ℤ) :
    FourGroupChevalley.rootChar (mono S1 S2 m1 m2) v = S1 ^ dotR m1 v * S2 ^ dotR m2 v := by
  simp only [FourGroupChevalley.rootChar, mono, mul_zpow, ← _root_.zpow_mul,
    Finset.prod_mul_distrib, Finset.prod_zpow_eq_zpow_sum, sum_rank]
  rfl

theorem rootChar_smul_eq_of_single
    {a b : Fin ReeTag.F4.tag.rank → Lˣ} {w : WeylGroup ReeTag.F4.tag}
    (h : ∀ i, FourGroupChevalley.rootChar a (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      b i)
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    FourGroupChevalley.rootChar a (w • v) = FourGroupChevalley.rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hs : FourGroupChevalley.rootChar b (Pi.single i 1) = b i := by
    have := FourGroupChevalley.rootChar_nsmul_single b i 1
    rwa [one_smul, pow_one] at this
  rw [rootChar_zsmul, rootChar_zsmul, h i, hs]

theorem conj_mono
    (w : WeylGroup ReeTag.F4.tag) (S1 S2 : Lˣ) {m1 m2 n1 n2 : Fin ReeTag.F4.tag.rank → ℤ}
    (h1 : ∀ k, dotR n1 (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) = m1 k)
    (h2 : ∀ k, dotR n2 (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) = m2 k) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w * rootDiagUnit ReeTag.F4.tag (mono S1 S2 m1 m2) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
      rootDiagUnit ReeTag.F4.tag (mono S1 S2 n1 n2) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).2 fun v => ?_).symm
  refine rootChar_smul_eq_of_single (fun k => ?_) v
  rw [rootChar_mono, h1, h2]
  rfl

theorem pow_zpow_eq (a : ℕ) (x : Lˣ) (m c : ℤ) (N : ℕ) (hN : (N : ℤ) = 2 ^ a * c) :
    (x ^ m) ^ N = (x ^ 2 ^ a) ^ (c * m) := by
  rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast x (2 ^ a), ← _root_.zpow_mul, hN]
  congr 1
  push_cast
  ring

theorem reeTuple_mono (a : ℕ) (t1 t2 : Lˣ) (m1 m2 : Fin ReeTag.F4.tag.rank → ℤ) :
    reeTuple a (mono t1 t2 m1 m2) = mono (t1 ^ 2 ^ a) (t2 ^ 2 ^ a)
      (v4 (2 * m1 3) (2 * m1 2) (m1 1) (m1 0)) (v4 (2 * m2 3) (2 * m2 2) (m2 1) (m2 0)) := by
  have hl : ReeTag.F4.relationExponent a 0 = 2 ^ a ∧ ReeTag.F4.relationExponent a 1 = 2 ^ a ∧
      ReeTag.F4.relationExponent a 2 = 2 ^ (a + 1) ∧
      ReeTag.F4.relationExponent a 3 = 2 ^ (a + 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ReeTag.relationExponent, ite_eq_left (by decide)]
      rfl
    · rw [ReeTag.relationExponent, ite_eq_left (by decide)]
      rfl
    · rw [ReeTag.relationExponent, ite_eq_right (by decide)]
      rfl
    · rw [ReeTag.relationExponent, ite_eq_right (by decide)]
      rfl
  have h2 : ((2 ^ (a + 1) : ℕ) : ℤ) = 2 ^ a * 2 := by push_cast; ring
  have h1 : ((2 ^ a : ℕ) : ℤ) = 2 ^ a * 1 := by push_cast; ring
  funext k
  simp only [reeTuple, mono]
  fin_cases k
  · show (t1 ^ m1 3 * t2 ^ m2 3) ^ ReeTag.F4.relationExponent a 3 = _
    rw [hl.2.2.2, mul_pow, pow_zpow_eq a t1 _ 2 _ h2, pow_zpow_eq a t2 _ 2 _ h2]
    rfl
  · show (t1 ^ m1 2 * t2 ^ m2 2) ^ ReeTag.F4.relationExponent a 2 = _
    rw [hl.2.2.1, mul_pow, pow_zpow_eq a t1 _ 2 _ h2, pow_zpow_eq a t2 _ 2 _ h2]
    rfl
  · show (t1 ^ m1 1 * t2 ^ m2 1) ^ ReeTag.F4.relationExponent a 1 = _
    rw [hl.2.1, mul_pow, pow_zpow_eq a t1 _ 1 _ h1, pow_zpow_eq a t2 _ 1 _ h1, one_mul, one_mul]
    rfl
  · show (t1 ^ m1 0 * t2 ^ m2 0) ^ ReeTag.F4.relationExponent a 0 = _
    rw [hl.1, mul_pow, pow_zpow_eq a t1 _ 1 _ h1, pow_zpow_eq a t2 _ 1 _ h1, one_mul, one_mul]
    rfl

end Mono

section Weyl

theorem q1U_smul_single (k : Fin ReeTag.F4.tag.rank) :
    q1U • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      ![v4 0 1 2 0, v4 1 1 2 2, v4 (-1) (-1) (-2) (-1), v4 1 1 1 0] k := by
  have hW : CFSG.RankThree.Lattice.wordMat ReeTag.F4.tag [0, 2, 1, 3, 2] =
      CFSG.RankThree.Lattice.toMat ReeTag.F4.tag.rank
        [[0, 1, -1, 1], [1, 1, -1, 1], [2, 2, -2, 1], [0, 2, -1, 0]] :=
    CFSG.RankThree.Lattice.wordMat_eq_toMat .F4 _ (by decide +kernel)
  funext l
  rw [q1U, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, hW,
    Matrix.mulVec_single_one]
  fin_cases k <;> fin_cases l <;> rfl

theorem q1W_zero_smul_single (k : Fin ReeTag.F4.tag.rank) :
    q1W 0 • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      ![v4 (-1) 0 0 0, v4 2 3 4 2, v4 (-1) (-2) (-3) (-2), v4 0 0 0 1] k := by
  have hW : CFSG.RankThree.Lattice.wordMat Tag.F4 (q1WWord 0) =
      CFSG.RankThree.Lattice.toMat Tag.F4.rank
        [[-1, 2, -1, 0], [0, 3, -2, 0], [0, 4, -3, 0], [0, 2, -2, 1]] :=
    CFSG.RankThree.Lattice.wordMat_eq_toMat .F4 _ (by decide +kernel)
  funext l
  rw [q1W_smul, hW]
  fin_cases k <;> fin_cases l <;> decide

theorem q1W_three_smul_single (k : Fin ReeTag.F4.tag.rank) :
    q1W 3 • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      ![v4 1 0 0 0, v4 (-2) (-3) (-4) (-2), v4 1 2 3 2, v4 0 0 0 (-1)] k := by
  have hW : CFSG.RankThree.Lattice.wordMat Tag.F4 (q1WWord 3) =
      CFSG.RankThree.Lattice.toMat Tag.F4.rank
        [[1, -2, 1, 0], [0, -3, 2, 0], [0, -4, 3, 0], [0, -2, 2, -1]] :=
    CFSG.RankThree.Lattice.wordMat_eq_toMat .F4 _ (by decide +kernel)
  funext l
  rw [q1W_smul, hW]
  fin_cases k <;> fin_cases l <;> decide

end Weyl

section Frames

variable {L : Type} [Field L]

@[expose] def diag2 (t1 t2 : Lˣ) : SL(3, L) :=
  ⟨Matrix.diagonal ![(t1 : L), (t2 : L), (((t1 * t2)⁻¹ : Lˣ) : L)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show (t1 : L) * t2 * (((t1 * t2)⁻¹ : Lˣ) : L) = 1
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

theorem coe_diag2 (t1 t2 : Lˣ) : ((diag2 t1 t2 : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
    Matrix.diagonal ![(t1 : L), (t2 : L), (((t1 * t2)⁻¹ : Lˣ) : L)] :=
  rfl

theorem f4rhoLong_diag2 (t1 t2 : Lˣ) :
    f4rhoLong L (diag2 t1 t2) = torus2Elt (f4Index 0) (f4Index 1) t1 (t1 * t2) := by
  have hrep : f4LongRep L ⟨torus2Elt (f4Index 0) (f4Index 1) t1 (t1 * t2),
      torus2Elt_mem_f4Long _ _⟩ = diag2 t1 t2 := by
    apply Subtype.ext
    rw [coe_f4LongRep, f4Long_Mat_torus, coe_diag2]
    congr 1
    funext k
    fin_cases k
    · rfl
    · show ((t1⁻¹ * (t1 * t2) : Lˣ) : L) = t2
      rw [inv_mul_cancel_left]
    · rfl
  rw [← hrep]
  exact f4rhoLong_f4LongRep (torus2Elt_mem_f4Long _ _)

theorem f4rhoLong_diag2_eq (t1 t2 : Lˣ) :
    f4rhoLong L (diag2 t1 t2) =
      rootDiagUnit Tag.F4 (mono t1 t2 (v4 1 1 (-1) 0) (v4 (-1) 2 (-1) 0)) := by
  have e1 : ∀ j : Fin Tag.F4.rank,
      Tag.F4.cartan (f4Index 0) j + Tag.F4.cartan (f4Index 1) j = v4 1 1 (-1) 0 j := by
    intro j
    fin_cases j <;> rfl
  have e2 : ∀ j : Fin Tag.F4.rank, Tag.F4.cartan (f4Index 1) j = v4 (-1) 2 (-1) 0 j := by
    intro j
    fin_cases j <;> rfl
  rw [f4rhoLong_diag2, torus2Elt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, mono, mul_zpow]
  rw [← mul_assoc, ← _root_.zpow_add, e1, e2]

theorem q1Rho_diag2 (t1 t2 : Lˣ) :
    q1Rho L (diag2 t1 t2) =
      rootDiagUnit ReeTag.F4.tag (mono t1 t2 (v4 0 (-1) 1 0) (v4 1 (-1) 0 1)) := by
  have h1 : f4rhoLongR L (diag2 t1 t2) =
      rootDiagUnit ReeTag.F4.tag (mono t1 t2 (v4 1 1 (-1) 0) (v4 (-1) 2 (-1) 0)) :=
    f4rhoLong_diag2_eq t1 t2
  show canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U * f4rhoLongR L (diag2 t1 t2) *
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U)⁻¹ = _
  rw [h1]
  refine conj_mono q1U t1 t2 (fun k => ?_) (fun k => ?_) <;> rw [q1U_smul_single] <;>
    fin_cases k <;> decide

variable [CharP L 2] [IsAlgClosed L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem q1PsiRho_diag2_even (hF : IsReeFrob a F) (ha : a % 2 = 0) (t1 t2 : Lˣ) :
    q1PsiRho F a (diag2 t1 t2) = rootDiagUnit ReeTag.F4.tag
      (mono (t1 ^ 2 ^ a) (t2 ^ 2 ^ a) (v4 0 2 (-1) 0) (v4 (-2) 2 (-1) 1)) := by
  have hs : q1Par a = 0 := by simp [q1Par, ha]
  rw [q1PsiRho_apply, twistMap, q1Rho_diag2, hF.fext_rootDiagUnit, reeTuple_mono, q1N, hs]
  refine conj_mono (q1W 0) _ _ (fun k => ?_) (fun k => ?_) <;> rw [q1W_zero_smul_single] <;>
    fin_cases k <;> decide

theorem q1PsiRho_diag2_odd (hF : IsReeFrob a F) (ha : a % 2 = 1) (t1 t2 : Lˣ) :
    q1PsiRho F a (diag2 t1 t2) = rootDiagUnit ReeTag.F4.tag
      (mono (t1 ^ 2 ^ a) (t2 ^ 2 ^ a) (v4 0 (-2) 1 0) (v4 2 (-2) 1 (-1))) := by
  have hs : q1Par a = 3 := by simp [q1Par, ha]
  rw [q1PsiRho_apply, twistMap, q1Rho_diag2, hF.fext_rootDiagUnit, reeTuple_mono, q1N, hs]
  refine conj_mono (q1W 3) _ _ (fun k => ?_) (fun k => ?_) <;> rw [q1W_three_smul_single] <;>
    fin_cases k <;> decide

end Frames

section Scalars

variable {L : Type} [Field L]

theorem zpow_eq_self_of_emod {r : Lˣ} (hr : r ^ 3 = 1) {n : ℤ} (hn : n % 3 = 1) : r ^ n = r := by
  have h : n = 3 * (n / 3) + 1 := by omega
  rw [h, _root_.zpow_add, _root_.zpow_mul, zpow_ofNat, hr, _root_.one_zpow, one_mul, zpow_one]

theorem two_pow_emod_three_of_even {a : ℕ} (ha : a % 2 = 0) : (2 : ℤ) ^ a % 3 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  rw [pow_mul]
  have h : (2 ^ 2 : ℤ) ^ k ≡ 1 ^ k [ZMOD 3] := Int.ModEq.pow k (by decide)
  rw [one_pow] at h
  exact h

theorem two_pow_emod_three_of_odd {a : ℕ} (ha : a % 2 = 1) : (2 : ℤ) ^ a % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  rw [pow_succ, pow_mul]
  have h : (2 ^ 2 : ℤ) ^ k * 2 ≡ 1 ^ k * 2 [ZMOD 3] := (Int.ModEq.pow k (by decide)).mul_right 2
  rw [one_pow, one_mul] at h
  exact h

theorem pow_two_pow_zpow_eq_self {r : Lˣ} (hr : r ^ 3 = 1) (a : ℕ) {m : ℤ}
    (hm : (2 : ℤ) ^ a * m % 3 = 1) : (r ^ 2 ^ a) ^ m = r := by
  rw [← zpow_natCast, ← _root_.zpow_mul]
  refine zpow_eq_self_of_emod hr ?_
  push_cast
  exact hm

theorem eq_diag2_of_mem_center {g : SL(3, L)} (hg : g ∈ Subgroup.center SL(3, L)) :
    ∃ r : Lˣ, r ^ 3 = 1 ∧ g = diag2 r r := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr3
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr3
  refine ⟨Units.mk0 r hr0, Units.ext (by simp [hr3]), Subtype.ext ?_⟩
  rw [← hr, coe_diag2, Matrix.scalar_apply]
  congr 1
  funext k
  fin_cases k
  · rfl
  · rfl
  · show r = (((Units.mk0 r hr0 * Units.mk0 r hr0)⁻¹ : Lˣ) : L)
    rw [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hr3]
    ring

end Scalars

section FrameScalars

variable {L : Type} [Field L]

theorem q1Rho_scalar {r : Lˣ} (hr : r ^ 3 = 1) :
    q1Rho L (diag2 r r) = rootDiagUnit ReeTag.F4.tag (fun _ => r) := by
  rw [q1Rho_diag2]
  congr 1
  funext i
  simp only [mono, ← _root_.zpow_add]
  refine zpow_eq_self_of_emod hr ?_
  fin_cases i <;> decide

variable [CharP L 2] [IsAlgClosed L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem q1PsiRho_scalar (hF : IsReeFrob a F) {r : Lˣ} (hr : r ^ 3 = 1) :
    q1PsiRho F a (diag2 r r) = rootDiagUnit ReeTag.F4.tag (fun _ => r) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · have h2 := two_pow_emod_three_of_even ha
    rw [q1PsiRho_diag2_even hF ha]
    congr 1
    funext i
    simp only [mono, ← _root_.zpow_add]
    refine pow_two_pow_zpow_eq_self hr a ?_
    fin_cases i <;> (rw [Int.mul_emod, h2]; decide)
  · have h2 := two_pow_emod_three_of_odd ha
    rw [q1PsiRho_diag2_odd hF ha]
    congr 1
    funext i
    simp only [mono, ← _root_.zpow_add]
    refine pow_two_pow_zpow_eq_self hr a ?_
    fin_cases i <;> (rw [Int.mul_emod, h2]; decide)

theorem q1Rho_eq_q1PsiRho_of_mem_center (hF : IsReeFrob a F) {z : SL(3, L)}
    (hz : z ∈ Subgroup.center SL(3, L)) : q1Rho L z = q1PsiRho F a z := by
  obtain ⟨r, hr, rfl⟩ := eq_diag2_of_mem_center hz
  rw [q1Rho_scalar hr, q1PsiRho_scalar hF hr]

theorem forall_fin_rank {P : Fin ReeTag.F4.tag.rank → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) : ∀ i, P i := by
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem exists_diag2_of_rootDiagUnit (hF : IsReeFrob a F) (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ t1 t2 s1 s2 : Lˣ, rootDiagUnit ReeTag.F4.tag b =
      q1Rho L (diag2 t1 t2) * q1PsiRho F a (diag2 s1 s2) := by
  have hroot : ∀ S : Lˣ, ∃ s : Lˣ, s ^ 2 ^ a = S := by
    intro S
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (S : L) (pow_pos (by norm_num : 0 < 2) a)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (by norm_num))] at hx
      exact S.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx])⟩
  have hcube : ∀ S : Lˣ, ∃ c : Lˣ, c ^ 3 = S := by
    intro S
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (S : L) (by norm_num : 0 < 3)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hx
      exact S.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx])⟩
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · obtain ⟨c, hc⟩ := hcube (b 3 * (b 0)⁻¹)
    obtain ⟨s1, hs1⟩ := hroot (b 1 * b 2 * b 3 * c⁻¹ * c⁻¹)
    obtain ⟨s2, hs2⟩ := hroot c
    refine ⟨b 2 * (b 1 * b 2 * b 3 * c⁻¹ * c⁻¹) * c, b 3 * c⁻¹, s1, s2, ?_⟩
    rw [q1Rho_diag2, q1PsiRho_diag2_even hF ha, hs1, hs2, ← rootDiagUnit_mul]
    congr 1
    have hb0 : b 0 = b 3 * (c ^ 3)⁻¹ := by
      rw [hc, _root_.mul_inv_rev, inv_inv, mul_comm (b 0), mul_inv_cancel_left]
    funext i
    revert i
    refine forall_fin_rank ?_ ?_ ?_ ?_
    all_goals
      try rw [hb0]
      apply Units.ext
      simp only [Pi.mul_apply, mono, v4_apply_zero, v4_apply_one, v4_apply_two, v4_apply_three,
        Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, _root_.zpow_neg,
        zpow_ofNat]
      field_simp
  · obtain ⟨c, hc⟩ := hcube (b 0 * (b 3)⁻¹)
    obtain ⟨s1, hs1⟩ := hroot (b 1 * b 2 * b 3 * c * c)⁻¹
    obtain ⟨s2, hs2⟩ := hroot c
    refine ⟨b 2 * (b 1 * b 2 * b 3 * c * c) * c⁻¹, b 3 * c, s1, s2, ?_⟩
    rw [q1Rho_diag2, q1PsiRho_diag2_odd hF ha, hs1, hs2, ← rootDiagUnit_mul]
    congr 1
    have hb0 : b 0 = b 3 * c ^ 3 := by
      rw [hc, mul_comm (b 0), mul_inv_cancel_left]
    funext i
    revert i
    refine forall_fin_rank ?_ ?_ ?_ ?_
    all_goals
      try rw [hb0]
      apply Units.ext
      simp only [Pi.mul_apply, mono, v4_apply_zero, v4_apply_one, v4_apply_two, v4_apply_three,
        Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, _root_.zpow_neg,
        zpow_ofNat]
      field_simp

end FrameScalars

end CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof
