module

public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Monster.B.Geometry
open CFSG.RankThree.PartOne.KLR CFSG.RankThree.Lattice

@[expose] def lin4 (x : Fin 4 → ℤ) (r : Fin 4 → Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun l => x 0 * r 0 l + x 1 * r 1 l + x 2 * r 2 l + x 3 * r 3 l

@[expose] def dot4 (u v : Fin 4 → ℤ) : ℤ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

@[expose] def w0Col : Fin 4 → Fin 4 → ℤ :=
  ![![-1, -3, -4, -2], ![-1, 0, 0, 0], ![1, 1, 1, 1], ![0, 0, 1, 0]]

@[expose] def uBar (s : ℤ) : Fin 2 → Fin 4 → ℤ :=
  ![![0, -1, 0, 1 - s], ![-1, -1, -s, 2]]

@[expose] def codeRoots (c : ℕ) : Fin ReeTag.F4.tag.rank → Fin 4 → ℤ :=
  fun j => Tag.F4.rootCertificate.root (f4Digit c j)

@[expose] def condA (s : ℤ) (c : ℕ) : Bool :=
  (List.finRange 4).all fun j => (List.finRange 2).all fun t =>
    (dot4 (uBar s t) (codeRoots c j) - uBar s t j) % 3 == 0

@[expose] def condB (c : ℕ) : Bool :=
  (List.finRange 4).all fun j =>
    List.ofFn (lin4 (w0Col j) (codeRoots c)) ==
      List.ofFn (lin4 (ReeTag.F4.dualRoot (codeRoots c (ReeTag.F4.perm j))) w0Col)

@[expose] def weylCheck (s : ℤ) : Bool :=
  (List.range 1152).all fun k =>
    !(condA s (f4Code k) && condB (f4Code k)) || f4Code k == 794688

@[expose] def rootCheck (s : ℤ) : Bool :=
  (List.range 48).all fun k =>
    !(dot4 (uBar s 0) (Tag.F4.rootCertificate.root k) % 3 == 0 &&
      dot4 (uBar s 1) (Tag.F4.rootCertificate.root k) % 3 == 0)

set_option maxRecDepth 100000 in
theorem weylCheck_one : weylCheck 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem weylCheck_two : weylCheck 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rootCheck_one : rootCheck 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rootCheck_two : rootCheck 2 = true := by decide +kernel

theorem smul_eq_lin4 (w : WeylGroup ReeTag.F4.tag) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    w • v = lin4 v (fun k => w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw]
  show ∑ i : Fin 4, v i • (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) = _
  rw [Fin.sum_univ_four]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lin4]

section Twisted


theorem wPhi2_smul_single (k : Fin ReeTag.F4.tag.rank) :
    wPhi2 • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) = w0Col k := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  funext l
  rw [wPhi2, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, hW,
    Matrix.mulVec_single_one]
  fin_cases k <;> fin_cases l <;> rfl

theorem wPhi2_smul (v : Fin ReeTag.F4.tag.rank → ℤ) : wPhi2 • v = lin4 v w0Col := by
  rw [smul_eq_lin4]
  congr 1
  funext k
  exact wPhi2_smul_single k

theorem codeRoots_eq {w : WeylGroup ReeTag.F4.tag} {c : ℕ} (h : F4Realizes w c)
    (j : Fin ReeTag.F4.tag.rank) :
    codeRoots c j = w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
  (h j).2.symm

theorem condA_of {s : ℤ} {w : WeylGroup ReeTag.F4.tag} {c : ℕ} (h : F4Realizes w c)
    (hA : ∀ (j : Fin ReeTag.F4.tag.rank) (t : Fin 2),
      (3 : ℤ) ∣ dot4 (uBar s t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) - uBar s t j) :
    condA s c = true := by
  simp only [condA, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  intro j t
  rw [codeRoots_eq h j]
  exact Int.emod_eq_zero_of_dvd (hA j t)

theorem condB_of {w : WeylGroup ReeTag.F4.tag} {c : ℕ} (h : F4Realizes w c)
    (hB : w * wPhi2 = wPhi2 * ReeTag.F4.weylPerm w) : condB c = true := by
  simp only [condB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  intro j
  congr 1
  have hc : codeRoots c = fun k => w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    funext fun k => codeRoots_eq h k
  have h1 : lin4 (w0Col j) (codeRoots c) =
      (w * wPhi2) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rw [mul_smul, wPhi2_smul_single j, smul_eq_lin4 w (w0Col j), hc]
    rfl
  have h2 : lin4 (ReeTag.F4.dualRoot (codeRoots c (ReeTag.F4.perm j))) w0Col =
      (wPhi2 * ReeTag.F4.weylPerm w) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rw [mul_smul, codeRoots_eq h (ReeTag.F4.perm j),
      ReeTag.dualRoot_smul w (isRoot_single _ (ReeTag.F4.perm j)),
      ReeTag.dualRoot_single ReeTag.F4 (ReeTag.F4.perm j), ReeTag.perm_perm (t := ReeTag.F4) j,
      wPhi2_smul]
  rw [h1, h2, hB]

theorem eq_one_of_weylCheck {s : ℤ} (hs : s = 1 ∨ s = 2) {w : WeylGroup ReeTag.F4.tag}
    (hA : ∀ (j : Fin ReeTag.F4.tag.rank) (t : Fin 2),
      (3 : ℤ) ∣ dot4 (uBar s t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) - uBar s t j)
    (hB : w * wPhi2 = wPhi2 * ReeTag.F4.weylPerm w) : w = 1 := by
  obtain ⟨k, hk, hr, -⟩ := exists_entry w
  have hcheck : weylCheck s = true := by
    rcases hs with rfl | rfl
    · exact weylCheck_one
    · exact weylCheck_two
  simp only [weylCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck k hk
  rw [condA_of hr hA, condB_of hr hB] at h1
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  rw [h1] at hr
  exact hr.eq f4Realizes_one

theorem not_three_dvd_of_isRoot {s : ℤ} (hs : s = 1 ∨ s = 2) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) :
    ¬ ((3 : ℤ) ∣ dot4 (uBar s 0) α ∧ (3 : ℤ) ∣ dot4 (uBar s 1) α) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.F4) hα
  have hcheck : rootCheck s = true := by
    rcases hs with rfl | rfl
    · exact rootCheck_one
    · exact rootCheck_two
  have hlen : Tag.F4.rootCertificate.roots.length = 48 := f4_roots_length
  simp only [rootCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck k (hlen ▸ hk)
  rintro ⟨h2, h3⟩
  rw [Int.emod_eq_zero_of_dvd h2, Int.emod_eq_zero_of_dvd h3] at h1
  simp at h1

end Twisted

end CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof
