module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofWeyl
public import CFSG.RankThree.PartOne.SEITZQ1.Twist

public section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Monster.B.Geometry
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof (codeRoots codeRoots_eq)

open CFSG.RankThree.PartOne.SEITZQ1 (q1Sig q1Tau q1Sig_values q1Tau_zero_values
  q1Tau_three_values isRoot_q1Sig isRoot_q1Tau)

open CFSG.LieType.Steinberg.Adjoint (iform)


@[expose] def ht4 (v : Fin ReeTag.F4.tag.rank → ℤ) : ℤ := v 0 + v 1 + v 2 + v 3

@[expose] def v4 (a b c d : ℤ) : Fin ReeTag.F4.tag.rank → ℤ := ![a, b, c, d]

@[simp] theorem v4_apply_zero (a b c d : ℤ) : v4 a b c d 0 = a := rfl

@[simp] theorem v4_apply_one (a b c d : ℤ) : v4 a b c d 1 = b := rfl

@[simp] theorem v4_apply_two (a b c d : ℤ) : v4 a b c d 2 = c := rfl

@[simp] theorem v4_apply_three (a b c d : ℤ) : v4 a b c d 3 = d := rfl

@[expose] def dotR (u v : Fin ReeTag.F4.tag.rank → ℤ) : ℤ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

@[expose] def gen4 : Fin 4 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![v4 0 1 2 0, v4 1 1 2 2, v4 1 1 1 0, v4 0 1 1 1]

@[expose] def cov4 : Fin 4 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![v4 (-1) 0 1 (-1), v4 1 (-1) 0 1, v4 2 0 0 (-1), v4 (-2) 2 (-1) 1]

@[expose] def refl4 (i : Fin 4) (v : Fin ReeTag.F4.tag.rank → ℤ) : Fin ReeTag.F4.tag.rank → ℤ :=
  fun l => v l - dotR (cov4 i) v * gen4 i l

@[expose] def stabWords : List (List (Fin 4)) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0]].flatMap fun g =>
    [[], [2], [3], [2, 3], [3, 2], [2, 3, 2]].map fun h => g ++ h

@[expose] def condStab (c : ℕ) : Bool :=
  (List.finRange 4).all fun j => ht4 (codeRoots c j) % 3 == 1

@[expose] def stabCheck : Bool :=
  (List.range 1152).all fun k => !(condStab (f4Code k)) ||
    stabWords.any fun l => (List.finRange 4).all fun j =>
      List.ofFn (codeRoots (f4Code k) j) == List.ofFn (l.foldr refl4 (Pi.single j 1))

@[expose] def kerList : List (Fin ReeTag.F4.tag.rank → ℤ) :=
  [v4 0 1 2 0, v4 1 1 2 2, v4 1 2 4 2, v4 0 (-1) (-2) 0, v4 (-1) (-1) (-2) (-2),
    v4 (-1) (-2) (-4) (-2), v4 1 1 1 0, v4 0 1 1 1, v4 1 2 2 1, v4 (-1) (-1) (-1) 0,
    v4 0 (-1) (-1) (-1), v4 (-1) (-2) (-2) (-1)]

@[expose] def kerCheck : Bool :=
  (List.range 48).all fun k => !(ht4 (Tag.F4.rootCertificate.root k) % 3 == 0) ||
    kerList.any fun v => List.ofFn v == List.ofFn (Tag.F4.rootCertificate.root k)

set_option maxRecDepth 100000 in
theorem stabCheck_eq : stabCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem kerCheck_eq : kerCheck = true := by decide +kernel

theorem sum_rank (f : Fin ReeTag.F4.tag.rank → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

theorem iform_F4 (x y : Fin ReeTag.F4.tag.rank → ℤ) :
    iform (τ := ReeTag.F4.tag) x y =
      x 0 * (4 * y 0 - 2 * y 1) + x 1 * (-2 * y 0 + 4 * y 1 - 2 * y 2) +
        x 2 * (-2 * y 1 + 2 * y 2 - y 3) + x 3 * (-y 2 + 2 * y 3) := by
  have e00 : ReeTag.F4.tag.symmetrizedCartan 0 0 = 4 := rfl
  have e01 : ReeTag.F4.tag.symmetrizedCartan 0 1 = -2 := rfl
  have e02 : ReeTag.F4.tag.symmetrizedCartan 0 2 = 0 := rfl
  have e03 : ReeTag.F4.tag.symmetrizedCartan 0 3 = 0 := rfl
  have e10 : ReeTag.F4.tag.symmetrizedCartan 1 0 = -2 := rfl
  have e11 : ReeTag.F4.tag.symmetrizedCartan 1 1 = 4 := rfl
  have e12 : ReeTag.F4.tag.symmetrizedCartan 1 2 = -2 := rfl
  have e13 : ReeTag.F4.tag.symmetrizedCartan 1 3 = 0 := rfl
  have e20 : ReeTag.F4.tag.symmetrizedCartan 2 0 = 0 := rfl
  have e21 : ReeTag.F4.tag.symmetrizedCartan 2 1 = -2 := rfl
  have e22 : ReeTag.F4.tag.symmetrizedCartan 2 2 = 2 := rfl
  have e23 : ReeTag.F4.tag.symmetrizedCartan 2 3 = -1 := rfl
  have e30 : ReeTag.F4.tag.symmetrizedCartan 3 0 = 0 := rfl
  have e31 : ReeTag.F4.tag.symmetrizedCartan 3 1 = 0 := rfl
  have e32 : ReeTag.F4.tag.symmetrizedCartan 3 2 = -1 := rfl
  have e33 : ReeTag.F4.tag.symmetrizedCartan 3 3 = 2 := rfl
  simp only [iform, sum_rank, e00, e01, e02, e03, e10, e11, e12, e13,
    e20, e21, e22, e23, e30, e31, e32, e33]
  ring


theorem isRoot_gen4 (i : Fin 4) : IsRoot ReeTag.F4.tag (gen4 i) := by
  obtain ⟨s01, s12, -, -, -, -⟩ := q1Sig_values
  obtain ⟨t01, t12, -, -, -, -⟩ := q1Tau_zero_values
  fin_cases i
  · have h := isRoot_q1Sig (i := 0) (j := 1) (by decide)
    rw [s01] at h
    exact h
  · have h := isRoot_q1Sig (i := 1) (j := 2) (by decide)
    rw [s12] at h
    exact h
  · have h := isRoot_q1Tau (s := 0) (i := 0) (j := 1) (by decide)
    rw [t01] at h
    exact h
  · have h := isRoot_q1Tau (s := 0) (i := 1) (j := 2) (by decide)
    rw [t12] at h
    exact h

theorem corootPair_gen4 (i : Fin 4) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    corootPair (τ := ReeTag.F4.tag) (gen4 i) v = dotR (cov4 i) v := by
  simp only [corootPair, iform_F4]
  fin_cases i <;> simp [gen4, cov4, dotR] <;> omega


theorem rootReflection_gen4_smul (i : Fin 4) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootReflection (τ := ReeTag.F4.tag) (gen4 i) • v = refl4 i v := by
  rw [rootReflection_smul (isRoot_gen4 i), corootPair_gen4]
  funext l
  simp [refl4]

theorem prod_rootReflection_gen4_smul (l : List (Fin 4)) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (l.map fun i => rootReflection (τ := ReeTag.F4.tag) (gen4 i)).prod • v =
      l.foldr refl4 v := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul, List.foldr_nil]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, rootReflection_gen4_smul]
    rfl

theorem rootChar_const {L : Type} [Field L] (x : Lˣ) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    FourGroupChevalley.rootChar (τ := ReeTag.F4.tag) (fun _ => x) v = x ^ ht4 v := by
  simp only [FourGroupChevalley.rootChar, Finset.prod_zpow_eq_zpow_sum, sum_rank]
  rfl

theorem gen4_mem_rootCharKernel {L : Type} [Field L] {x : Lˣ} (hx : orderOf x = 3) (i : Fin 4) :
    gen4 i ∈ rootCharKernel (fun _ : Fin ReeTag.F4.tag.rank => x) := by
  refine ⟨isRoot_gen4 i, ?_⟩
  rw [rootChar_const]
  have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h6 : x ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, h3, one_pow]
  fin_cases i
  · show x ^ (3 : ℤ) = 1
    rw [zpow_ofNat]; exact h3
  · show x ^ (6 : ℤ) = 1
    rw [zpow_ofNat]; exact h6
  · show x ^ (3 : ℤ) = 1
    rw [zpow_ofNat]; exact h3
  · show x ^ (3 : ℤ) = 1
    rw [zpow_ofNat]; exact h3

theorem rootCharStabilizer_const_subset {L : Type} [Field L] {x : Lˣ} (hx : orderOf x = 3) :
    rootCharStabilizer (fun _ : Fin ReeTag.F4.tag.rank => x) ⊆
      (Subgroup.closure {s | ∃ α ∈ rootCharKernel (fun _ : Fin ReeTag.F4.tag.rank => x),
        s = rootReflection α} : Set (WeylGroup ReeTag.F4.tag)) := by
  intro w hw
  obtain ⟨k, hk, hr, -⟩ := exists_entry w
  have hcond : condStab (f4Code k) = true := by
    simp only [condStab, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
    intro j
    rw [codeRoots_eq hr j]
    have h1 := hw (Pi.single j 1)
    rw [rootChar_const, rootChar_const] at h1
    have hht : ht4 (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) = 1 := by
      fin_cases j <;> rfl
    rw [hht, zpow_one] at h1
    have h2 : x ^ (ht4 (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) - 1) = 1 := by
      rw [zpow_sub_one, h1, mul_inv_cancel]
    have h3 := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hx] at h3
    push_cast at h3
    omega
  have hcheck := stabCheck_eq
  simp only [stabCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck k hk
  rw [hcond] at h1
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.all_eq_true,
    List.mem_finRange, true_implies, beq_iff_eq] at h1
  obtain ⟨l, -, hl⟩ := h1
  have hw' : w = (l.map fun i => rootReflection (τ := ReeTag.F4.tag) (gen4 i)).prod := by
    refine ext_single fun j => ?_
    rw [prod_rootReflection_gen4_smul, ← codeRoots_eq hr j]
    exact List.ofFn_injective (hl j)
  rw [hw']
  refine list_prod_mem fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.subset_closure ⟨gen4 i, gen4_mem_rootCharKernel hx i, rfl⟩

theorem mem_kerList_of_isRoot {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α)
    (h3 : ht4 α % 3 = 0) : α ∈ kerList := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.F4) hα
  have hcheck := kerCheck_eq
  simp only [kerCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck k (by rwa [f4_roots_length] at hk)
  rw [h3] at h1
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    beq_iff_eq] at h1
  obtain ⟨v, hv, hv'⟩ := h1
  rwa [← List.ofFn_injective hv']

theorem rootCharKernel_const_subset {L : Type} [Field L] {x : Lˣ} (hx : orderOf x = 3)
    {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) :
    rootCharKernel (fun _ : Fin ReeTag.F4.tag.rank => x) ⊆
      {α | ∃ i j : Fin 3, i ≠ j ∧ (α = q1Sig i j ∨ α = q1Tau s i j)} := by
  rintro α ⟨hα, h1⟩
  rw [rootChar_const] at h1
  have h3 : ht4 α % 3 = 0 := by
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hx] at h2
    push_cast at h2
    omega
  have hm := mem_kerList_of_isRoot hα h3
  obtain ⟨s01, s12, s02, s10, s21, s20⟩ := q1Sig_values
  have hm' : α = v4 0 1 2 0 ∨ α = v4 1 1 2 2 ∨ α = v4 1 2 4 2 ∨ α = v4 0 (-1) (-2) 0 ∨
      α = v4 (-1) (-1) (-2) (-2) ∨ α = v4 (-1) (-2) (-4) (-2) ∨ α = v4 1 1 1 0 ∨
      α = v4 0 1 1 1 ∨ α = v4 1 2 2 1 ∨ α = v4 (-1) (-1) (-1) 0 ∨ α = v4 0 (-1) (-1) (-1) ∨
      α = v4 (-1) (-2) (-2) (-1) := by
    simpa only [kerList, List.mem_cons, List.not_mem_nil, or_false] using hm
  rcases hs with rfl | rfl
  · obtain ⟨t01, t12, t02, t10, t21, t20⟩ := q1Tau_zero_values
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, Or.inl s01.symm⟩
    · exact ⟨1, 2, by decide, Or.inl s12.symm⟩
    · exact ⟨0, 2, by decide, Or.inl s02.symm⟩
    · exact ⟨1, 0, by decide, Or.inl s10.symm⟩
    · exact ⟨2, 1, by decide, Or.inl s21.symm⟩
    · exact ⟨2, 0, by decide, Or.inl s20.symm⟩
    · exact ⟨0, 1, by decide, Or.inr t01.symm⟩
    · exact ⟨1, 2, by decide, Or.inr t12.symm⟩
    · exact ⟨0, 2, by decide, Or.inr t02.symm⟩
    · exact ⟨1, 0, by decide, Or.inr t10.symm⟩
    · exact ⟨2, 1, by decide, Or.inr t21.symm⟩
    · exact ⟨2, 0, by decide, Or.inr t20.symm⟩
  · obtain ⟨t01, t12, t02, t10, t21, t20⟩ := q1Tau_three_values
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, Or.inl s01.symm⟩
    · exact ⟨1, 2, by decide, Or.inl s12.symm⟩
    · exact ⟨0, 2, by decide, Or.inl s02.symm⟩
    · exact ⟨1, 0, by decide, Or.inl s10.symm⟩
    · exact ⟨2, 1, by decide, Or.inl s21.symm⟩
    · exact ⟨2, 0, by decide, Or.inl s20.symm⟩
    · exact ⟨1, 0, by decide, Or.inr t10.symm⟩
    · exact ⟨2, 1, by decide, Or.inr t21.symm⟩
    · exact ⟨2, 0, by decide, Or.inr t20.symm⟩
    · exact ⟨0, 1, by decide, Or.inr t01.symm⟩
    · exact ⟨1, 2, by decide, Or.inr t12.symm⟩
    · exact ⟨0, 2, by decide, Or.inr t02.symm⟩

end CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof
