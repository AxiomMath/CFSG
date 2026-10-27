module

public import CFSG.RankThree.PartOne.KF4.Lattice4
public import CFSG.RankThree.PartOne.KF4.B2Data

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.RankThree.PartOne.KE (rootKernel mem_rootKernel not_dvd_card_weylGroup_F4)
open scoped Matrix

@[expose] def f4B2Beta : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 0]

@[expose] def f4B2Gamma : Fin Tag.F4.rank → ℤ := ![0, 1, 1, 0]

theorem even_card_of_sq_eq_neg_one {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M * M = -1) (J : Finset (Fin n)) (hJ : ∀ a ∉ J, ∀ c ∈ J, M a c = 0) :
    Even J.card := by
  classical
  let N : Matrix J J ℤ := fun a c => M a c
  have hN : N * N = -1 := by
    ext a c
    have h := congrFun (congrFun hM a) c
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.one_apply] at h ⊢
    have hsum : ∑ b : Fin n, M a b * M b c = ∑ b : J, N a b * N b c := by
      rw [← Finset.sum_subset (Finset.subset_univ J) fun b _ hb => by
        rw [hJ b hb c c.2, mul_zero]]
      exact (Finset.sum_coe_sort J fun b => M a b * M b c).symm
    rw [hsum] at h
    have e : ((a : Fin n) = c) ↔ a = c := Subtype.ext_iff.symm
    simpa only [e] using h
  have hdet := congrArg Matrix.det hN
  rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_coe] at hdet
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [Odd.neg_pow hodd, one_pow] at hdet
  have h1 : 0 ≤ N.det * N.det := mul_self_nonneg _
  linarith

set_option synthInstance.maxSize 4096 in
theorem f4Four_rotation_support : ∀ p q : Fin Tag.F4.rank, p ≠ q → ∀ m m' : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m i = 0) →
    (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m' i = 0) →
    (f4RootVec m p • f4RootVec m + f4RootVec m q • f4RootVec m' + Pi.single p 1 = 0) →
    (f4RootVec m' p • f4RootVec m + f4RootVec m' q • f4RootVec m' + Pi.single q 1 = 0) →
    (iform (f4RootVec m) (f4RootVec m) = iform (Pi.single p 1) (Pi.single p 1)) →
    (iform (f4RootVec m') (f4RootVec m') = iform (Pi.single q 1) (Pi.single q 1)) →
    (iform (f4RootVec m) (f4RootVec m') = iform (Pi.single p 1) (Pi.single q 1)) →
    (p = f4Index 1 ∧ q = f4Index 2) ∨ (p = f4Index 2 ∧ q = f4Index 1) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem f4Four_rotation_12 : ∀ m m' : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 1 ∨ i = f4Index 2) → f4RootVec m i = 0) →
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 1 ∨ i = f4Index 2) → f4RootVec m' i = 0) →
    (f4RootVec m (f4Index 1) • f4RootVec m + f4RootVec m (f4Index 2) • f4RootVec m' +
      Pi.single (f4Index 1) 1 = 0) →
    (f4RootVec m' (f4Index 1) • f4RootVec m + f4RootVec m' (f4Index 2) • f4RootVec m' +
      Pi.single (f4Index 2) 1 = 0) →
    (iform (f4RootVec m) (f4RootVec m) =
      iform (Pi.single (f4Index 1) 1) (Pi.single (f4Index 1) 1)) →
    (iform (f4RootVec m') (f4RootVec m') =
      iform (Pi.single (f4Index 2) 1) (Pi.single (f4Index 2) 1)) →
    (iform (f4RootVec m) (f4RootVec m') =
      iform (Pi.single (f4Index 1) 1) (Pi.single (f4Index 2) 1)) →
    ((f4RootVec m = f4B2Beta ∧ f4RootVec m' = -f4B2Gamma) ∨
      (f4RootVec m = -f4B2Beta ∧ f4RootVec m' = f4B2Gamma)) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem f4Four_rotation_21 : ∀ m m' : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 1) → f4RootVec m i = 0) →
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 1) → f4RootVec m' i = 0) →
    (f4RootVec m (f4Index 2) • f4RootVec m + f4RootVec m (f4Index 1) • f4RootVec m' +
      Pi.single (f4Index 2) 1 = 0) →
    (f4RootVec m' (f4Index 2) • f4RootVec m + f4RootVec m' (f4Index 1) • f4RootVec m' +
      Pi.single (f4Index 1) 1 = 0) →
    (iform (f4RootVec m) (f4RootVec m) =
      iform (Pi.single (f4Index 2) 1) (Pi.single (f4Index 2) 1)) →
    (iform (f4RootVec m') (f4RootVec m') =
      iform (Pi.single (f4Index 1) 1) (Pi.single (f4Index 1) 1)) →
    (iform (f4RootVec m) (f4RootVec m') =
      iform (Pi.single (f4Index 2) 1) (Pi.single (f4Index 1) 1)) →
    ((f4RootVec m' = f4B2Beta ∧ f4RootVec m = -f4B2Gamma) ∨
      (f4RootVec m' = -f4B2Beta ∧ f4RootVec m = f4B2Gamma)) := by
  decide +kernel


theorem weylMatrix_sq_neg_of_smul {T : WeylGroup Tag.F4}
    (hT : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x = -x) :
    weylMatrix T * weylMatrix T = -1 := by
  ext i j
  have h := congrFun (hT (Pi.single j 1)) i
  rw [← weylMatrix_mul, weylMatrix_apply, mul_smul, Matrix.neg_apply, Matrix.one_apply]
  simp only [Pi.neg_apply, Pi.single_apply] at h
  rw [h]

theorem weyl_smul_neg (g : WeylGroup Tag.F4) (x : Fin Tag.F4.rank → ℤ) : g • (-x) = -(g • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_neg]


theorem rotation_data_of_stable_sq {T : WeylGroup Tag.F4} {p q : Fin Tag.F4.rank} (hpq : p ≠ q)
    {J : Set (Fin Tag.F4.rank)} (hJ : ∀ i, i ∈ J ↔ i = p ∨ i = q)
    (hTmaps : ∀ β ∈ parabolicRoots Tag.F4 J, T • β ∈ parabolicRoots Tag.F4 J)
    (hTlat : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x = -x) :
    ∃ m m' : Fin 48, f4RootVec m = T • (Pi.single p 1 : Fin Tag.F4.rank → ℤ) ∧
      f4RootVec m' = T • (Pi.single q 1 : Fin Tag.F4.rank → ℤ) ∧
      (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m i = 0) ∧
      (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m' i = 0) ∧
      (f4RootVec m p • f4RootVec m + f4RootVec m q • f4RootVec m' + Pi.single p 1 = 0) ∧
      (f4RootVec m' p • f4RootVec m + f4RootVec m' q • f4RootVec m' + Pi.single q 1 = 0) ∧
      (iform (f4RootVec m) (f4RootVec m) = iform (Pi.single p 1) (Pi.single p 1)) ∧
      (iform (f4RootVec m') (f4RootVec m') = iform (Pi.single q 1) (Pi.single q 1)) ∧
      (iform (f4RootVec m) (f4RootVec m') = iform (Pi.single p 1) (Pi.single q 1)) := by
  have hsingle : ∀ k, k = p ∨ k = q → (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈
      parabolicRoots Tag.F4 J := fun k hk => by
    refine ⟨isRoot_single Tag.F4 k, fun i hi => ?_⟩
    have hik : i ≠ k := fun h => hi ((hJ i).2 (h ▸ hk))
    simp [hik]
  obtain ⟨hu, hu'⟩ := hTmaps _ (hsingle p (Or.inl rfl))
  obtain ⟨hv, hv'⟩ := hTmaps _ (hsingle q (Or.inr rfl))
  obtain ⟨m, hm⟩ := isRoot_iff_exists_f4RootVec.1 hu
  obtain ⟨m', hm'⟩ := isRoot_iff_exists_f4RootVec.1 hv
  have hsupp : ∀ (m₀ : Fin 48), f4RootVec m₀ = T • (Pi.single p 1 : Fin Tag.F4.rank → ℤ) ∨
      f4RootVec m₀ = T • (Pi.single q 1 : Fin Tag.F4.rank → ℤ) →
      ∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m₀ i = 0 := by
    intro m₀ h i hi
    rcases h with h | h
    · rw [h]
      exact hu' i (fun hiJ => hi ((hJ i).1 hiJ))
    · rw [h]
      exact hv' i (fun hiJ => hi ((hJ i).1 hiJ))
  have hmsupp := hsupp m (Or.inl hm)
  have hm'supp := hsupp m' (Or.inr hm')
  have hT : ∀ x : Fin Tag.F4.rank → ℤ, (∀ i, ¬(i = p ∨ i = q) → x i = 0) →
      T • x = x p • f4RootVec m + x q • f4RootVec m' := fun x hx => by
    conv_lhs => rw [eq_smul_single_add_of_support hpq hx]
    rw [weyl_smul_add, weyl_smul_zsmul, weyl_smul_zsmul, ← hm, ← hm']
  refine ⟨m, m', hm, hm', hmsupp, hm'supp, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hTlat (Pi.single p 1)
    rw [← hm, hT _ hmsupp] at h
    exact eq_neg_iff_add_eq_zero.1 h
  · have h := hTlat (Pi.single q 1)
    rw [← hm', hT _ hm'supp] at h
    exact eq_neg_iff_add_eq_zero.1 h
  · rw [hm, iform_smul]
  · rw [hm', iform_smul]
  · rw [hm, hm', iform_smul]

theorem f4Four_kernel_structure {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (r : ZMod p)
    (z : Fin Tag.F4.rank → ZMod p) (hz : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) f4W4).mulVec z = r • z) :
    rootKernel z = ∅ ∨ ∃ a : WeylGroup Tag.F4,
      (a • ·) '' rootKernel z = parabolicRoots Tag.F4 f4B2Support ∧
      (((a * f4W4 * a⁻¹) • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
          (a * f4W4 * a⁻¹) • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma) ∨
        ((a * f4W4 * a⁻¹) • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
          (a * f4W4 * a⁻¹) • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma)) := by
  classical
  obtain ⟨u₀, J₀, hΦ₀, hJ₀⟩ := exists_smul_rootKernel_eq_parabolicRoots
    (not_dvd_card_weylGroup_F4 Fact.out hp3) z
  have hJ₀' := hJ₀ hz
  have hmaps : ∀ α ∈ rootKernel z, f4W4 • α ∈ rootKernel z := fun α hα =>
    ⟨IsRoot.smul hα.1 f4W4, by
      rw [← charVal_dualMatrix, hzr, charVal_smul_col, hα.2, mul_zero]⟩
  set T := u₀ * f4W4 * u₀⁻¹ with hTdef
  have hTmaps : ∀ β ∈ parabolicRoots Tag.F4 J₀, T • β ∈ parabolicRoots Tag.F4 J₀ := by
    intro β hβ
    rw [← hΦ₀] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨f4W4 • α, hmaps α hα, by rw [hTdef, mul_smul, mul_smul, inv_smul_smul]⟩
  have hTlat : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x = -x := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y, x = u₀ • y := ⟨u₀⁻¹ • x, (smul_inv_smul u₀ x).symm⟩
    simp only [hTdef, mul_smul, inv_smul_smul]
    rw [f4W4_smul_smul, weyl_smul_neg]
  have heven : J₀.toFinset.card % 2 = 0 := by
    have h := even_card_of_sq_eq_neg_one (weylMatrix_sq_neg_of_smul hTlat) J₀.toFinset
      fun a ha c hc => by
        rw [Set.mem_toFinset] at ha hc
        rw [weylMatrix_apply]
        exact (hTmaps _ (single_mem_parabolicRoots_F4 hc)).2 a ha
    exact Nat.even_iff.1 h
  have hJ' : (J₀.toFinset : Set (Fin Tag.F4.rank)) = J₀ := Set.coe_toFinset J₀
  have hne : J₀.toFinset ≠ Finset.univ := fun h => hJ₀' (by rw [← hJ', h, Finset.coe_univ])
  have hlt : J₀.toFinset.card < 4 := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hne)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hcard : J₀.toFinset.card = 0 ∨ J₀.toFinset.card = 2 := by omega
  rcases hcard with h0 | h2
  ·
    left
    have hJe : J₀ = ∅ := by
      rw [← hJ', Finset.card_eq_zero.1 h0, Finset.coe_empty]
    have hroots : parabolicRoots Tag.F4 J₀ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun α hα => ?_
      refine IsRoot.ne_zero hα.1 ?_
      funext i
      exact hα.2 i (by rw [hJe]; exact Set.notMem_empty i)
    rw [hroots] at hΦ₀
    exact Set.image_eq_empty.1 hΦ₀
  · right
    obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.1 h2
    have hJ : ∀ i, i ∈ J₀ ↔ i = x ∨ i = y := fun i => by
      rw [← hJ', hS]
      simp
    obtain ⟨m, m', hm, hm', hms, hm's, hr1, hr2, hn1, hn2, hn3⟩ :=
      rotation_data_of_stable_sq hxy hJ hTmaps hTlat
    rcases f4Four_rotation_support x y hxy m m' hms hm's hr1 hr2 hn1 hn2 hn3 with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst hx
      subst hy
      have hJe : J₀ = f4B2Support := by
        ext i
        rw [hJ i]
        simp [f4B2Support]
      refine ⟨u₀, by rw [← hJe]; exact hΦ₀, ?_⟩
      rw [← hm, ← hm']
      exact f4Four_rotation_12 m m' hms hm's hr1 hr2 hn1 hn2 hn3
    · subst hx
      subst hy
      have hJe : J₀ = f4B2Support := by
        ext i
        rw [hJ i]
        simp [f4B2Support, or_comm]
      refine ⟨u₀, by rw [← hJe]; exact hΦ₀, ?_⟩
      rw [← hm, ← hm']
      exact f4Four_rotation_21 m m' hms hm's hr1 hr2 hn1 hn2 hn3


end CFSG.RankThree.PartOne.KF4
