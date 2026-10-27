module

public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KF4.LongA2Data
public import CFSG.RankThree.PartOne.KF4.ShortA2Data
public import CFSG.RankThree.PartOne.KE.F4Regular

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE (rootKernel mem_rootKernel not_dvd_card_weylGroup_F4)
open scoped Matrix

@[expose] def f4W3 : WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).wordProd [f4Index 0, f4Index 1, f4Index 2, f4Index 3] ^ 4

@[expose] def f4W3Mat : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 1, -1, 0; 1, 1, -1, -1; 2, 2, -2, -1; 0, 2, -1, -1]

theorem f4W3Mat_sq : f4W3Mat * f4W3Mat + f4W3Mat + 1 = 0 := by decide +kernel

theorem f4W3_eq_wordProd : f4W3 = (coxeterSystem Tag.F4).wordProd
    ([f4Index 0, f4Index 1, f4Index 2, f4Index 3] ++ [f4Index 0, f4Index 1, f4Index 2, f4Index 3] ++
      [f4Index 0, f4Index 1, f4Index 2, f4Index 3] ++
        [f4Index 0, f4Index 1, f4Index 2, f4Index 3]) := by
  simp only [f4W3, pow_succ, pow_zero, one_mul, CoxeterSystem.wordProd_append]

section Matrices


theorem weylMatrix_wordProd_of' {τ : Tag} {ω : List (Fin τ.rank)}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (h : ∀ j : Fin τ.rank, ω.foldr (reflect τ) (Pi.single j 1) = fun i => M i j) :
    weylMatrix ((coxeterSystem τ).wordProd ω) = M := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul]
  exact congrFun (h j) i

theorem weylMatrix_f4W3 : weylMatrix f4W3 = f4W3Mat := by
  rw [f4W3_eq_wordProd]
  exact weylMatrix_wordProd_of' (by decide +kernel)

theorem f4W3_smul (x : Fin Tag.F4.rank → ℤ) : f4W3 • x = f4W3Mat *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_f4W3]

theorem f4W3_cube : f4W3 ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_f4W3, weylMatrix_one]
  have h : f4W3Mat ^ 3 - 1 = (f4W3Mat - 1) * (f4W3Mat * f4W3Mat + f4W3Mat + 1) := by
    noncomm_ring
  rw [f4W3Mat_sq, mul_zero] at h
  exact sub_eq_zero.1 h

theorem f4W3_lattice (x : Fin Tag.F4.rank → ℤ) : f4W3 • f4W3 • x + f4W3 • x + x = 0 := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_f4W3,
    Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.one_mulVec x, Matrix.mulVec_mulVec,
    Matrix.mul_one, ← Matrix.add_mulVec, f4W3Mat_sq, Matrix.zero_mulVec]

theorem f4W3_lattice_fixed {x : Fin Tag.F4.rank → ℤ} (h : f4W3 • x = x) : x = 0 := by
  have h3 := f4W3_lattice x
  rw [h, h] at h3
  funext i
  have := congrFun h3 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  rw [Pi.zero_apply]
  omega

theorem weyl_smul_add (g : WeylGroup Tag.F4) (x y : Fin Tag.F4.rank → ℤ) :
    g • (x + y) = g • x + g • y := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_add]

theorem weyl_smul_zsmul (g : WeylGroup Tag.F4) (c : ℤ) (x : Fin Tag.F4.rank → ℤ) :
    g • (c • x) = c • (g • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_smul]

theorem weyl_smul_zero (g : WeylGroup Tag.F4) : g • (0 : Fin Tag.F4.rank → ℤ) = 0 := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_zero]

theorem weylMatrix_sq_add_of_smul {T : WeylGroup Tag.F4}
    (hT : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x + T • x + x = 0) :
    weylMatrix T * weylMatrix T + weylMatrix T + 1 = 0 := by
  ext i j
  have h := congrFun (hT (Pi.single j 1)) i
  rw [Matrix.add_apply, Matrix.add_apply, ← weylMatrix_mul, weylMatrix_apply, weylMatrix_apply,
    mul_smul, Matrix.one_apply, Matrix.zero_apply]
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_apply] at h
  exact h

end Matrices

theorem f4RootVec_injective : Function.Injective f4RootVec := by
  intro m m' h
  revert m m'
  decide +kernel

theorem ncard_parabolicRoots_F4 {J : Set (Fin Tag.F4.rank)}
    {P : Fin Tag.F4.rank → Prop} [DecidablePred P] (hJ : ∀ i, i ∈ J ↔ P i) {n : ℕ}
    (h : (Finset.univ.filter fun m : Fin 48 => ∀ i, ¬P i → f4RootVec m i = 0).card = n) :
    (parabolicRoots Tag.F4 J).ncard = n := by
  have e : parabolicRoots Tag.F4 J =
      f4RootVec '' ↑(Finset.univ.filter fun m : Fin 48 => ∀ i, ¬P i → f4RootVec m i = 0) := by
    ext α
    simp only [parabolicRoots, Set.mem_ofPred_eq, hJ, Set.mem_image, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hα, hs⟩
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα
      exact ⟨m, hs, rfl⟩
    · rintro ⟨m, hs, rfl⟩
      exact ⟨isRoot_f4RootVec m, hs⟩
  rw [e, Set.ncard_image_of_injective _ f4RootVec_injective, Set.ncard_coe_finset, h]

theorem f4T3_supports_complete : ∀ S : Finset (Fin Tag.F4.rank), S ≠ Finset.univ →
    S.card % 2 = 0 →
    (Finset.univ.filter fun m : Fin 48 => ∀ i, i ∉ S → f4RootVec m i = 0).card % 3 = 0 →
    S = ∅ ∨ S = {f4Index 0, f4Index 1} ∨ S = {f4Index 2, f4Index 3} := by
  decide +kernel

theorem f4Long_rotation : ∀ m m' : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 0 ∨ i = f4Index 1) → f4RootVec m i = 0) →
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 0 ∨ i = f4Index 1) → f4RootVec m' i = 0) →
    (f4RootVec m (f4Index 0) • f4RootVec m + f4RootVec m (f4Index 1) • f4RootVec m' +
      f4RootVec m + Pi.single (f4Index 0) 1 = 0) →
    (f4RootVec m' (f4Index 0) • f4RootVec m + f4RootVec m' (f4Index 1) • f4RootVec m' +
      f4RootVec m' + Pi.single (f4Index 1) 1 = 0) →
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      chainRoot f4chainLong i j (f4Index 0) • f4RootVec m +
        chainRoot f4chainLong i j (f4Index 1) • f4RootVec m' =
      chainRoot f4chainLong (π i) (π j) := by
  decide +kernel

theorem f4Short_rotation : ∀ m m' : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 3) → f4RootVec m i = 0) →
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 3) → f4RootVec m' i = 0) →
    (f4RootVec m (f4Index 2) • f4RootVec m + f4RootVec m (f4Index 3) • f4RootVec m' +
      f4RootVec m + Pi.single (f4Index 2) 1 = 0) →
    (f4RootVec m' (f4Index 2) • f4RootVec m + f4RootVec m' (f4Index 3) • f4RootVec m' +
      f4RootVec m' + Pi.single (f4Index 3) 1 = 0) →
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      f4ShortSigma i j (f4Index 2) • f4RootVec m + f4ShortSigma i j (f4Index 3) • f4RootVec m' =
      f4ShortSigma (π i) (π j) := by
  decide +kernel

section Rotation


theorem eq_smul_single_add_of_support {p q : Fin Tag.F4.rank} (hpq : p ≠ q)
    {x : Fin Tag.F4.rank → ℤ} (hx : ∀ i, ¬(i = p ∨ i = q) → x i = 0) :
    x = x p • (Pi.single p 1 : Fin Tag.F4.rank → ℤ) +
      x q • (Pi.single q 1 : Fin Tag.F4.rank → ℤ) := by
  funext i
  by_cases hip : i = p
  · subst hip
    simp [hpq]
  · by_cases hiq : i = q
    · subst hiq
      simp [hip]
    · rw [hx i (by tauto)]
      simp [hip, hiq]

theorem exists_rotation_of_stable {T : WeylGroup Tag.F4} {p q : Fin Tag.F4.rank} (hpq : p ≠ q)
    {J : Set (Fin Tag.F4.rank)} (hJ : ∀ i, i ∈ J ↔ i = p ∨ i = q)
    (hTmaps : ∀ β ∈ parabolicRoots Tag.F4 J, T • β ∈ parabolicRoots Tag.F4 J)
    (hTlat : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x + T • x + x = 0)
    {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hσ : ∀ i j, ∀ l, ¬(l = p ∨ l = q) → σ i j l = 0)
    (hfin : ∀ m m' : Fin 48,
      (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m i = 0) →
      (∀ i : Fin Tag.F4.rank, ¬(i = p ∨ i = q) → f4RootVec m' i = 0) →
      (f4RootVec m p • f4RootVec m + f4RootVec m q • f4RootVec m' +
        f4RootVec m + Pi.single p 1 = 0) →
      (f4RootVec m' p • f4RootVec m + f4RootVec m' q • f4RootVec m' +
        f4RootVec m' + Pi.single q 1 = 0) →
      ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
        σ i j p • f4RootVec m + σ i j q • f4RootVec m' = σ (π i) (π j)) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, T • σ i j = σ (π i) (π j) := by
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
  have hrel1 : f4RootVec m p • f4RootVec m + f4RootVec m q • f4RootVec m' + f4RootVec m +
      Pi.single p 1 = 0 := by
    have h := hTlat (Pi.single p 1)
    rw [← hm, hT _ hmsupp] at h
    exact h
  have hrel2 : f4RootVec m' p • f4RootVec m + f4RootVec m' q • f4RootVec m' + f4RootVec m' +
      Pi.single q 1 = 0 := by
    have h := hTlat (Pi.single q 1)
    rw [← hm', hT _ hm'supp] at h
    exact h
  obtain ⟨π, hπ⟩ := hfin m m' hmsupp hm'supp hrel1 hrel2
  refine ⟨π, fun i j => ?_⟩
  rw [hT _ (hσ i j)]
  exact hπ i j

end Rotation

theorem f4chainLong_support : ∀ i j : Fin 3, ∀ l : Fin Tag.F4.rank,
    ¬(l = f4Index 0 ∨ l = f4Index 1) → chainRoot f4chainLong i j l = 0 := by
  decide +kernel

theorem f4ShortSigma_support : ∀ i j : Fin 3, ∀ l : Fin Tag.F4.rank,
    ¬(l = f4Index 2 ∨ l = f4Index 3) → f4ShortSigma i j l = 0 := by
  decide +kernel

section Kernel


theorem f4_parabolic_card (S : Finset (Fin Tag.F4.rank)) :
    (parabolicRoots Tag.F4 ↑S).ncard =
      (Finset.univ.filter fun m : Fin 48 => ∀ i, i ∉ S → f4RootVec m i = 0).card :=
  ncard_parabolicRoots_F4 (P := fun i => i ∈ S) (fun _ => Finset.mem_coe) rfl

theorem single_mem_parabolicRoots_F4 {J : Set (Fin Tag.F4.rank)} {c : Fin Tag.F4.rank}
    (hc : c ∈ J) : (Pi.single c 1 : Fin Tag.F4.rank → ℤ) ∈ parabolicRoots Tag.F4 J := by
  refine ⟨isRoot_single Tag.F4 c, fun i hi => ?_⟩
  have hik : i ≠ c := fun h => hi (h ▸ hc)
  simp [hik]

theorem f4Three_kernel_structure {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (r : ZMod p)
    (z : Fin Tag.F4.rank → ZMod p) (hz : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) f4W3).mulVec z = r • z) :
    rootKernel z = ∅ ∨ ∃ a : WeylGroup Tag.F4,
      ((a • ·) '' rootKernel z = parabolicRoots Tag.F4 f4LongSupport ∧
        ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
          (a * f4W3 * a⁻¹) • chainRoot f4chainLong i j = chainRoot f4chainLong (π i) (π j)) ∨
      ((a • ·) '' rootKernel z = parabolicRoots Tag.F4 f4ShortSupport ∧
        ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
          (a * f4W3 * a⁻¹) • f4ShortSigma i j = f4ShortSigma (π i) (π j)) := by
  classical
  obtain ⟨u₀, J₀, hΦ₀, hJ₀⟩ := exists_smul_rootKernel_eq_parabolicRoots
    (not_dvd_card_weylGroup_F4 Fact.out hp3) z
  have hJ₀' := hJ₀ hz
  have hmaps : ∀ α ∈ rootKernel z, f4W3 • α ∈ rootKernel z := fun α hα =>
    ⟨IsRoot.smul hα.1 f4W3, by
      rw [← charVal_dualMatrix, hzr, charVal_smul_col, hα.2, mul_zero]⟩
  set T := u₀ * f4W3 * u₀⁻¹ with hTdef
  have hTmaps : ∀ β ∈ parabolicRoots Tag.F4 J₀, T • β ∈ parabolicRoots Tag.F4 J₀ := by
    intro β hβ
    rw [← hΦ₀] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨f4W3 • α, hmaps α hα, by rw [hTdef, mul_smul, mul_smul, inv_smul_smul]⟩
  have hTlat : ∀ x : Fin Tag.F4.rank → ℤ, T • T • x + T • x + x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y, x = u₀ • y := ⟨u₀⁻¹ • x, (smul_inv_smul u₀ x).symm⟩
    simp only [hTdef, mul_smul, inv_smul_smul]
    rw [← weyl_smul_add, ← weyl_smul_add, f4W3_lattice, weyl_smul_zero]
  have heven : J₀.toFinset.card % 2 = 0 := by
    have h := even_card_of_sq_add_self_add_one (weylMatrix_sq_add_of_smul hTlat) J₀.toFinset
      fun a ha c hc => by
        rw [Set.mem_toFinset] at ha hc
        rw [weylMatrix_apply]
        exact (hTmaps _ (single_mem_parabolicRoots_F4 hc)).2 a ha
    exact Nat.even_iff.1 h
  have hfin : (rootKernel z).Finite := (finite_setOf_isRoot Tag.F4).subset fun α hα => hα.1
  have h3 : 3 ∣ (rootKernel z).ncard :=
    three_dvd_ncard_of_free hfin f4W3_cube hmaps fun α hα h =>
      (IsRoot.ne_zero hα.1) (f4W3_lattice_fixed h)
  have hcardΦ : (parabolicRoots Tag.F4 J₀).ncard = (rootKernel z).ncard := by
    rw [← hΦ₀]
    exact Set.ncard_image_of_injective _ (MulAction.injective u₀)
  have hJ' : (J₀.toFinset : Set (Fin Tag.F4.rank)) = J₀ := Set.coe_toFinset J₀
  have hS := f4T3_supports_complete J₀.toFinset (fun h => hJ₀' (by
      rw [← hJ', h, Finset.coe_univ])) heven (by
    rw [← f4_parabolic_card, hJ', hcardΦ]
    exact Nat.mod_eq_zero_of_dvd h3)
  rcases hS with h | h | h
  ·
    left
    have hJe : J₀ = ∅ := by rw [← hJ', h, Finset.coe_empty]
    have hroots : parabolicRoots Tag.F4 J₀ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun α hα => ?_
      refine IsRoot.ne_zero hα.1 ?_
      funext i
      exact hα.2 i (by rw [hJe]; exact Set.notMem_empty i)
    rw [hroots] at hΦ₀
    exact Set.image_eq_empty.1 hΦ₀
  ·
    right
    refine ⟨u₀, Or.inl ⟨?_, ?_⟩⟩
    · have : J₀ = f4LongSupport := by
        rw [← hJ', h]
        ext i
        simp [f4LongSupport]
      rw [← this]
      exact hΦ₀
    · have hJ : ∀ i, i ∈ J₀ ↔ i = f4Index 0 ∨ i = f4Index 1 := fun i => by
        rw [← hJ', h]
        simp
      exact exists_rotation_of_stable (by decide) hJ hTmaps hTlat
        (σ := fun i j => chainRoot f4chainLong i j) f4chainLong_support
        (fun m m' => f4Long_rotation m m')
  ·
    right
    refine ⟨u₀, Or.inr ⟨?_, ?_⟩⟩
    · have : J₀ = f4ShortSupport := by
        rw [← hJ', h]
        ext i
        simp [f4ShortSupport]
      rw [← this]
      exact hΦ₀
    · have hJ : ∀ i, i ∈ J₀ ↔ i = f4Index 2 ∨ i = f4Index 3 := fun i => by
        rw [← hJ', h]
        simp
      exact exists_rotation_of_stable (by decide) hJ hTmaps hTlat
        (σ := f4ShortSigma) f4ShortSigma_support (fun m m' => f4Short_rotation m m')

end Kernel

end CFSG.RankThree.PartOne.KF4
