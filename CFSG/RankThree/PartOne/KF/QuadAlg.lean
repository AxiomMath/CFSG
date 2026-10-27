module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.RankThree.PartOne.KFQ

section Idem

variable {ι : Type*} [DecidableEq ι] {L : Type*} [Field L]

theorem single_mul_single_self (i : ι) (a b : L) :
    (Pi.single i a : ι → L) * Pi.single i b = Pi.single i (a * b) := by
  ext k; by_cases hk : k = i
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

theorem single_mul_single_ne {i i' : ι} (h : i ≠ i') (a b : L) :
    (Pi.single i a : ι → L) * Pi.single i' b = 0 := by
  ext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne hk]

theorem eq_zero_or_one_of_mul_self {a : L} (h : a * a = a) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    exact mul_left_cancel₀ ha (show a * a = a * 1 by rw [mul_one]; exact h)

end Idem

section Aut

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_perm_idem (φ : (ι → L) ≃ₐ[K] (ι → L)) :
    ∃ π : Equiv.Perm ι, ∀ i, φ (Pi.single i 1) = Pi.single (π i) 1 := by
  have hid : ∀ i j, φ (Pi.single i 1) j = 0 ∨ φ (Pi.single i 1) j = 1 := by
    intro i j
    have h2 : φ (Pi.single i 1) * φ (Pi.single i 1) = φ (Pi.single i 1) := by
      rw [← map_mul, single_mul_single_self, one_mul]
    exact eq_zero_or_one_of_mul_self (congrFun h2 j)
  have horth : ∀ i i' j, i ≠ i' → φ (Pi.single i 1) j * φ (Pi.single i' 1) j = 0 := by
    intro i i' j hii
    have h2 : φ (Pi.single i 1) * φ (Pi.single i' 1) = 0 := by
      rw [← map_mul, single_mul_single_ne hii, map_zero]
    exact congrFun h2 j
  have hsum : ∀ j, ∑ i, φ (Pi.single i 1) j = 1 := by
    intro j
    have h1 : ∑ i, (Pi.single i (1 : L) : ι → L) = 1 := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : ∑ i, φ (Pi.single i 1) = 1 := by rw [← map_sum, h1, map_one]
    have := congrFun h2 j
    simpa [Finset.sum_apply] using this
  have hex : ∀ j, ∃ i, φ (Pi.single i 1) j = 1 := by
    intro j
    by_contra hcon
    push Not at hcon
    have : ∑ i, φ (Pi.single i 1) j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hid i j with h | h
      · exact h
      · exact absurd h (hcon i)
    rw [hsum j] at this
    exact one_ne_zero this
  have huniq : ∀ j i i', φ (Pi.single i 1) j = 1 → φ (Pi.single i' 1) j = 1 → i = i' := by
    intro j i i' h h'
    by_contra hne
    have := horth i i' j hne
    rw [h, h', one_mul] at this
    exact one_ne_zero this
  choose ρ hρ using hex
  have hρsurj : Function.Surjective ρ := by
    intro i
    have hne : φ (Pi.single i 1) ≠ 0 := by
      intro h
      have : (Pi.single i (1 : L) : ι → L) = 0 := φ.injective (by rw [h, map_zero])
      have := congrFun this i
      simp at this
    obtain ⟨j, hj⟩ : ∃ j, φ (Pi.single i 1) j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext hcon)
    have hj1 : φ (Pi.single i 1) j = 1 := (hid i j).resolve_left hj
    exact ⟨j, huniq j _ _ (hρ j) hj1⟩
  have hρbij : Function.Bijective ρ := ⟨Finite.injective_iff_surjective.mpr hρsurj, hρsurj⟩
  refine ⟨(Equiv.ofBijective ρ hρbij).symm, fun i => ?_⟩
  ext j
  by_cases hj : j = (Equiv.ofBijective ρ hρbij).symm i
  · subst hj
    have h1 : ρ ((Equiv.ofBijective ρ hρbij).symm i) = i :=
      (Equiv.ofBijective ρ hρbij).apply_symm_apply i
    have := hρ ((Equiv.ofBijective ρ hρbij).symm i)
    rw [h1] at this
    simpa using this
  · have hne : ρ j ≠ i := by
      intro h
      apply hj
      rw [← h]
      exact ((Equiv.ofBijective ρ hρbij).symm_apply_apply j).symm
    rw [Pi.single_eq_of_ne hj]
    rcases hid i j with h | h
    · exact h
    · exact absurd (huniq j _ _ (hρ j) h) hne

omit [Fintype ι] in
theorem apply_single_eq (φ : (ι → L) ≃ₐ[K] (ι → L)) (π : Equiv.Perm ι)
    (hπ : ∀ i, φ (Pi.single i 1) = Pi.single (π i) 1) (i : ι) (a : L) :
    φ (Pi.single i a) = Pi.single (π i) (φ (Pi.single i a) (π i)) := by
  have h1 : (Pi.single i a : ι → L) = Pi.single i 1 * Pi.single i a := by
    rw [single_mul_single_self, one_mul]
  have h2 : φ (Pi.single i a) = Pi.single (π i) 1 * φ (Pi.single i a) := by
    conv_lhs => rw [h1]
    rw [map_mul, hπ]
  ext j
  by_cases hj : j = π i
  · subst hj; simp
  · have := congrFun h2 j
    rw [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul] at this
    rw [this, Pi.single_eq_of_ne hj]

omit [Fintype ι] in
noncomputable def compHom (φ : (ι → L) ≃ₐ[K] (ι → L)) (π : Equiv.Perm ι)
    (hπ : ∀ i, φ (Pi.single i 1) = Pi.single (π i) 1) (i : ι) : L →ₐ[K] L where
  toFun a := φ (Pi.single i a) (π i)
  map_one' := by simp [hπ]
  map_mul' a b := by
    rw [← single_mul_single_self, map_mul, Pi.mul_apply]
  map_zero' := by simp
  map_add' a b := by
    rw [Pi.single_add, map_add, Pi.add_apply]
  commutes' c := by
    have h1 : (Pi.single i (algebraMap K L c) : ι → L) =
        algebraMap K (ι → L) c * Pi.single i 1 := by
      ext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    show φ (Pi.single i (algebraMap K L c)) (π i) = algebraMap K L c
    rw [h1, map_mul, AlgEquiv.commutes, hπ]
    simp

theorem exists_perm_tau [FiniteDimensional K L] (φ : (ι → L) ≃ₐ[K] (ι → L)) :
    ∃ (π : Equiv.Perm ι) (τ : ι → (L ≃ₐ[K] L)), ∀ (x : ι → L) (i : ι),
      φ x (π i) = τ i (x i) := by
  obtain ⟨π, hπ⟩ := exists_perm_idem φ
  refine ⟨π, fun i => AlgEquiv.ofBijective (compHom φ π hπ i) (AlgHom.bijective _), ?_⟩
  intro x i
  have hx : x = ∑ k, (Pi.single k (x k) : ι → L) := (Finset.univ_sum_single x).symm
  have h1 : φ x (π i) = ∑ k, φ (Pi.single k (x k)) (π i) := by
    conv_lhs => rw [hx]
    rw [map_sum, Finset.sum_apply]
  rw [h1, Finset.sum_eq_single i]
  · rfl
  · intro k _ hk
    rw [apply_single_eq φ π hπ k (x k), Pi.single_eq_of_ne]
    exact fun h => hk (π.injective h).symm
  · intro h; exact absurd (Finset.mem_univ i) h

end Aut

section Tor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K L : Type*} [Field K] [Field L] [Algebra K L]

omit [Fintype ι] in
theorem single_one_mem_adjoin [FiniteDimensional K L] {μ : Set L} (hμ1 : (1 : L) ∈ μ)
    (hne : ∃ m ∈ μ, m ≠ 1) (i : ι) :
    (Pi.single i (1 : L) : ι → L) ∈ Algebra.adjoin K {x : ι → L | ∀ i, x i ∈ μ} := by
  obtain ⟨m, hm, hm1⟩ := hne
  set C := Algebra.adjoin K {x : ι → L | ∀ i, x i ∈ μ} with hC
  have hz : (Function.update (1 : ι → L) i m) ∈ {x : ι → L | ∀ i, x i ∈ μ} := by
    intro k
    by_cases hk : k = i
    · subst hk; simpa using hm
    · simpa [Function.update_of_ne hk] using hμ1
  have hzC : Function.update (1 : ι → L) i m ∈ C := Algebra.subset_adjoin hz
  have hint : IsIntegral K m := Algebra.IsIntegral.isIntegral m
  set f := minpoly K m with hf
  have hfC : Polynomial.aeval (Function.update (1 : ι → L) i m) f ∈ C := by
    have h1 : Algebra.adjoin K {Function.update (1 : ι → L) i m} ≤ C :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hzC)
    exact h1 (Polynomial.aeval_mem_adjoin_singleton K _)
  have hc : f.eval 1 ≠ 0 := by
    intro h0
    have hdvd : Polynomial.X - Polynomial.C (1 : K) ∣ f := Polynomial.dvd_iff_isRoot.mpr h0
    obtain ⟨g, hg⟩ := hdvd
    have hirr : Irreducible f := minpoly.irreducible hint
    rcases hirr.isUnit_or_isUnit hg with hu | hu
    · exact (Polynomial.not_isUnit_X_sub_C (1 : K)) hu
    · obtain ⟨u, hu0, hgu⟩ := Polynomial.isUnit_iff.mp hu
      have h1 : Polynomial.aeval m f = 0 := minpoly.aeval K m
      rw [hg, ← hgu] at h1
      simp [sub_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hm1 h1
      · exact hu0.ne_zero (by simpa using h1)
  have hcoord : ∀ k, Polynomial.aeval (Function.update (1 : ι → L) i m) f k =
      if k = i then 0 else algebraMap K L (f.eval 1) := by
    intro k
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom K (fun _ : ι => L) k)
      (Function.update (1 : ι → L) i m) f
    have h2 : (Pi.evalAlgHom K (fun _ : ι => L) k)
        (Polynomial.aeval (Function.update (1 : ι → L) i m) f)
        = Polynomial.aeval (Function.update (1 : ι → L) i m) f k := rfl
    rw [← h2, ← this]
    by_cases hk : k = i
    · subst hk
      have h3 : Polynomial.aeval m f = 0 := minpoly.aeval K m
      simp [h3]
    · simp [hk, Polynomial.aeval_def, Polynomial.eval₂_at_one]
  have hone : (1 : ι → L) - Pi.single i 1 = algebraMap K (ι → L) (f.eval 1)⁻¹ *
      Polynomial.aeval (Function.update (1 : ι → L) i m) f := by
    ext k
    rw [Pi.mul_apply, hcoord k]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, Pi.algebraMap_apply, hc]
  have : (Pi.single i (1 : L) : ι → L) = 1 - algebraMap K (ι → L) (f.eval 1)⁻¹ *
      Polynomial.aeval (Function.update (1 : ι → L) i m) f := by
    rw [← hone]; abel
  rw [this]
  exact C.sub_mem C.one_mem (C.mul_mem (C.algebraMap_mem _) hfC)

theorem adjoin_torus_eq_top [FiniteDimensional K L] {μ : Set L} (hμ1 : (1 : L) ∈ μ)
    (hspan : Submodule.span K μ = ⊤) (hne : ∃ m ∈ μ, m ≠ 1) :
    Algebra.adjoin K {x : ι → L | ∀ i, x i ∈ μ} = ⊤ := by
  set C := Algebra.adjoin K {x : ι → L | ∀ i, x i ∈ μ} with hC
  have hsingle : ∀ i a, (Pi.single i a : ι → L) ∈ C := by
    intro i a
    have ha : a ∈ Submodule.span K μ := by rw [hspan]; trivial
    induction ha using Submodule.span_induction with
    | mem m hm =>
      have hz : (Function.update (1 : ι → L) i m) ∈ {x : ι → L | ∀ i, x i ∈ μ} := by
        intro k
        by_cases hk : k = i
        · subst hk; simpa using hm
        · simpa [Function.update_of_ne hk] using hμ1
      have h1 : (Pi.single i m : ι → L) = Pi.single i 1 * Function.update (1 : ι → L) i m := by
        ext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
      rw [h1]
      exact C.mul_mem (single_one_mem_adjoin hμ1 hne i) (Algebra.subset_adjoin hz)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Pi.single_add]; exact C.add_mem hx hy
    | smul c x _ hx =>
      have : (Pi.single i (c • x) : ι → L) = algebraMap K (ι → L) c * Pi.single i x := by
        ext k
        by_cases hk : k = i
        · subst hk; simp [Algebra.smul_def]
        · simp [Pi.single_eq_of_ne hk]
      rw [this]
      exact C.mul_mem (C.algebraMap_mem c) hx
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  exact C.sum_mem fun i _ => hsingle i (x i)

variable (K) in
@[expose] noncomputable def mulAlg : (ι → L) →ₐ[K] Module.End K (ι → L) :=
  Algebra.lsmul K (A := ι → L) K (ι → L)

omit [Fintype ι] [DecidableEq ι] in
theorem mulAlg_apply (a v : ι → L) : mulAlg K a v = a * v := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem mulAlg_injective : Function.Injective (mulAlg K (ι := ι) (L := L)) := by
  intro a b h
  have := LinearMap.congr_fun h 1
  simpa [mulAlg_apply] using this

theorem exists_algEquiv_of_conj [FiniteDimensional K L] {μ : Set L} (hμ1 : (1 : L) ∈ μ)
    (hspan : Submodule.span K μ = ⊤) (hne : ∃ m ∈ μ, m ≠ 1) (g : (ι → L) ≃ₗ[K] (ι → L))
    (hg : ∀ x : ι → L, (∀ i, x i ∈ μ) →
      ∃ y : ι → L, LinearEquiv.conjAlgEquiv K g (mulAlg K x) = mulAlg K y) :
    ∃ φ : (ι → L) ≃ₐ[K] (ι → L), ∀ x,
      LinearEquiv.conjAlgEquiv K g (mulAlg K x) = mulAlg K (φ x) := by
  set c := LinearEquiv.conjAlgEquiv K g with hc
  have hmi : Function.Injective (mulAlg K (ι := ι) (L := L)) := mulAlg_injective
  have hall : ∀ x : ι → L, ∃ y : ι → L, c (mulAlg K x) = mulAlg K y := by
    intro x
    have hx : x ∈ Algebra.adjoin K {x : ι → L | ∀ i, x i ∈ μ} := by
      rw [adjoin_torus_eq_top hμ1 hspan hne]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap r =>
      exact ⟨algebraMap K (ι → L) r, by rw [AlgHom.commutes, AlgEquiv.commutes]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a * b, by rw [map_mul, map_mul, map_mul, ha, hb]⟩
  choose φ₀ hφ₀ using hall
  have hinj : Function.Injective φ₀ := by
    intro x y hxy
    have : c (mulAlg K x) = c (mulAlg K y) := by rw [hφ₀, hφ₀, hxy]
    exact hmi (c.injective this)
  let φ₁ : (ι → L) →ₐ[K] (ι → L) :=
    { toFun := φ₀
      map_one' := by
        refine hmi ?_
        rw [← hφ₀]; simp
      map_mul' := fun x y => by
        refine hmi ?_
        rw [map_mul, ← hφ₀, ← hφ₀, ← hφ₀, map_mul, map_mul]
      map_zero' := by
        refine hmi ?_
        rw [← hφ₀]; simp
      map_add' := fun x y => by
        refine hmi ?_
        rw [map_add, ← hφ₀, ← hφ₀, ← hφ₀, map_add, map_add]
      commutes' := fun r => by
        refine hmi ?_
        rw [← hφ₀]; simp [AlgHom.commutes, AlgEquiv.commutes] }
  have hbij : Function.Bijective φ₁ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective (f := φ₁.toLinearMap)).mp hinj
  exact ⟨AlgEquiv.ofBijective φ₁ hbij, fun x => hφ₀ x⟩

theorem normalizer_torus [FiniteDimensional K L] {μ : Set L} (hμ1 : (1 : L) ∈ μ)
    (hspan : Submodule.span K μ = ⊤) (hne : ∃ m ∈ μ, m ≠ 1) (g : (ι → L) ≃ₗ[K] (ι → L))
    (hg : ∀ x : ι → L, (∀ i, x i ∈ μ) →
      ∃ y : ι → L, LinearEquiv.conjAlgEquiv K g (mulAlg K x) = mulAlg K y) :
    ∃ (π : Equiv.Perm ι) (τ : ι → (L ≃ₐ[K] L)), ∀ (x y : ι → L),
      LinearEquiv.conjAlgEquiv K g (mulAlg K x) = mulAlg K y → ∀ i, y (π i) = τ i (x i) := by
  obtain ⟨φ, hφ⟩ := exists_algEquiv_of_conj hμ1 hspan hne g hg
  obtain ⟨π, τ, hπτ⟩ := exists_perm_tau φ
  refine ⟨π, τ, fun x y hxy i => ?_⟩
  have : y = φ x := mulAlg_injective (hxy.symm.trans (hφ x))
  rw [this]
  exact hπτ x i

end Tor

end CFSG.RankThree.PartOne.KFQ
