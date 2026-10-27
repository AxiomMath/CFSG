module

public import CFSG.LinearAlgebra.RootGroupSL.FpfCommon
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Filtration
import Mathlib.FieldTheory.Finite.Extension
public import CFSG.LinearAlgebra.RootGroupSL.FpfArith

public section

namespace CFSG.StandardType.LieKnownR2.SpecialLinearNC

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open

private theorem finite_sl_dspace {k X : Type} [Field k] [Finite k] [AddCommGroup X]
    [Module k X] [Module.Finite k X] : Finite (SpecialLinearGroup k (DSpace k X)) := by
  haveI : Finite X := Module.finite_of_finite k
  haveI : Finite (DSpace k X ≃ₗ[k] DSpace k X) :=
    Finite.of_injective (fun e : DSpace k X ≃ₗ[k] DSpace k X => e.toEquiv.toFun)
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  infer_instance

private theorem eq_mulLeft_apply_one {k : Type} [Field k] (f : k →ₗ[k] k) :
    f = LinearMap.mulLeft k (f 1) := by
  refine LinearMap.ext fun s => ?_
  have := f.map_smul s 1
  simpa [mul_comm] using this

private theorem blockSL_mem_normalizer {k X : Type} [Field k] [Finite k] [AddCommGroup X]
    [Module k X] [Module.Finite k X] (a b : k ≃ₗ[k] k) (g : X ≃ₗ[k] X)
    (hdet : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1) :
    blockSL a g b hdet ∈ Subgroup.normalizer
      (rootSL k k X : Set (SpecialLinearGroup k (DSpace k X))) := by
  rw [blockSL_mem_normalizer_iff]
  intro t
  exact ⟨_, eq_mulLeft_apply_one _⟩

private theorem mem_rootSL_of_commute {k X : Type} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup X] [Module k X] [Module.Finite k X] (a b : k ≃ₗ[k] k) (g : X ≃ₗ[k] X)
    (hdet : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1)
    (hφ : ∀ φ : X →ₗ[k] k, a.toLinearMap ∘ₗ φ = φ ∘ₗ g.toLinearMap → φ = 0)
    (hχ : ∀ χ : k →ₗ[k] X, g.toLinearMap ∘ₗ χ = χ ∘ₗ b.toLinearMap → χ = 0)
    {y : SpecialLinearGroup k (DSpace k X)} (hy : y ∈ QK k k X)
    (hcomm : y * blockSL a g b hdet = blockSL a g b hdet * y) : y ∈ rootSL k k X := by
  obtain ⟨φ, χ, ψ, hyeq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hy)
  have hfix_sl : blockSL a g b hdet * y * (blockSL a g b hdet)⁻¹ = y := by
    rw [← hcomm, mul_inv_cancel_right]
  have hfix := blockDiag_conj_of_centralizer hfix_sl rfl hyeq
  obtain ⟨h1, h2, -⟩ := (blockDiag_conj_unipElt_eq_iff a g b φ χ ψ).mp hfix
  rw [mem_rootSL_iff]
  refine ⟨ψ 1, ?_⟩
  rw [hyeq, hφ φ h1, hχ χ h2, rootEquiv, shearE_eq_unipElt, ← eq_mulLeft_apply_one ψ]

private theorem exists_unit_prime_order {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) : ∃ (l : kˣ) (r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf l = r := by
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hcard⟩ := FiniteField.card k 2
  have hcardk : Nat.card k = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units, hcardk]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      (Even.pow_of_ne_zero even_two (Nat.pos_iff_ne_zero.mp n.pos)) odd_one
  have hne : Nat.card kˣ ≠ 1 := by
    rw [Nat.card_units]
    omega
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) r hdvd
  exact ⟨l, r, hr, hr2, hl⟩

private theorem mulLeftEquiv_pow_apply {k : Type} [Field k] (l : kˣ) (n : ℕ) (x : k) :
    ((mulLeftEquiv k l) ^ n) x = ((l : k) ^ n) * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, mulLeftEquiv_apply, ih, pow_succ]
    ring

private theorem exists_fpf_large {k X : Type} [Field k] [Finite k] [CharP k 2] [AddCommGroup X]
    [Module k X] [Module.Finite k X] (hk : 4 ≤ Nat.card k) :
    ∃ (h : SpecialLinearGroup k (DSpace k X)) (r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf h = r ∧
      h ∈ Subgroup.normalizer (rootSL k k X : Set (SpecialLinearGroup k (DSpace k X))) ∧
      ∀ y ∈ QK k k X, y * h = h * y → y ∈ rootSL k k X := by
  obtain ⟨l, r, hr, hr2, hord⟩ := exists_unit_prime_order hk
  haveI : Fact r.Prime := ⟨hr⟩
  have hl1 : (l : k) ≠ 1 := by
    intro h1
    have h2 : l = 1 := Units.ext h1
    rw [h2, orderOf_one] at hord
    exact hr.one_lt.ne hord
  have hdet : LinearEquiv.det (mulLeftEquiv k l) * LinearEquiv.det (1 : X ≃ₗ[k] X) *
      LinearEquiv.det (mulLeftEquiv k l)⁻¹ = 1 := by
    rw [map_inv, map_one, mul_one, mul_inv_cancel]
  have har : mulLeftEquiv k l ^ r = 1 := by
    refine LinearEquiv.ext fun x => ?_
    rw [mulLeftEquiv_pow_apply, ← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
    simp
  refine ⟨blockSL (mulLeftEquiv k l) 1 (mulLeftEquiv k l)⁻¹ hdet, r, hr, hr2, ?_,
    blockSL_mem_normalizer _ _ _ hdet, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · apply SpecialLinearGroup.toLinearEquiv_injective
      rw [map_pow, map_one]
      change (blockDiag (mulLeftEquiv k l) 1 (mulLeftEquiv k l)⁻¹) ^ r = 1
      rw [blockDiag_pow, har, one_pow, inv_pow, har, inv_one, blockDiag_one]
    · intro h1
      have := congrArg (fun z : SpecialLinearGroup k (DSpace k X) =>
        ((z : DSpace k X ≃ₗ[k] DSpace k X) ((1 : k), (0 : X), (0 : k))).1) h1
      simp [blockSL, blockDiag, mulLeftEquiv_apply] at this
      exact hl1 (Units.val_eq_one.2 this)
  · intro y hy hcomm
    refine mem_rootSL_of_commute _ _ _ hdet ?_ ?_ hy hcomm
    · intro φ hφ
      refine LinearMap.ext fun x => ?_
      have h1 := congrArg (fun f : X →ₗ[k] k => f x) hφ
      simp [mulLeftEquiv_apply] at h1
      have h2 : ((l : k) - 1) * φ x = 0 := by rw [sub_mul, one_mul, h1, sub_self]
      simpa [sub_ne_zero.2 hl1] using h2
    · intro χ hχ
      have h1 := congrArg (fun f : k →ₗ[k] X => f 1) hχ
      have hinv : (mulLeftEquiv k l)⁻¹ 1 = ((l⁻¹ : kˣ) : k) := by
        change (mulLeftEquiv k l).symm 1 = _
        rw [LinearEquiv.symm_apply_eq, mulLeftEquiv_apply]
        simp
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hinv] at h1
      have h3 : χ ((l⁻¹ : kˣ) : k) = ((l⁻¹ : kˣ) : k) • χ 1 := by
        simpa using χ.map_smul ((l⁻¹ : kˣ) : k) 1
      have hne : (1 - ((l⁻¹ : kˣ) : k)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h4
        exact hl1 (by simpa using congrArg (fun z : k => z⁻¹) h4.symm)
      have h4 : (1 - ((l⁻¹ : kˣ) : k)) • χ 1 = 0 := by
        rw [sub_smul, one_smul, ← h3, ← h1]
        simp
      have h5 : χ 1 = 0 := (smul_eq_zero.1 h4).resolve_left hne
      refine LinearMap.ext fun s => ?_
      simpa [h5] using χ.map_smul s 1

private theorem eq_zero_of_comp_eq {k X : Type} [Field k] [AddCommGroup X] [Module k X]
    [Module.Finite k X] (g : X ≃ₗ[k] X) (hg : ∀ x, g x = x → x = 0) (φ : X →ₗ[k] k)
    (h : φ ∘ₗ g.toLinearMap = φ) : φ = 0 := by
  have hinj : Function.Injective (g.toLinearMap - LinearMap.id : X →ₗ[k] X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact hg x (sub_eq_zero.1 (by simpa using hx))
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  refine LinearMap.ext fun z => ?_
  obtain ⟨w, rfl⟩ := hsurj z
  have := congrArg (fun f : X →ₗ[k] k => f w) h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  simp [map_sub, this]

private theorem exists_singer_aux {k X L : Type} [Field k] [AddCommGroup X] [Module k X] [Field L]
    [Algebra k L] [Finite L] (e : X ≃ₗ[k] L) (hodd : Odd (Nat.card Lˣ))
    (hne : Nat.card Lˣ ≠ 1) :
    ∃ (g : X ≃ₗ[k] X) (r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf g = r ∧ ∀ x, g x = x → x = 0 := by
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ν, hν⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) r hdvd
  have hν1 : (ν : L) ≠ 1 := by
    intro h1
    have h2 : ν = 1 := Units.ext h1
    rw [h2, orderOf_one] at hν
    exact hr.one_lt.ne hν
  have hgx : ∀ x : X, (e.trans ((mulLeftEquiv k ν).trans e.symm)) x = e.symm ((ν : L) * e x) := by
    intro x
    simp [mulLeftEquiv_apply]
  have hgpow : ∀ (n : ℕ) (x : X),
      ((e.trans ((mulLeftEquiv k ν).trans e.symm)) ^ n) x = e.symm (((ν : L) ^ n) * e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, LinearEquiv.mul_apply, ih, hgx, LinearEquiv.apply_symm_apply, pow_succ]
      congr 1
      ring
  have hfix : ∀ x, (e.trans ((mulLeftEquiv k ν).trans e.symm)) x = x → x = 0 := by
    intro x hx
    rw [hgx] at hx
    have h1 : (ν : L) * e x = e x := by
      have := congrArg e hx
      simpa using this
    have h2 : ((ν : L) - 1) * e x = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    have h3 : e x = 0 := (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hν1)
    exact e.injective (by simpa using h3)
  refine ⟨e.trans ((mulLeftEquiv k ν).trans e.symm), r, hr, hr2, orderOf_eq_prime ?_ ?_, hfix⟩
  · refine LinearEquiv.ext fun x => ?_
    rw [hgpow, ← hν, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
    simp
  · intro h1
    have h2 : e.symm 1 ≠ 0 := by
      intro h
      have := congrArg e h
      simp at this
    exact h2 (hfix _ (by rw [h1]; rfl))

private theorem exists_fpf_two {k X : Type} [Field k] [Finite k] [CharP k 2] [AddCommGroup X]
    [Module k X] [Module.Finite k X] (hk : Nat.card k = 2) (hX : 2 ≤ Module.finrank k X) :
    ∃ (h : SpecialLinearGroup k (DSpace k X)) (r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf h = r ∧
      h ∈ Subgroup.normalizer (rootSL k k X : Set (SpecialLinearGroup k (DSpace k X))) ∧
      ∀ y ∈ QK k k X, y * h = h * y → y ∈ rootSL k k X := by
  haveI : NeZero (Module.finrank k X) := ⟨by omega⟩
  have hLcard : Nat.card (FiniteField.Extension k 2 (Module.finrank k X)) =
      2 ^ Module.finrank k X := by
    rw [FiniteField.natCard_extension, hk]
  have hLu : Nat.card (FiniteField.Extension k 2 (Module.finrank k X))ˣ =
      2 ^ Module.finrank k X - 1 := by
    rw [Nat.card_units, hLcard]
  obtain ⟨g, r, hr, hr2, hord, hfix⟩ := exists_singer_aux
    (LinearEquiv.ofFinrankEq X (FiniteField.Extension k 2 (Module.finrank k X))
      (FiniteField.finrank_extension k 2 _).symm)
    (by
      rw [hLu]
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
        (Even.pow_of_ne_zero even_two (by omega)) odd_one)
    (by
      rw [hLu]
      have : 2 ^ 2 ≤ 2 ^ Module.finrank k X := Nat.pow_le_pow_right (by norm_num) hX
      omega)
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Subsingleton kˣ := (Nat.card_eq_one_iff_unique.1 (by rw [Nat.card_units, hk])).1
  have hdet : LinearEquiv.det (1 : k ≃ₗ[k] k) * LinearEquiv.det g *
      LinearEquiv.det (1 : k ≃ₗ[k] k) = 1 := Subsingleton.elim _ _
  refine ⟨blockSL 1 g 1 hdet, r, hr, hr2, ?_, blockSL_mem_normalizer _ _ _ hdet, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · apply SpecialLinearGroup.toLinearEquiv_injective
      rw [map_pow, map_one]
      change (blockDiag 1 g 1) ^ r = 1
      rw [blockDiag_pow, one_pow, ← hord, pow_orderOf_eq_one, blockDiag_one]
    · intro h1
      obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank k X)
      have := congrArg (fun z : SpecialLinearGroup k (DSpace k X) =>
        ((z : DSpace k X ≃ₗ[k] DSpace k X) ((0 : k), x, (0 : k))).2.1) h1
      simp [blockSL, blockDiag] at this
      exact hx (hfix x this)
  · intro y hy hcomm
    refine mem_rootSL_of_commute _ _ _ hdet ?_ ?_ hy hcomm
    · intro φ hφ
      exact eq_zero_of_comp_eq g hfix φ (by simpa using hφ.symm)
    · intro χ hχ
      refine LinearMap.ext fun s => ?_
      have h1 := congrArg (fun f : k →ₗ[k] X => f s) hχ
      simpa using hfix _ (by simpa using h1)

theorem exists_primeOrder_fpf_rootSL {k X : Type} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup X] [Module k X] [Module.Finite k X]
    (hk : 4 ≤ Nat.card k ∨ 2 ≤ Module.finrank k X) :
    ∃ (h : SpecialLinearGroup k (DSpace k X)) (r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf h = r ∧
      h ∈ Subgroup.normalizer (rootSL k k X : Set (SpecialLinearGroup k (DSpace k X))) ∧
      ∀ y ∈ QK k k X, y * h = h * y → y ∈ rootSL k k X := by
  by_cases h4 : 4 ≤ Nat.card k
  · exact exists_fpf_large h4
  · haveI : Fintype k := Fintype.ofFinite k
    obtain ⟨n, -, hcard⟩ := FiniteField.card k 2
    have hcardk : Nat.card k = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
    have hn : (n : ℕ) = 1 := by
      by_contra hn1
      have h2 : 2 ≤ (n : ℕ) := by have := n.pos; omega
      have : 2 ^ 2 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
      omega
    exact exists_fpf_two (by rw [hcardk, hn]; rfl) (hk.resolve_left h4)

theorem ggRootNoCentralAt_top_rootSL {k X : Type} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup X] [Module k X] [Module.Finite k X] (hX : 1 ≤ Module.finrank k X)
    (hk : 4 ≤ Nat.card k ∨ 2 ≤ Module.finrank k X) :
    GGRootNoCentralAt (⊤ : Subgroup (SpecialLinearGroup k (DSpace k X))) (rootSL k k X) := by
  haveI : Finite (SpecialLinearGroup k (DSpace k X)) := finite_sl_dspace
  obtain ⟨h, r, hr, hr2, hord, hN, hfix⟩ := exists_primeOrder_fpf_rootSL (X := X) hk
  refine noCentral_of_fixedPoint hr hr2 hord ⟨Subgroup.mem_top h, hN⟩ fun y hy hcomm => ?_
  rw [top_inf_eq, pCoreOf_normalizer_rootSL hX] at hy
  exact hfix y hy hcomm.symm

end CFSG.StandardType.LieKnownR2.SpecialLinearNC


