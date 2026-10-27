module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpQv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)

variable {r : ℕ} {K : Type} [Field K]

private lemma spForm_add_right (y z w : Fin r ⊕ Fin r → K) :
    spForm y (z + w) = spForm y z + spForm y w := by
  simp [spForm, Matrix.mulVec_add, dotProduct_add]

private lemma spForm_smul_right (y z : Fin r ⊕ Fin r → K) (c : K) :
    spForm y (c • z) = c * spForm y z := by
  simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma spForm_sub_right (y z w : Fin r ⊕ Fin r → K) :
    spForm y (z - w) = spForm y z - spForm y w := by
  simp [spForm, Matrix.mulVec_sub, dotProduct_sub]

private lemma spForm_neg_left (y z : Fin r ⊕ Fin r → K) :
    spForm (-y) z = -spForm y z := by
  simp [spForm, dotProduct, Finset.sum_neg_distrib]

private lemma spT_smul_right (c a : Fin r ⊕ Fin r → K) (s : K) :
    spT c (s • a) = s • spT c a := by
  simp only [spT, smul_vecMulVec]

private lemma spT_smul_left (c a : Fin r ⊕ Fin r → K) (s : K) :
    spT (s • c) a = s • spT c a := by
  simp only [spT, Matrix.mulVec_smul, vecMulVec_smul]

private lemma spN_smul_left (a c : Fin r ⊕ Fin r → K) (s : K) :
    spN (s • a) c = s • spN a c := by
  rw [spN, spN, spT_smul_right, spT_smul_left, smul_add]

private lemma spN_smul_right (a c : Fin r ⊕ Fin r → K) (s : K) :
    spN a (s • c) = s • spN a c := by
  rw [spN, spN, spT_smul_left, spT_smul_right, smul_add]

private lemma spN_mul_spN (a c a' c' : Fin r ⊕ Fin r → K) :
    spN a c * spN a' c' = spForm a' c • spT c' a + spForm c' c • spT a' a +
      spForm a' a • spT c' c + spForm c' a • spT a' c := by
  simp only [spN, Matrix.add_mul, Matrix.mul_add, spT_mul_spT]
  abel

private lemma isSp_sub {M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : Mᵀ * formJ r K + formJ r K * M = 0)
    (hN : Nᵀ * formJ r K + formJ r K * N = 0) :
    (M - N)ᵀ * formJ r K + formJ r K * (M - N) = 0 := by
  have h : (M - N)ᵀ * formJ r K + formJ r K * (M - N) =
      (Mᵀ * formJ r K + formJ r K * M) - (Nᵀ * formJ r K + formJ r K * N) := by
    rw [transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h, hM, hN, sub_zero]

private lemma mulVec_mulVec_eq {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) (y : Fin r ⊕ Fin r → K) : a *ᵥ (a *ᵥ y) = d • y := by
  rw [Matrix.mulVec_mulVec, hd, Matrix.smul_mulVec, Matrix.one_mulVec]

private lemma mulVec_ne_zero {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) (hd0 : d ≠ 0) {y : Fin r ⊕ Fin r → K} (hy : y ≠ 0) :
    a *ᵥ y ≠ 0 := by
  intro h
  apply hy
  have h1 := mulVec_mulVec_eq hd y
  rw [h, Matrix.mulVec_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hd0

private lemma isSquare_of_eigen {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) {y : Fin r ⊕ Fin r → K} (hy : y ≠ 0) (c : K)
    (h : a *ᵥ y = c • y) : IsSquare d := by
  have h1 : d • y = (c * c) • y := by
    rw [← mulVec_mulVec_eq hd y, h, Matrix.mulVec_smul, h, smul_smul]
  have h2 : (d - c * c) • y = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : d - c * c = 0 := (smul_eq_zero.mp h2).resolve_right hy
  exact ⟨c, by rw [← sub_eq_zero]; exact h3⟩

private lemma notMem_span_singleton_of_nonsquare {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    {d : K} (hd : a * a = d • 1) (hdsq : ¬ IsSquare d) {y : Fin r ⊕ Fin r → K}
    (hy : y ≠ 0) : a *ᵥ y ∉ Submodule.span K {y} := by
  intro h
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact hdsq (isSquare_of_eigen hd hy c hc.symm)

private lemma transpose_formJ_mul_eq {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hA : aᵀ * formJ r K * a = d • formJ r K) (hd : a * a = d • 1) (hd0 : d ≠ 0) :
    aᵀ * formJ r K = formJ r K * a := by
  have h1 : a * (d⁻¹ • a) = 1 := by
    rw [Matrix.mul_smul, hd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have h2 : aᵀ * formJ r K * (a * (d⁻¹ • a)) = d • (formJ r K * (d⁻¹ • a)) := by
    rw [← Matrix.mul_assoc, hA, Matrix.smul_mul]
  calc aᵀ * formJ r K = aᵀ * formJ r K * 1 := (Matrix.mul_one _).symm
    _ = aᵀ * formJ r K * (a * (d⁻¹ • a)) := by rw [h1]
    _ = d • (formJ r K * (d⁻¹ • a)) := h2
    _ = d • (d⁻¹ • (formJ r K * a)) := by rw [Matrix.mul_smul]
    _ = formJ r K * a := by rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]

private lemma spForm_self_adjoint {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hA : aᵀ * formJ r K * a = d • formJ r K) (hd : a * a = d • 1) (hd0 : d ≠ 0)
    (y z : Fin r ⊕ Fin r → K) : spForm (a *ᵥ y) z = spForm y (a *ᵥ z) := by
  have hJA := transpose_formJ_mul_eq hA hd hd0
  simp only [spForm]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJA,
    ← Matrix.mulVec_mulVec]

private lemma span_four_lt_top (hr : 3 ≤ r) (x₁ x₂ x₃ x₄ : Fin r ⊕ Fin r → K) :
    Submodule.span K ({x₁, x₂, x₃, x₄} : Set (Fin r ⊕ Fin r → K)) < ⊤ := by
  classical
  have hle : Set.finrank K ({x₁, x₂, x₃, x₄} : Set (Fin r ⊕ Fin r → K)) ≤ 4 := by
    have h := finrank_span_finset_le_card (R := K)
      ({x₁, x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
    have hcard : ({x₁, x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K)).card ≤ 4 := by
      have h1 := Finset.card_insert_le x₁ ({x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
      have h2 := Finset.card_insert_le x₂ ({x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
      have h3 := Finset.card_insert_le x₃ ({x₄} : Finset (Fin r ⊕ Fin r → K))
      have h4 : ({x₄} : Finset (Fin r ⊕ Fin r → K)).card ≤ 1 := by simp
      omega
    simpa using le_trans h hcard
  rw [lt_top_iff_ne_top]
  intro htop
  have h2 : Module.finrank K (⊤ : Submodule K (Fin r ⊕ Fin r → K)) ≤ 4 := htop ▸ hle
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h2
  simp only [Fintype.card_sum, Fintype.card_fin] at h2
  omega

private lemma mem_span_three {V : Type} [AddCommGroup V] [Module K V] (v e g x : V)
    (h : x ∈ Submodule.span K ({v, e, g} : Set V)) :
    ∃ α β γ : K, x = α • v + β • e + γ • g := by
  rw [show ({v, e, g} : Set V) = insert v (insert e {g}) by simp] at h
  rw [Submodule.mem_span_insert] at h
  obtain ⟨α, z, hz, rfl⟩ := h
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨β, w, hw, rfl⟩ := hz
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨γ, rfl⟩ := hw
  exact ⟨α, β, γ, by rw [add_assoc]⟩

private lemma notMem_span_image {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) (hdsq : ¬ IsSquare d) {v e f : Fin r ⊕ Fin r → K}
    (hav : a *ᵥ v = e) (hae : a *ᵥ e = d • v)
    (hf : f ∉ Submodule.span K ({v, e} : Set (Fin r ⊕ Fin r → K))) :
    f ∉ Submodule.span K ({v, e, a *ᵥ f} : Set (Fin r ⊕ Fin r → K)) := by
  intro hmem
  obtain ⟨α, β, γ, hdec⟩ := mem_span_three v e (a *ᵥ f) f hmem
  have hγ : γ ≠ 0 := by
    intro h0
    apply hf
    rw [hdec, h0, zero_smul, add_zero]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ α (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ β (Submodule.subset_span (by simp)))
  have h1 : f = α • v + β • e + γ • (a *ᵥ f) := hdec
  have h2 : a *ᵥ f = α • e + (β * d) • v + (γ * d) • f := by
    conv_lhs => rw [h1]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hav, hae, mulVec_mulVec_eq hd f]
    simp only [smul_smul]
  have h3 : f = α • v + β • e + γ • (α • e + (β * d) • v + (γ * d) • f) := by
    calc f = α • v + β • e + γ • (a *ᵥ f) := h1
      _ = α • v + β • e + γ • (α • e + (β * d) • v + (γ * d) • f) := by rw [h2]
  have h3' : f = (α • v + β • e + (γ * α) • e + (γ * β * d) • v) + (γ * γ * d) • f := by
    conv_lhs => rw [h3]
    simp only [smul_add, smul_smul, mul_assoc]
    abel
  have h4 : f - (γ * γ * d) • f =
      α • v + β • e + (γ * α) • e + (γ * β * d) • v :=
    sub_eq_iff_eq_add.mpr h3'
  have hmain : (γ * γ * d - 1) • f = -((α + γ * β * d) • v) - ((β + γ * α) • e) := by
    have h5 : (γ * γ * d - 1) • f = -(f - (γ * γ * d) • f) := by
      rw [sub_smul, one_smul]
      abel
    rw [h5, h4, add_smul, add_smul]
    abel
  have hmem' : (γ * γ * d - 1) • f ∈ Submodule.span K ({v, e} : Set (Fin r ⊕ Fin r → K)) := by
    rw [hmain]
    exact Submodule.sub_mem _
      (Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hγd : γ * γ * d - 1 = 0 := by
    by_contra hs
    apply hf
    have h6 := Submodule.smul_mem (Submodule.span K ({v, e} : Set (Fin r ⊕ Fin r → K)))
      ((γ * γ * d - 1)⁻¹) hmem'
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h6
    exact h6
  apply hdsq
  have h7 : γ * γ * d = 1 := sub_eq_zero.mp hγd
  have h9 : d = (γ * γ)⁻¹ := by
    calc d = ((γ * γ)⁻¹ * (γ * γ)) * d := by
          rw [inv_mul_cancel₀ (mul_ne_zero hγ hγ), one_mul]
      _ = (γ * γ)⁻¹ * ((γ * γ) * d) := by rw [mul_assoc]
      _ = (γ * γ)⁻¹ := by rw [h7, mul_one]
  exact ⟨γ⁻¹, by rw [h9, ← _root_.mul_inv_rev]⟩

private lemma spForm_mulVec_self_eq_zero {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hself : ∀ y z, spForm (a *ᵥ y) z = spForm y (a *ᵥ z)) (h2 : (2 : K) ≠ 0)
    (y : Fin r ⊕ Fin r → K) : spForm (a *ᵥ y) y = 0 := by
  have h3 : spForm (a *ᵥ y) y = -spForm (a *ᵥ y) y := by
    calc spForm (a *ᵥ y) y = spForm y (a *ᵥ y) := hself y y
      _ = -spForm (a *ᵥ y) y := spForm_swap (a *ᵥ y) y
  have h4 : (2 : K) * spForm (a *ᵥ y) y = 0 := by
    rw [two_mul, (eq_neg_iff_add_eq_zero).mp h3]
  exact (mul_eq_zero.mp h4).resolve_left h2

theorem exists_heis_inv_ext (hr : 3 ≤ r) (h2 : (2 : K) ≠ 0) (A : GL (Fin r ⊕ Fin r) K) {d : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = d • formJ r K)
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A = d • 1) (hdsq : ¬ IsSquare d) :
    ∃ N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
      N₁ᵀ * formJ r K + formJ r K * N₁ = 0 ∧ N₂ᵀ * formJ r K + formJ r K * N₂ = 0 ∧
      N₁ * N₁ = 0 ∧ N₂ * N₂ = 0 ∧ N₁ * N₂ * N₁ = 0 ∧ N₂ * N₁ * N₂ = 0 ∧ N₁ * N₂ ≠ 0 ∧
      N₁ * N₂ ≠ N₂ * N₁ ∧
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N₁ *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -N₁ := by
  classical
  let a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have haA : aᵀ * formJ r K * a = d • formJ r K := hA
  have had : a * a = d • 1 := hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdsq ⟨0, by simp⟩
  have hself : ∀ y z, spForm (a *ᵥ y) z = spForm y (a *ᵥ z) :=
    spForm_self_adjoint haA had hd0
  have himg : ∀ y, spForm (a *ᵥ y) y = 0 := spForm_mulVec_self_eq_zero hself h2
  obtain ⟨v, hv⟩ : ∃ v : Fin r ⊕ Fin r → K, v ≠ 0 := by
    refine ⟨Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K), ?_⟩
    intro h
    have h1 := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp at h1
  obtain ⟨e, hav, hae⟩ : ∃ e : Fin r ⊕ Fin r → K, a *ᵥ v = e ∧ a *ᵥ e = d • v :=
    ⟨a *ᵥ v, rfl, mulVec_mulVec_eq had v⟩
  have he : e ≠ 0 := by
    rw [← hav]
    exact mulVec_ne_zero had hd0 hv
  have hve0 : spForm v e = 0 := by
    have h := himg v
    rw [hav] at h
    rw [spForm_swap, h, neg_zero]
  have hve : e ∉ Submodule.span K ({v} : Set (Fin r ⊕ Fin r → K)) := by
    have h := notMem_span_singleton_of_nonsquare had hdsq hv
    rwa [hav] at h
  have hv_notin_e : v ∉ Submodule.span K ({e} : Set (Fin r ⊕ Fin r → K)) := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_smul] at hc
      exact hv hc.symm
    · apply hve
      rw [Submodule.mem_span_singleton]
      refine ⟨c⁻¹, ?_⟩
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨y₁, hy₁, hy₁v⟩ := exists_spForm_sep (S := {e}) (c := v) hv_notin_e
  obtain ⟨y₂, hy₂, hy₂e⟩ := exists_spForm_sep (S := {v}) (c := e) hve
  have hy₁e : spForm e y₁ = 0 := hy₁ e (by simp)
  have hy₂v : spForm v y₂ = 0 := hy₂ v (by simp)
  obtain ⟨u, hu⟩ : ∃ u, u ∉ Submodule.span K ({v, e, y₁, y₂} : Set (Fin r ⊕ Fin r → K)) := by
    obtain ⟨u, -, hu⟩ :=
      (SetLike.lt_iff_le_and_exists.mp (span_four_lt_top hr v e y₁ y₂)).2
    exact ⟨u, hu⟩
  obtain ⟨f, hfW, hvf, hef⟩ : ∃ f : Fin r ⊕ Fin r → K,
      f ∉ Submodule.span K ({v, e} : Set (Fin r ⊕ Fin r → K)) ∧
        spForm v f = 0 ∧ spForm e f = 0 := by
    refine ⟨u - spForm v u • y₁ - spForm e u • y₂, ?_, ?_, ?_⟩
    · intro hfmem
      apply hu
      have hsub : Submodule.span K ({v, e} : Set (Fin r ⊕ Fin r → K)) ≤
          Submodule.span K ({v, e, y₁, y₂} : Set (Fin r ⊕ Fin r → K)) :=
        Submodule.span_mono (by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          tauto)
      have hy₁m : y₁ ∈ Submodule.span K ({v, e, y₁, y₂} : Set (Fin r ⊕ Fin r → K)) :=
        Submodule.subset_span (by simp)
      have hy₂m : y₂ ∈ Submodule.span K ({v, e, y₁, y₂} : Set (Fin r ⊕ Fin r → K)) :=
        Submodule.subset_span (by simp)
      have hfeq : u = (u - spForm v u • y₁ - spForm e u • y₂) + spForm v u • y₁ +
          spForm e u • y₂ := by abel
      rw [hfeq]
      exact Submodule.add_mem _
        (Submodule.add_mem _ (hsub hfmem) (Submodule.smul_mem _ _ hy₁m))
        (Submodule.smul_mem _ _ hy₂m)
    · rw [spForm_sub_right, spForm_sub_right, spForm_smul_right, spForm_smul_right,
        hy₁v, hy₂v]
      ring
    · rw [spForm_sub_right, spForm_sub_right, spForm_smul_right, spForm_smul_right,
        hy₁e, hy₂e]
      ring
  let g : Fin r ⊕ Fin r → K := a *ᵥ f
  have hfg : f ∉ Submodule.span K ({v, e, a *ᵥ f} : Set (Fin r ⊕ Fin r → K)) :=
    notMem_span_image had hdsq hav hae hfW
  obtain ⟨w, hw, hwf⟩ := exists_spForm_sep (S := {v, e, a *ᵥ f}) (c := f) hfg
  have hvw : spForm v w = 0 := hw v (by simp)
  have hew : spForm e w = 0 := hw e (by simp)
  have hgw : spForm (a *ᵥ f) w = 0 := hw (a *ᵥ f) (by simp)
  have hfe : spForm f e = 0 := by rw [spForm_swap, hef, neg_zero]
  have hev : spForm e v = 0 := by rw [spForm_swap, hve0, neg_zero]
  have hfv : spForm f v = 0 := by rw [spForm_swap, hvf, neg_zero]
  have hfg0 : spForm f (a *ᵥ f) = 0 := by rw [spForm_swap, himg f, neg_zero]
  have hgf0 : spForm (a *ᵥ f) f = 0 := himg f
  have hvg : spForm v (a *ᵥ f) = 0 := by
    have h := (hself v f).symm
    rw [hav] at h
    rw [h, hef]
  have heg : spForm e (a *ᵥ f) = 0 := by
    have h := spForm_mulVec haA v f
    rw [hav, hvf, mul_zero] at h
    exact h
  have hge : spForm (a *ᵥ f) e = 0 := by rw [spForm_swap, heg, neg_zero]
  have hvv : spForm v v = 0 := spForm_self v
  have hgg : spForm (a *ᵥ f) (a *ᵥ f) = 0 := spForm_self (a *ᵥ f)
  have hgv : spForm (a *ᵥ f) v = 0 := by
    have h := hself f v
    rw [hav] at h
    rw [h, hfe]
  have hwg : spForm w (a *ᵥ f) = 0 := by rw [spForm_swap, hgw, neg_zero]
  have hwe : spForm w e = 0 := by rw [spForm_swap, hew, neg_zero]
  have hwv : spForm w v = 0 := by rw [spForm_swap, hvw, neg_zero]
  have hww : spForm w w = 0 := spForm_self w
  have hwf1 : spForm f w = 1 := hwf
  let N₁ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := spN e f - spN v g
  let N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := spN w g
  have hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0 :=
    isSp_sub (isSp_spN e f) (isSp_spN v g)
  have hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0 := isSp_spN w g
  have hN1sq : N₁ * N₁ = 0 := by
    simp only [N₁, g, Matrix.sub_mul, Matrix.mul_sub, spN_mul_spN]
    simp [hef, hfe, hve0, hev, hfv, hvf, hgf0, hfg0, heg, hge, hvg, hgv, spForm_self]
  have hN2sq : N₂ * N₂ = 0 := by
    simp only [N₂, g, spN_mul_spN]
    simp [hwg, hgg, hgw, spForm_self]
  have hwf' : spForm w f = -1 := by rw [spForm_swap, hwf1]
  have hN12 : N₁ * N₂ = -spT g e := by
    simp only [N₁, N₂, g, Matrix.sub_mul, spN_mul_spN]
    simp [hwf', hgf0, hwe, hge, hwg, hgg, hwv, hgv]
  have hN21 : N₂ * N₁ = spT e g := by
    simp only [N₁, N₂, g, Matrix.mul_sub, spN_mul_spN]
    simp [heg, hfg0, hew, hwf1, hvg, hgg, hvw, hgw]
  have hN121 : N₁ * N₂ * N₁ = 0 := by
    rw [hN12, Matrix.neg_mul, neg_eq_zero]
    simp only [N₁, g, Matrix.mul_sub, spN, Matrix.mul_add, spT_mul_spT]
    simp [heg, hfg0, hvg, hgg]
  have hN212 : N₂ * N₁ * N₂ = 0 := by
    rw [Matrix.mul_assoc, hN12, Matrix.mul_neg, neg_eq_zero]
    simp only [N₂, g, spN, Matrix.add_mul, spT_mul_spT]
    simp [heg, hew]
  have hf0 : f ≠ 0 := by
    intro h0
    exact hfW (h0 ▸ Submodule.zero_mem _)
  have hfg0' : a *ᵥ f ∉ Submodule.span K ({e} : Set (Fin r ⊕ Fin r → K)) := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    apply hfW
    have h2' : a *ᵥ (f - c • v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hav]
      rw [show a *ᵥ f = c • e from hc.symm, sub_self]
    have h3' : f - c • v = 0 := by
      by_contra hne
      exact mulVec_ne_zero had hd0 hne h2'
    have h4' : f = c • v := sub_eq_zero.mp h3'
    rw [h4']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨y₀, hy₀, hy₀g⟩ := exists_spForm_sep (S := {e}) (c := a *ᵥ f) hfg0'
  have hye : spForm (-y₀) e = 0 := by
    rw [spForm_neg_left, spForm_swap, hy₀ e (by simp), neg_zero, neg_zero]
  have hyg : spForm (-y₀) (a *ᵥ f) = 1 := by
    rw [spForm_neg_left, spForm_swap, hy₀g, neg_neg]
  have hspT : spT (a *ᵥ f) e ≠ 0 := by
    intro h0
    have h1 : spT (a *ᵥ f) e *ᵥ (-y₀) = 0 := by rw [h0, Matrix.zero_mulVec]
    rw [spT_mulVec, hyg] at h1
    exact he (by simpa using h1)
  have hN12ne : N₁ * N₂ ≠ 0 := by
    rw [hN12]
    intro h0
    exact hspT (neg_eq_zero.mp h0)
  have hN12ne' : N₁ * N₂ ≠ N₂ * N₁ := by
    rw [hN12, hN21]
    intro h0
    have h1 : (-spT g e - spT e g) *ᵥ (-y₀) = 0 := by
      rw [h0, sub_self, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec, Matrix.neg_mulVec, spT_mulVec, spT_mulVec, hyg, hye, one_smul,
      zero_smul, sub_zero] at h1
    exact he (neg_eq_zero.mp h1)
  have hconj : a * N₁ *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -N₁ := by
    have h1 : a * spN e f *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        d⁻¹ • spN (a *ᵥ e) (a *ᵥ f) := conj_spN A haA e f
    have h2 : a * spN v g *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        d⁻¹ • spN (a *ᵥ v) (a *ᵥ g) := conj_spN A haA v g
    rw [hae] at h1
    rw [hav, show a *ᵥ g = d • f from mulVec_mulVec_eq had f] at h2
    have hsub : a * N₁ *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        a * spN e f * ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) -
        a * spN v g * ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      simp only [N₁, Matrix.mul_sub, Matrix.sub_mul]
    rw [hsub, h1, h2, spN_smul_left, spN_smul_right]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul, one_smul]
    simp only [N₁]
    abel
  exact ⟨N₁, N₂, hs₁, hs₂, hN1sq, hN2sq, hN121, hN212, hN12ne, hN12ne', hconj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
