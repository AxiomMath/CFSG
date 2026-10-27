module

public import CFSG.ClassicalGroups.Alternating.PointRadicalCount
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Alternating.PointRadicalCard
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating CFSG.Open
open scoped Matrix

theorem exists_siegel_LspGL {m : ℕ} {K : Type} [Field K] (u w : Fin m ⊕ Fin m → K)
    (huw : spForm m K u w = 0) (c : K) :
    ∃ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        x + spForm m K x u • w + spForm m K x w • u + (c * spForm m K x u) • u := by
  set g := Ssp (spForm_isAlt (m := m) (K := K)) u w c with hg
  set A : StatedSp m K := (spEquiv (m := m) (K := K)).symm g with hA
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), mem_LspGL_iff.mpr ⟨A.2, ?_⟩, fun x => ?_⟩
  · have : spEquiv (m := m) (K := K) ⟨(A : GL (Fin m ⊕ Fin m) K), A.2⟩ = g := by
      show spEquiv (m := m) (K := K) A = g
      rw [hA, MulEquiv.apply_symm_apply]
    rw [this]
    exact Ssp_mem_Lsp _ huw _
  · have h1 := spEquiv_app A x
    rw [hA, MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact siegel_apply spForm_isAlt huw c x

theorem card_addSubgroup_le_of_totallyIsotropic_finrank {m : ℕ} {K : Type} [Field K]
    (S : Submodule K (Fin m ⊕ Fin m → K)) (hS : S ≤ (spForm m K).orthogonal S) :
    Module.finrank K S ≤ m := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal (spForm_nondegenerate (m := m) (K := K)) S
  have h2 : Module.finrank K S ≤ Module.finrank K ((spForm m K).orthogonal S) :=
    Submodule.finrank_mono hS
  have h3 : Module.finrank K S ≤ Module.finrank K (Fin m ⊕ Fin m → K) :=
    Submodule.finrank_le S
  have h4 : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := finrank_spSpace
  omega

theorem card_addSubgroup_le_of_totallyIsotropic {m : ℕ} {K : Type} [Field K] [Finite K]
    (T : AddSubgroup (Fin m ⊕ Fin m → K)) (hT : ∀ x ∈ T, ∀ y ∈ T, spForm m K x y = 0) :
    Nat.card T ≤ Nat.card K ^ m := by
  obtain ⟨S, hSdef⟩ : ∃ S : Submodule K (Fin m ⊕ Fin m → K),
      S = Submodule.span K (T : Set (Fin m ⊕ Fin m → K)) := ⟨_, rfl⟩
  have hTsub : ∀ x ∈ T, x ∈ S := by
    intro x hx
    rw [hSdef]
    exact Submodule.subset_span (SetLike.mem_coe.mpr hx)
  have hTS : ∀ x ∈ T, x ∈ (spForm m K).orthogonal S := by
    intro x hx
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
    have hle : S ≤ LinearMap.ker ((spForm m K).flip x) := by
      rw [hSdef]
      refine Submodule.span_le.mpr fun t ht => ?_
      exact LinearMap.mem_ker.mpr (hT t ht x hx)
    exact LinearMap.mem_ker.mp (hle hn)
  have hSle : S ≤ (spForm m K).orthogonal S := by
    subst hSdef
    exact Submodule.span_le.mpr fun x hx => hTS x hx
  have hdim : Module.finrank K S ≤ m := card_addSubgroup_le_of_totallyIsotropic_finrank S hSle
  have hTS' : Nat.card T ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun x : T => (⟨(x : Fin m ⊕ Fin m → K), hTsub (x : Fin m ⊕ Fin m → K) x.2⟩ : S)) ?_
    intro x y hxy
    have hv := congrArg (fun z : S => (z : Fin m ⊕ Fin m → K)) hxy
    exact Subtype.ext hv
  have hSc : Nat.card S = Nat.card K ^ Module.finrank K S := Module.natCard_eq_pow_finrank
  have hK : 0 < Nat.card K := Nat.card_pos
  have hpow : Nat.card K ^ Module.finrank K S ≤ Nat.card K ^ m := Nat.pow_le_pow_right hK hdim
  calc Nat.card T ≤ Nat.card S := hTS'
    _ = Nat.card K ^ Module.finrank K S := hSc
    _ ≤ Nat.card K ^ m := hpow

theorem card_le_of_forall_isotropic_LspGL {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (hm : 2 ≤ m)
    (P : Subgroup (GL (Fin m ⊕ Fin m) K)) (hP : P ≤ LspGL m K u)
    (hno : ∀ A ∈ P, ∀ y : Fin m ⊕ Fin m → K,
      spForm m K y ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = 0) :
    Nat.card P ≤ Nat.card K ^ (m - 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨f, hf⟩ : ∃ f : GL (Fin m ⊕ Fin m) K →*
      LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K),
      f = Matrix.GeneralLinearGroup.toLin.toMonoidHom := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by
    subst hf
    exact Matrix.GeneralLinearGroup.toLin.injective
  have hact : ∀ (A : GL (Fin m ⊕ Fin m) K) (x : Fin m ⊕ Fin m → K),
      ((f A : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) x =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x := by
    subst hf
    intro A x
    rfl
  have hcard : Nat.card (P.map f) = Nat.card P := Subgroup.card_map_of_injective hfinj
  have hP' : P.map f ≤ pointRadical (spForm m K) spForm_isAlt u := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨-, w, c, hw, hM⟩ := mem_LspGL_iff_siegel.mp (hP hA)
    refine mem_pointRadical.mpr ⟨w, c, hw, Units.ext (LinearMap.ext fun x => ?_)⟩
    rw [siegel_apply spForm_isAlt hw c x, hact]
    exact (hM x).symm
  have hno' : ∀ (w : Fin m ⊕ Fin m → K) (c : K), spForm m K u w = 0 →
      siegel (spForm m K) spForm_isAlt u w c ∈ P.map f → c = 0 ∨ ∃ s : K, w = s • u := by
    intro w c hw hmem
    left
    obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp hmem
    have hy : ∀ y : Fin m ⊕ Fin m → K, spForm m K y
        ((siegel (spForm m K) spForm_isAlt u w c :
          (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) y) = 0 := by
      intro y
      rw [← hAeq, hact]
      exact hno A hA y
    exact (forall_form_apply_siegel_eq_zero_iff h2 spForm_isAlt spForm_nondegenerate hu hw c).mp hy
  have key := card_le_of_no_c2 spForm_isAlt spForm_nondegenerate hu hm finrank_spSpace (P.map f)
    hP' hno'
  rw [hcard] at key
  exact key

theorem LspGL_invariant_subspace_dichotomy {m : ℕ} {K : Type} [Field K]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (D : Submodule K (Fin m ⊕ Fin m → K)) (huD : u ∈ D)
    (hinv : ∀ A ∈ LspGL m K u, ∀ d ∈ D,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ d ∈ D) :
    (∀ d ∈ D, spForm m K u d = 0) ∨ D = ⊤ := by
  by_cases h : ∀ d ∈ D, spForm m K u d = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨d, hdD, hud⟩ := h
  have halt : (spForm m K).IsAlt := spForm_isAlt
  have ha : spForm m K d u ≠ 0 := by
    rw [← halt.neg_eq u d]
    exact neg_ne_zero.mpr hud
  have hperp : ∀ w : Fin m ⊕ Fin m → K, spForm m K u w = 0 → w ∈ D := by
    intro w huw
    obtain ⟨A, hA, hAx⟩ := exists_siegel_LspGL u w huw 0
    have h1 : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ d ∈ D := hinv A hA d hdD
    have heq : spForm m K d u • w =
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ d - d) - spForm m K d w • u := by
      rw [hAx d]
      simp only [zero_mul, zero_smul, add_zero]
      abel
    have h2 : spForm m K d u • w ∈ D := by
      rw [heq]
      exact D.sub_mem (D.sub_mem h1 hdD) (D.smul_mem _ huD)
    have h3 := D.smul_mem (spForm m K d u)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3
  rw [eq_top_iff]
  intro x _
  obtain ⟨c, hc⟩ : ∃ c : K, c * spForm m K d u = spForm m K x u :=
    ⟨spForm m K x u / spForm m K d u, div_mul_cancel₀ _ ha⟩
  have hyu : spForm m K (x - c • d) u = 0 := by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hc, sub_self]
  have hy : spForm m K u (x - c • d) = 0 := by
    have h := halt.neg_eq u (x - c • d)
    rw [hyu, neg_eq_zero] at h
    exact h
  have hxy : x - c • d + c • d ∈ D := D.add_mem (hperp _ hy) (D.smul_mem c hdD)
  rwa [sub_add_cancel] at hxy

theorem card_le_of_comm_mem_LspGL {m : ℕ} {K : Type} [Field K] [Finite K]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (D : AddSubgroup (Fin m ⊕ Fin m → K))
    (hD : ∀ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x ∈ D) :
    Nat.card K ^ (2 * m - 1) ≤ Nat.card D := by
  obtain ⟨y, hy⟩ : ∃ y : Fin m ⊕ Fin m → K, spForm m K y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu ((spForm_nondegenerate (m := m) (K := K)).2 u hcon)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin m ⊕ Fin m → K, spForm m K y₀ u = 1 := by
    refine ⟨(spForm m K y u)⁻¹ • y, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy]
  have hcu : ∀ c : K, c • u ∈ D := by
    intro c
    obtain ⟨A, hA, hAx⟩ := exists_siegel_LspGL u 0 (map_zero _) c
    have h1 : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y₀ - y₀ = c • u := by
      rw [hAx y₀, hy₀, map_zero]
      simp
    have h := hD A hA y₀
    rwa [h1] at h
  have hker : ∀ w : Fin m ⊕ Fin m → K, spForm m K u w = 0 → w ∈ D := by
    intro w hw
    obtain ⟨A, hA, hAx⟩ := exists_siegel_LspGL u w hw 0
    have h1 : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y₀ - y₀ =
        w + spForm m K y₀ w • u := by
      rw [hAx y₀, hy₀]
      simp only [one_smul, zero_mul, zero_smul, add_zero]
      abel
    have h2 := D.sub_mem (hD A hA y₀) (hcu (spForm m K y₀ w))
    rw [h1] at h2
    simpa using h2
  have hu_y₀ : spForm m K u y₀ = -1 := by
    have h := spForm_isAlt.neg_eq u y₀
    rw [hy₀] at h
    exact neg_eq_iff_eq_neg.mp h
  have hsurj : Function.Surjective (spForm m K u) := by
    intro t
    refine ⟨t • -y₀, ?_⟩
    rw [map_smul, map_neg, hu_y₀, smul_eq_mul, neg_neg, mul_one]
  have hrank : Module.finrank K (LinearMap.range (spForm m K u)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hsum := LinearMap.finrank_range_add_finrank_ker (spForm m K u)
  rw [hrank, finrank_spSpace] at hsum
  have hfin : Module.finrank K (LinearMap.ker (spForm m K u)) = 2 * m - 1 := by
    omega
  have hcard : Nat.card (LinearMap.ker (spForm m K u)) = Nat.card K ^ (2 * m - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (spForm m K u)), hfin]
  have hle : Nat.card (LinearMap.ker (spForm m K u)) ≤ Nat.card D := by
    refine Nat.card_le_card_of_injective
      (fun w => (⟨(w : Fin m ⊕ Fin m → K), hker w.1 (LinearMap.mem_ker.mp w.2)⟩ : D)) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext h
  exact hcard.symm.le.trans hle

theorem card_le_card_of_LspGL_move {m : ℕ} {K : Type} [Field K] [Finite K]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (D : Submodule K (Fin m ⊕ Fin m → K)) (huD : u ∈ D)
    (hDu : ∀ d ∈ D, spForm m K u d = 0) (S : Subgroup (GL (Fin m ⊕ Fin m) K))
    (hS : ∀ A, A ∈ S ↔ A ∈ LspGL m K u ∧ ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x ∈ D) :
    Nat.card D ≤ Nat.card S := by
  obtain ⟨y, hy⟩ : ∃ y : Fin m ⊕ Fin m → K, spForm m K y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu ((spForm_nondegenerate (m := m) (K := K)).2 u hcon)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin m ⊕ Fin m → K, spForm m K y₀ u = 1 :=
    ⟨(spForm m K y u)⁻¹ • y, by rw [LinearMap.BilinForm.smul_left, inv_mul_cancel₀ hy]⟩
  have hex : ∀ d : D, ∃ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        x + spForm m K x u • d.1 + spForm m K x d.1 • u +
          (-(spForm m K y₀ d.1) * spForm m K x u) • u :=
    fun d => exists_siegel_LspGL u d.1 (hDu d.1 d.2) (-(spForm m K y₀ d.1))
  choose f hfL hf using hex
  have hfy : ∀ d : D, (f d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y₀ = y₀ + d.1 := by
    intro d
    rw [hf d y₀, hy₀, one_smul, mul_one, neg_smul]
    abel
  have hmem : ∀ d : D, ∀ x : Fin m ⊕ Fin m → K,
      (f d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x ∈ D := by
    intro d x
    have h : (f d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x =
        spForm m K x u • d.1 +
          (spForm m K x d.1 + -(spForm m K y₀ d.1) * spForm m K x u) • u := by
      rw [hf d x]
      module
    rw [h]
    exact D.add_mem (D.smul_mem _ d.2) (D.smul_mem _ huD)
  have hSmem : ∀ d : D, f d ∈ S := fun d => (hS (f d)).2 ⟨hfL d, hmem d⟩
  have hfinj : Function.Injective f := by
    intro d₁ d₂ h
    apply Subtype.ext
    have h3 : (f d₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y₀ =
        (f d₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y₀ := by
      rw [h]
    exact add_left_cancel ((hfy d₁).symm.trans (h3.trans (hfy d₂)))
  have hinj : Function.Injective (fun d : D => (⟨f d, hSmem d⟩ : S)) := by
    intro d₁ d₂ h
    have h' : f d₁ = f d₂ := congrArg Subtype.val h
    exact hfinj h'
  exact Nat.card_le_card_of_injective _ hinj

section Invol

open Module

theorem sec8_invol_quotient {K E : Type} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (T : E →ₗ[K] E) (hT2 : ∀ e, T (T e) = e)
    (A₀ A : Submodule K E) (hle : A₀ ≤ A) (hdim : finrank K A = finrank K A₀ + 1)
    (hA : ∀ a ∈ A, T a ∈ A) (hA₀ : ∀ a ∈ A₀, T a ∈ A₀) :
    ∀ a ∈ A, T a - a ∈ A₀ := by
  have hne : A₀ ≠ A := by
    intro h
    rw [h] at hdim
    omega
  have hex : ∃ w ∈ A, w ∉ A₀ := by
    by_contra hcon
    apply hne
    apply le_antisymm hle
    intro x hx
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨w, hwA, hw⟩ := hex
  have hw0 : w ≠ 0 := by
    intro h
    apply hw
    rw [h]
    exact A₀.zero_mem
  have hle' : A₀ ⊔ Submodule.span K {w} ≤ A :=
    sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hwA)
  have hinf : A₀ ⊓ Submodule.span K {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA₀, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · exfalso
      apply hw
      have h' := A₀.smul_mem c⁻¹ hxA₀
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq A₀ (Submodule.span K {w})
  rw [hinf, finrank_bot, finrank_span_singleton hw0] at hfin
  have hsup : A₀ ⊔ Submodule.span K {w} = A :=
    Submodule.eq_of_le_of_finrank_eq hle' (by omega)
  have hTw : T w ∈ A₀ ⊔ Submodule.span K {w} := by
    rw [hsup]
    exact hA w hwA
  obtain ⟨a₀, ha₀, z, hz, hsum⟩ := Submodule.mem_sup.mp hTw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hcalc : w = T a₀ + c • a₀ + (c * c) • w := by
    calc w = T (T w) := (hT2 w).symm
      _ = T (a₀ + c • w) := by rw [hsum]
      _ = T a₀ + c • T w := by rw [map_add, map_smul]
      _ = T a₀ + c • (a₀ + c • w) := by rw [← hsum]
      _ = T a₀ + c • a₀ + (c * c) • w := by rw [smul_add, smul_smul]; abel
  have hkey : (1 - c * c) • w = T a₀ + c • a₀ := by
    linear_combination (norm := module) hcalc
  have hmem : (1 - c * c) • w ∈ A₀ := by
    rw [hkey]
    exact A₀.add_mem (hA₀ a₀ ha₀) (A₀.smul_mem c ha₀)
  have hcc : 1 - c * c = 0 := by
    by_contra hne0
    apply hw
    have h' := A₀.smul_mem (1 - c * c)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne0, one_smul] at h'
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c - 1) * (c - 1) = 0 := by
    linear_combination (-1 : K) * hcc + (-(c - 1)) * h2
  have hc1 : c = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  have hTa : T w - w = a₀ := by
    rw [← hsum, hc1, one_smul]
    abel
  intro v hv
  rw [← hsup] at hv
  obtain ⟨a₁, ha₁, z, hz, hsum2⟩ := Submodule.mem_sup.mp hv
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
  subst hsum2
  have hcomp : T (a₁ + r • w) - (a₁ + r • w) = (T a₁ - a₁) + r • (T w - w) := by
    rw [map_add, map_smul, smul_sub]
    abel
  rw [hcomp, hTa]
  exact A₀.add_mem (A₀.sub_mem (hA₀ a₁ ha₁) ha₁) (A₀.smul_mem r ha₀)

end Invol

end CFSG.RankThree.GF2n.Stroth80
