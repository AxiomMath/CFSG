module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Quasithin.H13.CTK

open Module

universe u

variable {K : Type*} [Field K]

theorem card_le_two_pow_finrank (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ S : Finset (End K V), (∀ f ∈ S, f * f = 1) → (∀ f ∈ S, ∀ g ∈ S, f * g = g * f) →
      S.card ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn S hS1 hS2
  classical
  by_cases hscal : ∀ f ∈ S, f = 1 ∨ f = -1
  · have hsub : S ⊆ {1, -1} := fun f hf => by simpa using hscal f hf
    have hc2 : S.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rcases n with _ | n
    · have : Subsingleton V := Module.finrank_zero_iff.1 hn
      exact (Finset.card_le_one_of_subsingleton S).trans (by norm_num)
    · exact hc2.trans (by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  · push Not at hscal
    obtain ⟨g, hgS, hg1, hg2⟩ := hscal
    have hgg : g * g = 1 := hS1 g hgS
    have hgg' : ∀ v, g (g v) = v := fun v => by
      have := congrArg (fun T : End K V => T v) hgg
      simpa using this
    set Wp : Submodule K V := LinearMap.ker (g - 1) with hWp
    set Wm : Submodule K V := LinearMap.ker (g + 1) with hWm
    have hWp_mem : ∀ v, v ∈ Wp ↔ g v = v := fun v => by
      simp [hWp, sub_eq_zero]
    have hWm_mem : ∀ v, v ∈ Wm ↔ g v = -v := fun v => by
      simp [hWm, add_eq_zero_iff_eq_neg]
    have hcompl : IsCompl Wp Wm := by
      constructor
      · rw [Submodule.disjoint_def]
        intro v hv1 hv2
        rw [hWp_mem] at hv1
        rw [hWm_mem] at hv2
        have hvv : v = -v := hv1.symm.trans hv2
        have h2v : (2 : K) • v = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hvv]
          simp
        exact (smul_eq_zero.1 h2v).resolve_left h2
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        have hp : (2⁻¹ : K) • (v + g v) ∈ Wp := by
          refine Submodule.smul_mem _ _ ((hWp_mem _).2 ?_)
          rw [map_add, hgg', add_comm]
        have hm : (2⁻¹ : K) • (v - g v) ∈ Wm := by
          refine Submodule.smul_mem _ _ ((hWm_mem _).2 ?_)
          rw [map_sub, hgg', neg_sub]
        have e : v = (2⁻¹ : K) • (v + g v) + (2⁻¹ : K) • (v - g v) := by
          rw [← smul_add]
          have : v + g v + (v - g v) = (2 : K) • v := by
            rw [two_smul]
            abel
          rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
        rw [e]
        exact Submodule.add_mem_sup hp hm
    have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
    have hWp_ne : Wp ≠ ⊥ := by
      intro hbot
      have htop : Wm = ⊤ := by
        have := hcompl.sup_eq_top
        rwa [hbot, bot_sup_eq] at this
      have : g + 1 = 0 := LinearMap.ker_eq_top.1 htop
      exact hg2 (eq_neg_of_add_eq_zero_left this)
    have hWm_ne : Wm ≠ ⊥ := by
      intro hbot
      have htop : Wp = ⊤ := by
        have := hcompl.sup_eq_top
        rwa [hbot, sup_bot_eq] at this
      have : g - 1 = 0 := LinearMap.ker_eq_top.1 htop
      exact hg1 (sub_eq_zero.1 this)
    have hp1 : 1 ≤ finrank K Wp := Submodule.one_le_finrank_iff.2 hWp_ne
    have hm1 : 1 ≤ finrank K Wm := Submodule.one_le_finrank_iff.2 hWm_ne
    have hpresP : ∀ f ∈ S, ∀ v ∈ Wp, f v ∈ Wp := by
      intro f hf v hv
      rw [hWp_mem] at hv ⊢
      have := congrArg (fun T : End K V => T v) (hS2 g hgS f hf)
      simp only [Module.End.mul_apply] at this
      rw [this, hv]
    have hpresM : ∀ f ∈ S, ∀ v ∈ Wm, f v ∈ Wm := by
      intro f hf v hv
      rw [hWm_mem] at hv ⊢
      have := congrArg (fun T : End K V => T v) (hS2 g hgS f hf)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_neg]
    let rP : End K V → End K Wp := fun f =>
      if h : ∀ v ∈ Wp, f v ∈ Wp then f.restrict h else 0
    let rM : End K V → End K Wm := fun f =>
      if h : ∀ v ∈ Wm, f v ∈ Wm then f.restrict h else 0
    have rP_apply : ∀ f ∈ S, ∀ v : Wp, ((rP f v : Wp) : V) = f v := by
      intro f hf v
      simp only [rP]
      rw [dite_eq_left_of_eq_true (eq_true (hpresP f hf))]
      rfl
    have rM_apply : ∀ f ∈ S, ∀ v : Wm, ((rM f v : Wm) : V) = f v := by
      intro f hf v
      simp only [rM]
      rw [dite_eq_left_of_eq_true (eq_true (hpresM f hf))]
      rfl
    have hrP1 : ∀ f ∈ S, rP f * rP f = 1 := by
      intro f hf
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have h1 := rP_apply f hf (rP f v)
      have h2 := rP_apply f hf v
      have h3 := congrArg (fun T : End K V => T v) (hS1 f hf)
      simp only [Module.End.mul_apply, Module.End.one_apply] at h3 ⊢
      rw [h1, h2, h3]
    have hrM1 : ∀ f ∈ S, rM f * rM f = 1 := by
      intro f hf
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have h1 := rM_apply f hf (rM f v)
      have h2 := rM_apply f hf v
      have h3 := congrArg (fun T : End K V => T v) (hS1 f hf)
      simp only [Module.End.mul_apply, Module.End.one_apply] at h3 ⊢
      rw [h1, h2, h3]
    have hrPc : ∀ f ∈ S, ∀ f' ∈ S, rP f * rP f' = rP f' * rP f := by
      intro f hf f' hf'
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have h1 := rP_apply f hf (rP f' v)
      have h2 := rP_apply f' hf' v
      have h1' := rP_apply f' hf' (rP f v)
      have h2' := rP_apply f hf v
      have h3 := congrArg (fun T : End K V => T v) (hS2 f hf f' hf')
      simp only [Module.End.mul_apply] at h3 ⊢
      rw [h1, h2, h1', h2', h3]
    have hrMc : ∀ f ∈ S, ∀ f' ∈ S, rM f * rM f' = rM f' * rM f := by
      intro f hf f' hf'
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have h1 := rM_apply f hf (rM f' v)
      have h2 := rM_apply f' hf' v
      have h1' := rM_apply f' hf' (rM f v)
      have h2' := rM_apply f hf v
      have h3 := congrArg (fun T : End K V => T v) (hS2 f hf f' hf')
      simp only [Module.End.mul_apply] at h3 ⊢
      rw [h1, h2, h1', h2', h3]
    have hP : (S.image rP).card ≤ 2 ^ finrank K Wp :=
      ih (finrank K Wp) (by omega) Wp rfl (S.image rP)
        (by
          intro f' hf'
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
          exact hrP1 f hf)
        (by
          intro f' hf' g' hg'
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
          obtain ⟨g'', hg'', rfl⟩ := Finset.mem_image.1 hg'
          exact hrPc f hf g'' hg'')
    have hM : (S.image rM).card ≤ 2 ^ finrank K Wm :=
      ih (finrank K Wm) (by omega) Wm rfl (S.image rM)
        (by
          intro f' hf'
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
          exact hrM1 f hf)
        (by
          intro f' hf' g' hg'
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
          obtain ⟨g'', hg'', rfl⟩ := Finset.mem_image.1 hg'
          exact hrMc f hf g'' hg'')
    have hinj : Set.InjOn (fun f => (rP f, rM f)) (S : Set (End K V)) := by
      intro f hf f' hf' hff
      simp only [Prod.mk.injEq] at hff
      obtain ⟨h1, h2'⟩ := hff
      have hf0 := Finset.mem_coe.1 hf
      have hf0' := Finset.mem_coe.1 hf'
      apply LinearMap.ext
      intro v
      have hv : v ∈ Wp ⊔ Wm := by
        rw [hcompl.sup_eq_top]
        trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, map_add]
      congr 1
      · rw [← rP_apply f hf0 ⟨a, ha⟩, ← rP_apply f' hf0' ⟨a, ha⟩, h1]
      · rw [← rM_apply f hf0 ⟨b, hb⟩, ← rM_apply f' hf0' ⟨b, hb⟩, h2']
    have hcard : S.card ≤ (S.image rP).card * (S.image rM).card := by
      calc S.card = (S.image (fun f => (rP f, rM f))).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (S.image rP ×ˢ S.image rM).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
            exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hf, Finset.mem_image_of_mem _ hf⟩
        _ = _ := Finset.card_product _ _
    calc S.card ≤ (S.image rP).card * (S.image rM).card := hcard
      _ ≤ 2 ^ finrank K Wp * 2 ^ finrank K Wm := Nat.mul_le_mul hP hM
      _ = 2 ^ n := by rw [← pow_add, hdim, hn]

theorem card_le_two_pow_gl (h2 : (2 : K) ≠ 0) (n : ℕ) {E : Subgroup (GL (Fin n) K)} [Finite E]
    (hsq : ∀ g ∈ E, g * g = 1) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    Nat.card E ≤ 2 ^ n := by
  classical
  have := Fintype.ofFinite E
  let φ : E → Module.End K (Fin n → K) := fun g =>
    Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hφ : Function.Injective φ := by
    intro a b hab
    have := Matrix.toLin'.injective hab
    exact Subtype.ext (Units.ext this)
  have hcard : Nat.card E = (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hφ, Nat.card_eq_fintype_card, Finset.card_univ]
  rw [hcard]
  refine card_le_two_pow_finrank h2 n (Fin n → K) (Module.finrank_fin_fun K) _ ?_ ?_
  · intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hf
    show Matrix.toLin' _ * Matrix.toLin' _ = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Units.val_mul, hsq g g.2, Units.val_one,
      Matrix.toLin'_one]
    rfl
  · intro f hf f' hf'
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 hf'
    show Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      ← Units.val_mul, ← Units.val_mul, hcomm g g.2 g' g'.2]

end CFSG.Quasithin.H13.CTK
