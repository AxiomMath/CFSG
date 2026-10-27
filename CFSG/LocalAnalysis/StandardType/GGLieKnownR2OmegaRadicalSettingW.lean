module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSetting
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalIrr
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalIrrFour
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelConj
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.StandardType CFSG.StandardType.ClassicalPosition

private theorem setW_siegelW_map {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (a₁ a₂ b₁ b₂ : V) :
    siegelW Q (A a₁) (A a₂) (A b₁) (A b₂) =
      Submodule.map (A : V →ₗ[K] V) (siegelW Q a₁ a₂ b₁ b₂) := by
  have hset : Submodule.map (A : V →ₗ[K] V) (Submodule.span K ({a₁, a₂, b₁, b₂} : Set V)) =
      Submodule.span K ({A a₁, A a₂, A b₁, A b₂} : Set V) := by
    rw [Submodule.map_span]
    congr 1
    ext w; simp
  apply le_antisymm
  · intro y hy
    simp only [siegelW] at hy
    have hy' := (mem_orth_iff.mp hy)
    refine ⟨A.symm y, ?_, by simp⟩
    simp only [siegelW]
    refine mem_orth_iff.mpr fun x hx => ?_
    have hx' : A x ∈ Submodule.span K {A a₁, A a₂, A b₁, A b₂} := by
      rw [← hset]
      exact Submodule.mem_map_of_mem hx
    rw [← polar_map_of_mem hA x (A.symm y), LinearEquiv.apply_symm_apply]
    exact hy' _ hx'
  · rintro y ⟨x, hx, rfl⟩
    simp only [siegelW] at hx ⊢
    have hx' := mem_orth_iff.mp hx
    refine mem_orth_iff.mpr fun z hz => ?_
    rw [← hset, Submodule.mem_map] at hz
    obtain ⟨z', hz', hz'eq⟩ := hz
    rw [← hz'eq]
    exact (polar_map_of_mem hA z' x).trans (hx' z' hz')

private theorem setW_irreducible_of_map {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}
    (hAorth : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a₁ a₂ b₁ b₂ : V}
    (hirr : ∀ X : Submodule K V, X ≤ siegelW Q a₁ a₂ b₁ b₂ →
      (∀ g ∈ elementaryGroup Q,
        (∀ v ∈ Submodule.span K ({a₁, a₂, b₁, b₂} : Set V), g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW Q a₁ a₂ b₁ b₂) :
    ∀ X : Submodule K V, X ≤ siegelW Q (A a₁) (A a₂) (A b₁) (A b₂) →
      (∀ g ∈ elementaryGroup Q,
        (∀ v ∈ Submodule.span K ({A a₁, A a₂, A b₁, A b₂} : Set V), g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW Q (A a₁) (A a₂) (A b₁) (A b₂) := by
  intro X hXW hXinv
  let Y : Submodule K V := X.comap (A : V →ₗ[K] V)
  have hmapX : Submodule.map (A : V →ₗ[K] V) Y = X := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      refine ⟨A.symm y, ?_, by simp⟩
      change (A : V →ₗ[K] V) (A.symm y) ∈ X
      have h1 : (A : V →ₗ[K] V) (A.symm y) = y := LinearEquiv.apply_symm_apply A y
      rw [h1]
      exact hy
  have hYW : Y ≤ siegelW Q a₁ a₂ b₁ b₂ := by
    intro y hy
    have h1 : (A : V →ₗ[K] V) y ∈ siegelW Q (A a₁) (A a₂) (A b₁) (A b₂) := hXW hy
    rw [setW_siegelW_map hAorth a₁ a₂ b₁ b₂, Submodule.mem_map] at h1
    obtain ⟨w, hw, hw_eq⟩ := h1
    have : w = y := A.injective hw_eq
    rw [this] at hw
    exact hw
  have hYinv : ∀ g ∈ elementaryGroup Q,
      (∀ v ∈ Submodule.span K ({a₁, a₂, b₁, b₂} : Set V), g v = v) →
      ∀ x ∈ Y, g x ∈ Y := by
    intro g hg hgfix x hx
    have hconj : A * g * A⁻¹ ∈ elementaryGroup Q := conj_mem_elementaryGroup hAorth hg
    have hset : Submodule.map (A : V →ₗ[K] V) (Submodule.span K ({a₁, a₂, b₁, b₂} : Set V)) =
        Submodule.span K ({A a₁, A a₂, A b₁, A b₂} : Set V) := by
      rw [Submodule.map_span]
      congr 1
      ext w; simp
    have hfix : ∀ v ∈ Submodule.span K ({A a₁, A a₂, A b₁, A b₂} : Set V),
        (A * g * A⁻¹) v = v := by
      intro v hv
      rw [← hset, Submodule.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 : A⁻¹ ((A : V →ₗ[K] V) w) = w := LinearEquiv.symm_apply_apply A w
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, hgfix w hw]
      rfl
    have hxA : (A : V →ₗ[K] V) x ∈ X := hx
    have hres := hXinv _ hconj hfix _ hxA
    have heq : (A * g * A⁻¹) ((A : V →ₗ[K] V) x) = (A : V →ₗ[K] V) (g x) := by
      have h1 : A⁻¹ ((A : V →ₗ[K] V) x) = x := LinearEquiv.symm_apply_apply A x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1]
      rfl
    rw [heq] at hres
    exact hres
  rcases hirr Y hYW hYinv with hY | hY
  · left
    rw [← hmapX, hY, Submodule.map_bot]
  · right
    rw [← hmapX, hY, ← setW_siegelW_map hAorth a₁ a₂ b₁ b₂]

private theorem setW_map_conj_range_eq_siegelRoot {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N) {i j : Fin N}
    (hij : i ≠ j) (s t : Bool) (hS : SpinOmegaData Q) {H : Subgroup (spinGroup Q)}
    (hH : H = (F.longRoot hij s t).range) (u : spinGroup Q) :
    H.map (MulAut.conj u).toMonoidHom =
      siegelRoot Q (spinAction Q u (F.vec j t)) (spinAction Q u (F.vec i s)) := by
  have hf : Function.Injective (spinAction Q) :=
    (MonoidHom.ker_eq_bot_iff (spinAction Q)).mp hS.ker_eq_bot
  have hsiegel_le : siegelGroup Q (spinAction Q u (F.vec j t)) (spinAction Q u (F.vec i s)) ≤
      elementaryGroup Q := by
    rw [siegelGroup, Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact eichler_mem_elementaryGroup Q _ _
  refine Subgroup.map_injective hf ?_
  rw [hH,
    CFSG.StandardType.ClassicalPosition.Geo.map_conj_range_longRoot_eq_siegelGroup F hij s t u,
    siegelRoot, Subgroup.map_comap_eq, hS.range_eq, inf_eq_right.mpr hsiegel_le]

private theorem setW_frame_of_root {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N) {i j : Fin N} (hij : i ≠ j) (s t : Bool)
    (hS : SpinOmegaData Q) (u : spinGroup Q) {H : Subgroup (spinGroup Q)}
    (hH : H = (F.longRoot hij s t).range)
    (hirr : ∀ X : Submodule K V,
      X ≤ siegelW Q (F.vec j t) (F.vec i s) (F.vec j (!t)) (F.vec i (!s)) →
      (∀ g ∈ elementaryGroup Q,
        (∀ v ∈ Submodule.span K ({F.vec j t, F.vec i s, F.vec j (!t), F.vec i (!s)} : Set V),
          g v = v) → ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW Q (F.vec j t) (F.vec i s) (F.vec j (!t)) (F.vec i (!s))) :
    ∃ P P' : HypPair Q, P.Orth P' ∧
      H.map (MulAut.conj u).toMonoidHom = siegelRoot Q P.e P'.e ∧
      (∀ X : Submodule K V, X ≤ siegelW Q P.e P'.e P.f P'.f →
        (∀ g ∈ elementaryGroup Q,
          (∀ v ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V), g v = v) →
          ∀ x ∈ X, g x ∈ X) →
        X = ⊥ ∨ X = siegelW Q P.e P'.e P.f P'.f) := by
  have hAorth : spinAction Q u ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q u)
  refine ⟨⟨spinAction Q u (F.vec j t), spinAction Q u (F.vec j (!t)), ?_, ?_, ?_⟩,
    ⟨spinAction Q u (F.vec i s), spinAction Q u (F.vec i (!s)), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [map_spinAction]; exact F.map_vec j t
  · rw [map_spinAction]; exact F.map_vec j (!t)
  · rw [polar_spinAction]; exact F.polar_vec_not j t
  · rw [map_spinAction]; exact F.map_vec i s
  · rw [map_spinAction]; exact F.map_vec i (!s)
  · rw [polar_spinAction]; exact F.polar_vec_not i s
  · exact ⟨by rw [polar_spinAction]; exact F.polar_vec_of_ne hij.symm t s,
      by rw [polar_spinAction]; exact F.polar_vec_of_ne hij.symm t (!s),
      by rw [polar_spinAction]; exact F.polar_vec_of_ne hij.symm (!t) s,
      by rw [polar_spinAction]; exact F.polar_vec_of_ne hij.symm (!t) (!s)⟩
  · exact setW_map_conj_range_eq_siegelRoot F hij s t hS hH u
  · exact setW_irreducible_of_map (A := spinAction Q u) (a₁ := F.vec j t) (a₂ := F.vec i s)
      (b₁ := F.vec j (!t)) (b₂ := F.vec i (!s)) hAorth hirr

theorem exists_frame_hW_of_root_plus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F]
    (hS : SpinOmegaData (Spin.quadPlus n F))
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots)
    (u : ↥(spinGroup (Spin.quadPlus n F))) :
    ∃ P P' : HypPair (Spin.quadPlus n F), P.Orth P' ∧
      ((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom =
        siegelRoot (Spin.quadPlus n F) P.e P'.e ∧
      ∀ X : Submodule F (Fin n ⊕ Fin n → F),
        X ≤ siegelW (Spin.quadPlus n F) P.e P'.e P.f P'.f →
        (∀ g ∈ elementaryGroup (Spin.quadPlus n F),
          (∀ v ∈ Submodule.span F {P.e, P'.e, P.f, P'.f}, g v = v) → ∀ x ∈ X, g x ∈ X) →
        X = ⊥ ∨ X = siegelW (Spin.quadPlus n F) P.e P'.e P.f P'.f := by
  obtain ⟨i, j, hij, s, t, h, hrg⟩ :=
    exists_plusRootGroup_eq (K := F) (n := n) (by omega) hβ
  exact setW_frame_of_root (Spin.plusFrame n F (by omega)) hij s t hS u hrg
    (siegelW_irreducible_quadPlus (F := F) (by omega) hij s t)

theorem exists_frame_hW_of_root_minus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hS : SpinOmegaData (Spin.quadMinus n F b c))
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c))) :
    ∃ P P' : HypPair (Spin.quadMinus n F b c), P.Orth P' ∧
      ((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom =
        siegelRoot (Spin.quadMinus n F b c) P.e P'.e ∧
      ∀ X : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
        X ≤ siegelW (Spin.quadMinus n F b c) P.e P'.e P.f P'.f →
        (∀ g ∈ elementaryGroup (Spin.quadMinus n F b c),
          (∀ v ∈ Submodule.span F {P.e, P'.e, P.f, P'.f}, g v = v) → ∀ x ∈ X, g x ∈ X) →
        X = ⊥ ∨ X = siegelW (Spin.quadMinus n F b c) P.e P'.e P.f P'.f := by
  obtain ⟨i, j, hij, s, t, h⟩ :=
    CFSG.StandardType.RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn hl
  have hrg : (Spin.Twisted.minusDatum n hirr).rootGroup β =
      ((Spin.Twisted.minusFrame n b c).toHypFrame.longRoot hij s t).range :=
    Spin.Twisted.minusRootGroup_eq_long n hirr hij s t h
  by_cases h5 : 5 ≤ n
  · exact setW_frame_of_root (Spin.Twisted.minusFrame n b c).toHypFrame hij s t hS u hrg
      (siegelW_irreducible_quadMinus_ge_five (F := F) h5 hirr hij s t)
  · have hn4 : n = 4 := by omega
    subst n
    exact setW_frame_of_root (Spin.Twisted.minusFrame 4 b c).toHypFrame hij s t hS u hrg
      (siegelW_irreducible_quadMinus_four (F := F) hirr hij s t)

end CFSG.StandardType.LieKnownR2.POmega.Radical
