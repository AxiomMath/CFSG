module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]

theorem eq_zero_of_comm {W A C V B T : Submodule K E} (hAW : A ≤ W) (hWAC : W ≤ A ⊔ C)
    (hBT : B ⊓ T = ⊥) {ι : Type} (D : ι → E →ₗ[K] E) (hDW : ∀ i, ∀ w ∈ W, D i w ∈ A)
    (hfix : ∀ v ∈ V, (∀ i, D i v = 0) → v ∈ B) (g : ↥W →ₗ[K] E)
    (hgA : ∀ w : ↥W, (w : E) ∈ A → g w = 0) (hgC : ∀ w : ↥W, (w : E) ∈ C → g w ∈ T)
    (hgV : ∀ w : ↥W, g w ∈ V)
    (hcomm : ∀ i, ∀ w : ↥W, D i (g w) = g ⟨D i w, hAW (hDW i w w.2)⟩) : g = 0 := by
  have hB : ∀ w : ↥W, g w ∈ B := fun w => hfix _ (hgV w) fun i => by
    rw [hcomm i w]
    exact hgA _ (hDW i w w.2)
  refine LinearMap.ext fun w => ?_
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hWAC w.2)
  have hcW : c ∈ W := by
    have e : c = (w : E) - a := by rw [← hac]; abel
    rw [e]
    exact W.sub_mem w.2 (hAW ha)
  have hsplit : w = ⟨a, hAW ha⟩ + ⟨c, hcW⟩ := Subtype.ext hac.symm
  have hmem : g ⟨c, hcW⟩ ∈ B ⊓ T := ⟨hB _, hgC _ hc⟩
  rw [hBT, Submodule.mem_bot] at hmem
  rw [hsplit, map_add, hgA ⟨a, hAW ha⟩ ha, hmem, add_zero, LinearMap.zero_apply]

structure RestrHyp (W A C V B T : Submodule K E) (hAW : A ≤ W) {ι : Type}
    (D : ι → E →ₗ[K] E) (hDW : ∀ i, ∀ w ∈ W, D i w ∈ A) (X : AddSubgroup (↥W →ₗ[K] E)) :
    Prop where
  mapsA : ∀ f ∈ X, ∀ w : ↥W, (w : E) ∈ A → f w ∈ B
  mapsV : ∀ f ∈ X, ∀ w : ↥W, (w : E) ∈ V → f w = 0
  mapsC : ∀ f ∈ X, ∀ w : ↥W, (w : E) ∈ C → f w ∈ T
  mapsW : ∀ f ∈ X, ∀ w : ↥W, f w ∈ V
  comm : ∀ f ∈ X, ∀ i, ∀ w : ↥W, D i (f w) = f ⟨D i w, hAW (hDW i w w.2)⟩

theorem eq_smul_of_restr {W A C V B T : Submodule K E} (hAW : A ≤ W) (hVA : V ≤ A)
    (hWAC : W ≤ A ⊔ C) (hBT : B ⊓ T = ⊥) {ι : Type} {D : ι → E →ₗ[K] E}
    {hDW : ∀ i, ∀ w ∈ W, D i w ∈ A} (hfix : ∀ v ∈ V, (∀ i, D i v = 0) → v ∈ B)
    {X : AddSubgroup (↥W →ₗ[K] E)} (hX : RestrHyp W A C V B T hAW D hDW X)
    {A' : Submodule K ↥A} (hA' : IsCompl (V.comap A.subtype) A') {f g : ↥W →ₗ[K] E}
    (hf : f ∈ X) (hg : g ∈ X) (k : K)
    (hres : ∀ a ∈ A', g ⟨(a : E), hAW a.2⟩ = k • f ⟨(a : E), hAW a.2⟩) : g = k • f := by
  refine sub_eq_zero.mp (eq_zero_of_comm hAW hWAC hBT D hDW hfix (g - k • f) ?_ ?_ ?_ ?_)
  · intro w hw
    have hwA : (⟨(w : E), hw⟩ : ↥A) ∈ V.comap A.subtype ⊔ A' := by
      rw [hA'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨v, hv, a, ha, hva⟩ := Submodule.mem_sup.mp hwA
    have hvV : ((v : ↥A) : E) ∈ V := hv
    have hsplit : w = ⟨((v : ↥A) : E), hAW v.2⟩ + ⟨((a : ↥A) : E), hAW a.2⟩ := by
      apply Subtype.ext
      have := congrArg Subtype.val hva
      simpa using this.symm
    rw [hsplit]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_add]
    rw [hX.mapsV g hg ⟨((v : ↥A) : E), hAW v.2⟩ hvV, hX.mapsV f hf ⟨((v : ↥A) : E), hAW v.2⟩ hvV,
      hres a ha]
    simp
  · intro w hw
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    exact Submodule.sub_mem _ (hX.mapsC g hg w hw) (Submodule.smul_mem _ k (hX.mapsC f hf w hw))
  · intro w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    exact Submodule.sub_mem _ (hX.mapsW g hg w) (Submodule.smul_mem _ k (hX.mapsW f hf w))
  · intro i w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
    rw [hX.comm g hg i w, hX.comm f hf i w]

theorem smul_mem_of_card [Finite K] [Module.Finite K E] {W A C V B T : Submodule K E}
    (hAW : A ≤ W) (hVA : V ≤ A) (hWAC : W ≤ A ⊔ C) (hBT : B ⊓ T = ⊥)
    (hB : Module.finrank K B = 1) {ι : Type} {D : ι → E →ₗ[K] E}
    {hDW : ∀ i, ∀ w ∈ W, D i w ∈ A} (hfix : ∀ v ∈ V, (∀ i, D i v = 0) → v ∈ B)
    {X : AddSubgroup (↥W →ₗ[K] E)} (hX : RestrHyp W A C V B T hAW D hDW X)
    (hcard : Nat.card K ^ (Module.finrank K A - Module.finrank K V) ≤ Nat.card X) :
    ∀ f ∈ X, ∀ k : K, k • f ∈ X := by
  classical
  obtain ⟨A', hA'⟩ := Submodule.exists_isCompl (V.comap A.subtype)
  let incl : ↥A' →ₗ[K] ↥W :=
    (Submodule.inclusion hAW).comp A'.subtype
  have hincl : ∀ a : ↥A', (incl a : E) = ((a : ↥A) : E) := fun a => rfl
  let res : ↥X → (↥A' →ₗ[K] ↥B) := fun f =>
    LinearMap.codRestrict B ((f : ↥W →ₗ[K] E).comp incl)
      (fun a => hX.mapsA f f.2 (incl a) (a : ↥A).2)
  have hres : ∀ (f : ↥X) (a : ↥A'), ((res f a : ↥B) : E) = (f : ↥W →ₗ[K] E) (incl a) :=
    fun f a => rfl
  have hinj : Function.Injective res := by
    intro f g hfg
    apply Subtype.ext
    have h := eq_smul_of_restr hAW hVA hWAC hBT hfix hX hA' f.2 g.2 1 (fun a ha => by
      have h1 := congrArg (fun φ : ↥A' →ₗ[K] ↥B => ((φ ⟨a, ha⟩ : ↥B) : E)) hfg
      simp only [hres] at h1
      rw [one_smul]
      exact h1.symm)
    rw [one_smul] at h
    exact h.symm
  haveI : Finite ↥B := Module.finite_of_finite K
  have hdimA' : Module.finrank K ↥A' = Module.finrank K A - Module.finrank K V := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA'
    have h2 : Module.finrank K ↥(V.comap A.subtype) = Module.finrank K V :=
      (Submodule.comapSubtypeEquivOfLe hVA).finrank_eq
    omega
  have hcardH : Nat.card (↥A' →ₗ[K] ↥B) =
      Nat.card K ^ (Module.finrank K A - Module.finrank K V) := by
    rw [Module.natCard_eq_pow_finrank (K := K), Module.finrank_linearMap, hB, mul_one, hdimA']
  haveI : Finite (↥A' →ₗ[K] ↥B) := Module.finite_of_finite K
  have hbij : Function.Bijective res := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcardH]
    exact hcard
  intro f hf k
  obtain ⟨g, hg⟩ := hbij.2 (k • res ⟨f, hf⟩)
  have h := eq_smul_of_restr hAW hVA hWAC hBT hfix hX hA' hf g.2 k (fun a ha => by
    have h1 := congrArg (fun φ : ↥A' →ₗ[K] ↥B => ((φ ⟨a, ha⟩ : ↥B) : E)) hg
    simp only [hres, LinearMap.smul_apply, Submodule.coe_smul] at h1
    exact h1)
  rw [← h]
  exact g.2

theorem comm_formula {D₁ D₂ P : E →ₗ[K] E} (hP₁ : ∀ x, P (D₁ x) = 0)
    (hP₂ : ∀ x, P (D₂ x) = 0)
    (h : ∀ x, (x + D₁ x + D₂ (x + D₁ x)) + P (x + D₁ x + D₂ (x + D₁ x)) =
      (x + D₂ x) + D₁ (x + D₂ x)) :
    ∀ x, P x = D₁ (D₂ x) - D₂ (D₁ x) := by
  intro x
  have hx := h x
  simp only [map_add, hP₁, hP₂, add_zero] at hx
  linear_combination (norm := module) hx

theorem bilin_D_left {B : LinearMap.BilinForm K E} {V W : Submodule K E} {D : E →ₗ[K] E}
    (hiso : ∀ x y, B (x + D x) (y + D y) = B x y) (hDE : ∀ x, D x ∈ W) (hDW : ∀ w ∈ W, D w ∈ V)
    (hVW : ∀ v ∈ V, ∀ w ∈ W, B v w = 0) {a : E} (ha : a ∈ W) (y : E) :
    B (D a) y = -B a (D y) := by
  have h := hiso a y
  have h0 : B (D a) (D y) = 0 := hVW _ (hDW a ha) _ (hDE y)
  simp only [map_add, LinearMap.add_apply, h0] at h
  linear_combination h

theorem pair_comm {B : LinearMap.BilinForm K E} {V W : Submodule K E} {D₁ D₂ P : E →ₗ[K] E}
    (hP : ∀ x, P x = D₁ (D₂ x) - D₂ (D₁ x))
    (hiso₁ : ∀ x y, B (x + D₁ x) (y + D₁ y) = B x y)
    (hiso₂ : ∀ x y, B (x + D₂ x) (y + D₂ y) = B x y) (hD₁E : ∀ x, D₁ x ∈ W)
    (hD₂E : ∀ x, D₂ x ∈ W) (hD₁W : ∀ w ∈ W, D₁ w ∈ V) (hD₂W : ∀ w ∈ W, D₂ w ∈ V)
    (hVW : ∀ v ∈ V, ∀ w ∈ W, B v w = 0) (x y : E) :
    B (P x) y = B (D₁ x) (D₂ y) - B (D₂ x) (D₁ y) := by
  have h1 := bilin_D_left hiso₁ hD₁E hD₁W hVW (hD₂E x) y
  have h2 := bilin_D_left hiso₂ hD₂E hD₂W hVW (hD₁E x) y
  rw [hP x, map_sub, LinearMap.sub_apply, h1, h2]
  ring

theorem pair_sq [CharP K 2] {B : LinearMap.BilinForm K E} {V W : Submodule K E}
    {D P : E →ₗ[K] E} (h : ∀ x, (x + D x) + D (x + D x) = x + P x)
    (hiso : ∀ x y, B (x + D x) (y + D y) = B x y) (hDE : ∀ x, D x ∈ W)
    (hDW : ∀ w ∈ W, D w ∈ V) (hVW : ∀ v ∈ V, ∀ w ∈ W, B v w = 0) (x y : E) :
    B (P x) y = -B (D x) (D y) := by
  have hx := h x
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hDD : D (D x) = P x := by
    rw [map_add] at hx
    have e : (2 : K) • D x = 0 := by rw [h2, zero_smul]
    linear_combination (norm := module) hx - e
  rw [← hDD]
  exact bilin_D_left hiso hDE hDW hVW (hDE x) y

theorem bilin_D_right {B : LinearMap.BilinForm K E} {V W : Submodule K E} {D : E →ₗ[K] E}
    (hiso : ∀ x y, B (x + D x) (y + D y) = B x y) (hDE : ∀ x, D x ∈ W)
    (hDW : ∀ w ∈ W, D w ∈ V) (hWV : ∀ w ∈ W, ∀ v ∈ V, B w v = 0) (x : E) {w : E}
    (hw : w ∈ W) : B (D x) w = -B x (D w) := by
  have h := hiso x w
  have h0 : B (D x) (D w) = 0 := hWV _ (hDE x) _ (hDW w hw)
  simp only [map_add, LinearMap.add_apply, h0] at h
  linear_combination h

theorem bilin_comb {B : LinearMap.BilinForm K E} {V W : Submodule K E} {D₁ D₂ D₃ : E →ₗ[K] E}
    (hiso₁ : ∀ x y, B (x + D₁ x) (y + D₁ y) = B x y)
    (hiso₂ : ∀ x y, B (x + D₂ x) (y + D₂ y) = B x y)
    (hiso₃ : ∀ x y, B (x + D₃ x) (y + D₃ y) = B x y) (hD₁E : ∀ x, D₁ x ∈ W)
    (hD₂E : ∀ x, D₂ x ∈ W) (hD₃E : ∀ x, D₃ x ∈ W) (hD₁W : ∀ w ∈ W, D₁ w ∈ V)
    (hD₂W : ∀ w ∈ W, D₂ w ∈ V) (hD₃W : ∀ w ∈ W, D₃ w ∈ V)
    (hWV : ∀ w ∈ W, ∀ v ∈ V, B w v = 0) {k₁ k₂ : K}
    (hk : ∀ w ∈ W, D₃ w = k₁ • D₁ w + k₂ • D₂ w) (x : E) {w : E} (hw : w ∈ W) :
    B (D₃ x) w = k₁ * B (D₁ x) w + k₂ * B (D₂ x) w := by
  rw [bilin_D_right hiso₃ hD₃E hD₃W hWV x hw, bilin_D_right hiso₁ hD₁E hD₁W hWV x hw,
    bilin_D_right hiso₂ hD₂E hD₂W hWV x hw, hk w hw, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

end CFSG.RankThree.GF2n.Stroth80.S714
