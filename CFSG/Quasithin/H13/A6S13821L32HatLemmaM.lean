module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.A6.L32HatM

open scoped Matrix

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def ela₁ : SL3 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩
@[expose] def ela₂ : SL3 := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩
@[expose] def rho₃ : SL3 := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by rw [Matrix.det_fin_three]; decide⟩
@[expose] def E₀ : Subgroup SL3 := Subgroup.closure {ela₁, ela₂}
@[expose] def A₀ : Subgroup SL3 := Subgroup.closure {ela₁, ela₂, rho₃}

def swap01 : SL3 := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩
def swap02 : SL3 := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by rw [Matrix.det_fin_three]; decide⟩

abbrev Mat3 := Matrix (Fin 3) (Fin 3) (ZMod 2)

private def detF (M : Mat3) : ZMod 2 :=
  M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2
    + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0

private theorem det_eq_detF (M : Mat3) : M.det = detF M := by
  rw [Matrix.det_fin_three]; rfl

private def adj3 (M : Mat3) : Mat3 :=
  !![M 1 1 * M 2 2 - M 1 2 * M 2 1, -(M 0 1 * M 2 2) + M 0 2 * M 2 1,
      M 0 1 * M 1 2 - M 0 2 * M 1 1;
    -(M 1 0 * M 2 2) + M 1 2 * M 2 0, M 0 0 * M 2 2 - M 0 2 * M 2 0,
      -(M 0 0 * M 1 2) + M 0 2 * M 1 0;
    M 1 0 * M 2 1 - M 1 1 * M 2 0, -(M 0 0 * M 2 1) + M 0 1 * M 2 0,
      M 0 0 * M 1 1 - M 0 1 * M 1 0]

private theorem adj3_eq (M : Mat3) : adj3 M = Matrix.adjugate M := by
  rw [Matrix.adjugate_fin_three]; rfl

private def ela1M : Mat3 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]
private def ela2M : Mat3 := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
private def rho3M : Mat3 := !![1, 0, 0; 0, 0, 1; 0, 1, 1]
private def swapM : Mat3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def P0M : List Mat3 :=
  [!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 0, 1, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 1, 0],
    !![1, 0, 1; 0, 0, 1; 0, 1, 0], !![1, 0, 1; 0, 0, 1; 0, 1, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    !![1, 0, 1; 0, 1, 0; 0, 1, 1], !![1, 0, 1; 0, 1, 1; 0, 0, 1], !![1, 0, 1; 0, 1, 1; 0, 1, 0],
    !![1, 1, 0; 0, 0, 1; 0, 1, 0], !![1, 1, 0; 0, 0, 1; 0, 1, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 1, 1], !![1, 1, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 0; 0, 1, 1; 0, 1, 0],
    !![1, 1, 1; 0, 0, 1; 0, 1, 0], !![1, 1, 1; 0, 0, 1; 0, 1, 1], !![1, 1, 1; 0, 1, 0; 0, 0, 1],
    !![1, 1, 1; 0, 1, 0; 0, 1, 1], !![1, 1, 1; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 1, 0]]

private def A0M : List Mat3 :=
  [!![1, 0, 0; 0, 0, 1; 0, 1, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 1, 0],
    !![1, 0, 1; 0, 0, 1; 0, 1, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 1; 0, 1, 0],
    !![1, 1, 0; 0, 0, 1; 0, 1, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 1; 0, 1, 0],
    !![1, 1, 1; 0, 0, 1; 0, 1, 1], !![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 1, 0]]

private def E0M : List Mat3 := [1, ela1M, ela2M, ela1M * ela2M]

private def genM : Fin 3 → Mat3 := ![ela1M, ela2M, rho3M]

private def wordM (w : List (Fin 3)) : Mat3 := w.foldr (fun i acc => genM i * acc) 1

private def A0W : List (List (Fin 3)) :=
  [[2], [], [2, 2], [0, 2], [1], [2, 0, 2], [2, 0], [0], [1, 2, 2], [1, 2], [0, 1], [0, 2, 2]]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
private theorem P0M_enum : ∀ a b c d e f g h i : ZMod 2,
    detF !![a, b, c; d, e, f; g, h, i] = 1 → a = 1 → d = 0 → g = 0 →
      !![a, b, c; d, e, f; g, h, i] ∈ P0M := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem P0M_props : ∀ M ∈ P0M, detF M = 1 ∧ M 0 0 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem P0M_conj : ∀ M ∈ P0M, ∃ T ∈ P0M, T * M = adj3 M * T := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem P0M_norm : ∀ M ∈ P0M, ∀ e ∈ [ela1M, ela2M],
    ∃ f ∈ E0M, adj3 M * e * M = f := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
private theorem cover_fin : ∀ a b c d e f g h i : ZMod 2,
    detF !![a, b, c; d, e, f; g, h, i] = 1 → ¬ (a = 1 ∧ d = 0 ∧ g = 0) →
      ∃ s ∈ P0M, adj3 (s * swapM) * !![a, b, c; d, e, f; g, h, i] ∈ A0M := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem A0M_words : ∀ M ∈ A0M, ∃ w ∈ A0W, wordM w = M := by
  decide +kernel

private theorem swapM_det : detF swapM = 1 := by decide

def e0v : Fin 3 → ZMod 2 := ![1, 0, 0]

private theorem mulVec_e0_iff (M : Mat3) :
    M *ᵥ e0v = e0v ↔ M 0 0 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0v] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0v, h0, h1, h2]

private theorem mem_P0M_of (s : SL3) (hs : s.1 *ᵥ e0v = e0v) : s.1 ∈ P0M := by
  obtain ⟨h0, h1, h2⟩ := (mulVec_e0_iff s.1).1 hs
  have hM := Matrix.eta_fin_three s.1
  have hdet : detF !![s.1 0 0, s.1 0 1, s.1 0 2; s.1 1 0, s.1 1 1, s.1 1 2;
      s.1 2 0, s.1 2 1, s.1 2 2] = 1 := by
    rw [← hM, ← det_eq_detF]; exact s.2
  have key := P0M_enum _ _ _ _ _ _ _ _ _ hdet h0 h1 h2
  rwa [← hM] at key

private theorem sl3_of_P0M {M : Mat3} (hM : M ∈ P0M) : ∃ t : SL3, t.1 = M :=
  ⟨⟨M, by rw [det_eq_detF]; exact (P0M_props M hM).1⟩, rfl⟩

private theorem inv_fix {s : SL3} (hs : s.1 *ᵥ e0v = e0v) : (s⁻¹).1 *ᵥ e0v = e0v := by
  have h : (s⁻¹).1 * s.1 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (s⁻¹).1 *ᵥ e0v = (s⁻¹).1 *ᵥ (s.1 *ᵥ e0v) := by rw [hs]
    _ = ((s⁻¹).1 * s.1) *ᵥ e0v := by rw [Matrix.mulVec_mulVec]
    _ = e0v := by rw [h, Matrix.one_mulVec]

private theorem conj_witness {s : SL3} (hs : s.1 *ᵥ e0v = e0v) :
    ∃ t : SL3, t.1 *ᵥ e0v = e0v ∧ t * s = s⁻¹ * t := by
  obtain ⟨T, hT, hTs⟩ := P0M_conj s.1 (mem_P0M_of s hs)
  obtain ⟨t, rfl⟩ := sl3_of_P0M hT
  refine ⟨t, ?_, ?_⟩
  · exact (mulVec_e0_iff t.1).2
      ⟨(P0M_props _ hT).2.1, (P0M_props _ hT).2.2.1, (P0M_props _ hT).2.2.2⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ← adj3_eq]
    exact hTs

private theorem ela₁_mem_E0 : ela₁ ∈ E₀ := Subgroup.subset_closure (by simp)
private theorem ela₂_mem_E0 : ela₂ ∈ E₀ := Subgroup.subset_closure (by simp)
private theorem ela₁_mem_A0 : ela₁ ∈ A₀ := Subgroup.subset_closure (by simp)
private theorem ela₂_mem_A0 : ela₂ ∈ A₀ := Subgroup.subset_closure (by simp)
private theorem rho₃_mem_A0 : rho₃ ∈ A₀ := Subgroup.subset_closure (by simp)

private theorem E0_le_A0 : E₀ ≤ A₀ := by
  unfold E₀ A₀
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private def genSL : Fin 3 → SL3 := ![ela₁, ela₂, rho₃]

private theorem genSL_mem (i : Fin 3) : genSL i ∈ A₀ := by
  fin_cases i
  · exact ela₁_mem_A0
  · exact ela₂_mem_A0
  · exact rho₃_mem_A0

private theorem genSL_coe (i : Fin 3) : (genSL i).1 = genM i := by
  fin_cases i <;> rfl

private def wordSL (w : List (Fin 3)) : SL3 := w.foldr (fun i acc => genSL i * acc) 1

private theorem wordSL_mem (w : List (Fin 3)) : wordSL w ∈ A₀ := by
  induction w with
  | nil => exact A₀.one_mem
  | cons i w ih => exact A₀.mul_mem (genSL_mem i) ih

private theorem wordSL_coe (w : List (Fin 3)) : (wordSL w).1 = wordM w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    show (genSL i * wordSL w).1 = genM i * wordM w
    rw [Matrix.SpecialLinearGroup.coe_mul, ih, genSL_coe]

private theorem A0M_sub {M : Mat3} (hM : M ∈ A0M) : ∃ a : SL3, a ∈ A₀ ∧ a.1 = M := by
  obtain ⟨w, -, hw⟩ := A0M_words M hM
  exact ⟨wordSL w, wordSL_mem w, by rw [wordSL_coe, hw]⟩

private theorem E0M_sub {M : Mat3} (hM : M ∈ E0M) : ∃ e : SL3, e ∈ E₀ ∧ e.1 = M := by
  simp only [E0M, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨1, E₀.one_mem, rfl⟩
  · exact ⟨ela₁, ela₁_mem_E0, rfl⟩
  · exact ⟨ela₂, ela₂_mem_E0, rfl⟩
  · exact ⟨ela₁ * ela₂, E₀.mul_mem ela₁_mem_E0 ela₂_mem_E0, rfl⟩

private theorem conj_mem_E0 {s : SL3} (hs : s.1 *ᵥ e0v = e0v) {e : SL3} (he : e ∈ E₀) :
    s⁻¹ * e * s ∈ E₀ := by
  have gen : ∀ x ∈ ({ela₁, ela₂} : Set SL3), s⁻¹ * x * s ∈ E₀ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hxM : x.1 ∈ [ela1M, ela2M] := by
      rcases hx with rfl | rfl
      · show ela1M ∈ [ela1M, ela2M]; simp
      · show ela2M ∈ [ela1M, ela2M]; simp
    obtain ⟨f, hf, hfx⟩ := P0M_norm s.1 (mem_P0M_of s hs) x.1 hxM
    obtain ⟨e', he', he'M⟩ := E0M_sub hf
    have heq : s⁻¹ * x * s = e' := by
      apply Subtype.ext
      rw [he'M, ← hfx, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, adj3_eq]
    rw [heq]; exact he'
  have key : ∀ x ∈ E₀, s⁻¹ * x * s ∈ E₀ := by
    intro x hx
    have hx' : x ∈ Subgroup.closure ({ela₁, ela₂} : Set SL3) := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy => exact gen y hy
    | one => simp
    | mul a b _ _ iha ihb =>
      have : s⁻¹ * (a * b) * s = (s⁻¹ * a * s) * (s⁻¹ * b * s) := by group
      rw [this]; exact E₀.mul_mem iha ihb
    | inv a _ iha =>
      have : s⁻¹ * a⁻¹ * s = (s⁻¹ * a * s)⁻¹ := by group
      rw [this]; exact E₀.inv_mem iha
  exact key e he

private theorem mem_fixedC {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (u : U) :
    u ∈ (⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) ↔ ∀ e ∈ E₀, ρ e u = u := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

private theorem rho_mul {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (a b : SL3) (u : U) : ρ (a * b) u = ρ a (ρ b u) := by
  rw [map_mul, Module.End.mul_apply]

private theorem rho_stable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) {s : SL3} (hs : s.1 *ᵥ e0v = e0v) {c : U}
    (hc : c ∈ (⨅ e ∈ E₀, LinearMap.ker (ρ e - 1))) :
    ρ s c ∈ (⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) := by
  rw [mem_fixedC] at hc ⊢
  intro e he
  have h1 : ρ (s⁻¹ * e * s) c = c := hc _ (conj_mem_E0 hs he)
  have hsplit : e * s = s * (s⁻¹ * e * s) := by group
  calc ρ e (ρ s c) = ρ (e * s) c := (rho_mul ρ e s c).symm
    _ = ρ (s * (s⁻¹ * e * s)) c := by rw [hsplit]
    _ = ρ s (ρ (s⁻¹ * e * s) c) := rho_mul ρ s _ c
    _ = ρ s c := by rw [h1]

private theorem scalar_formula {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (φ : U →ₗ[F] F)
    (hker : LinearMap.ker φ = ⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) (u₁ : U) (hu₁ : φ u₁ = 1)
    {s : SL3} (hs : s.1 *ᵥ e0v = e0v) (u : U) :
    φ (ρ s u) = φ (ρ s u₁) * φ u := by
  have hw : u - φ u • u₁ ∈ (⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) := by
    rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hu₁, smul_eq_mul, mul_one, sub_self]
  have hsw : φ (ρ s (u - φ u • u₁)) = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact rho_stable ρ hs hw
  have hsplit : ρ s u = φ u • ρ s u₁ + ρ s (u - φ u • u₁) := by
    rw [map_sub, map_smul]; abel
  rw [hsplit, map_add, hsw, add_zero, map_smul, smul_eq_mul, mul_comm]

private theorem sc_mul {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (φ : U →ₗ[F] F)
    (hker : LinearMap.ker φ = ⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) (u₁ : U) (hu₁ : φ u₁ = 1)
    (s t : SL3) (hs : s.1 *ᵥ e0v = e0v) :
    φ (ρ (s * t) u₁) = φ (ρ s u₁) * φ (ρ t u₁) := by
  rw [rho_mul, scalar_formula ρ φ hker u₁ hu₁ hs]

private theorem sc_eq_one {F U : Type*} [Field F] [CharP F 2] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (φ : U →ₗ[F] F)
    (hker : LinearMap.ker φ = ⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) (u₁ : U) (hu₁ : φ u₁ = 1)
    {s : SL3} (hs : s.1 *ᵥ e0v = e0v) : φ (ρ s u₁) = 1 := by
  obtain ⟨t, ht, hts⟩ := conj_witness hs
  have hsinv := inv_fix hs
  have htinv := inv_fix ht
  have h1 : φ (ρ t u₁) * φ (ρ s u₁) = φ (ρ s⁻¹ u₁) * φ (ρ t u₁) := by
    rw [← sc_mul ρ φ hker u₁ hu₁ t s ht, hts, sc_mul ρ φ hker u₁ hu₁ s⁻¹ t hsinv]
  have h2 : φ (ρ s u₁) * φ (ρ s⁻¹ u₁) = 1 := by
    rw [← sc_mul ρ φ hker u₁ hu₁ s s⁻¹ hs, mul_inv_cancel, map_one, Module.End.one_apply, hu₁]
  have h3 : φ (ρ t u₁) * φ (ρ t⁻¹ u₁) = 1 := by
    rw [← sc_mul ρ φ hker u₁ hu₁ t t⁻¹ ht, mul_inv_cancel, map_one, Module.End.one_apply, hu₁]
  have hc0 : φ (ρ t u₁) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h3
    exact zero_ne_one h3
  have h4 : φ (ρ t u₁) * (φ (ρ s u₁) ^ 2 - 1) = 0 := by
    linear_combination φ (ρ s u₁) * h1 + φ (ρ t u₁) * h2
  have h5 : φ (ρ s u₁) ^ 2 = 1 := by
    have := (mul_eq_zero.1 h4).resolve_left hc0
    linear_combination this
  have h2' : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h6 : (φ (ρ s u₁) - 1) ^ 2 = 0 := by
    linear_combination h5 - (φ (ρ s u₁) - 1) * h2'
  have h7 : φ (ρ s u₁) - 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h6
  linear_combination h7

private theorem cover_sl {g : SL3} (hg : g.1 *ᵥ e0v ≠ e0v) :
    ∃ s : SL3, s.1 *ᵥ e0v = e0v ∧ ∃ a : SL3, a ∈ A₀ ∧ g = s * swap01 * a := by
  have hM := Matrix.eta_fin_three g.1
  have hdet : detF !![g.1 0 0, g.1 0 1, g.1 0 2; g.1 1 0, g.1 1 1, g.1 1 2;
      g.1 2 0, g.1 2 1, g.1 2 2] = 1 := by
    rw [← hM, ← det_eq_detF]; exact g.2
  have hnot : ¬ (g.1 0 0 = 1 ∧ g.1 1 0 = 0 ∧ g.1 2 0 = 0) :=
    fun h => hg ((mulVec_e0_iff g.1).2 h)
  obtain ⟨s, hsP, hsA⟩ := cover_fin _ _ _ _ _ _ _ _ _ hdet hnot
  rw [← hM] at hsA
  obtain ⟨a, haA, ha⟩ := A0M_sub hsA
  obtain ⟨S, hS⟩ := sl3_of_P0M hsP
  have hsd : (s * swapM).det = 1 := by
    rw [Matrix.det_mul, det_eq_detF s, det_eq_detF swapM, (P0M_props s hsP).1, swapM_det,
      mul_one]
  refine ⟨S, ?_, a, haA, ?_⟩
  · rw [hS]
    exact (mulVec_e0_iff s).2
      ⟨(P0M_props s hsP).2.1, (P0M_props s hsP).2.2.1, (P0M_props s hsP).2.2.2⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS, ha]
    show g.1 = s * swapM * (adj3 (s * swapM) * g.1)
    rw [adj3_eq, ← Matrix.mul_assoc, Matrix.mul_adjugate, hsd, one_smul, one_mul]

private theorem rho_conj_one {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (h : ρ ela₁ = 1) (σ τ T : SL3) (hστ : σ * τ = 1)
    (hT : T = σ * ela₁ * τ) : ρ T = 1 := by
  rw [hT, map_mul, map_mul, h, mul_one, ← map_mul, hστ, map_one]

private def mkSL3 (M : Mat3) (h : detF M = 1) : SL3 := ⟨M, by rw [det_eq_detF]; exact h⟩

private def trM : Fin 6 → Mat3 :=
  ![ela1M, ela2M, !![1, 0, 0; 1, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 1]]

private theorem trM_det : ∀ k : Fin 6, detF (trM k) = 1 := by decide

private def trSL (k : Fin 6) : SL3 := ⟨trM k, by rw [det_eq_detF]; exact trM_det k⟩

private theorem trSL_coe (k : Fin 6) : (trSL k).1 = trM k := rfl

private def wordTM (w : List (Fin 6)) : Mat3 := w.foldr (fun k acc => trM k * acc) 1

private def wordTSL (w : List (Fin 6)) : SL3 := w.foldr (fun k acc => trSL k * acc) 1

private theorem wordTSL_coe (w : List (Fin 6)) : (wordTSL w).1 = wordTM w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    show (trSL k).1 * (wordTSL w).1 = trM k * wordTM w
    rw [ih, trSL_coe]

private def P0W : List (List (Fin 6)) :=
  [[3, 5, 3], [3, 5], [], [5], [3], [5, 3], [0, 3, 5, 3], [0, 3, 5], [1], [5, 1], [1, 3],
    [5, 1, 3], [1, 3, 5, 3], [3, 0, 5], [0], [0, 5], [3, 0], [1, 5, 3], [3, 0, 5, 3], [1, 3, 5],
    [0, 1], [1, 5], [0, 3], [0, 5, 3]]

private def swapW : List (Fin 6) := [0, 2, 0]

set_option maxRecDepth 100000 in
private theorem P0W_ok : ∀ M ∈ P0M, ∃ w ∈ P0W, wordTM w = M := by
  decide +kernel

private theorem swapW_ok : wordTM swapW = swapM := by decide +kernel

private theorem rho_wordTSL {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (hT : ∀ k, ρ (trSL k) = 1) (w : List (Fin 6)) :
    ρ (wordTSL w) = 1 := by
  induction w with
  | nil => exact map_one ρ
  | cons k w ih =>
    show ρ (trSL k * wordTSL w) = 1
    rw [map_mul, hT k, ih, mul_one]

private theorem rho_trSL {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (h : ρ ela₁ = 1) (k : Fin 6) : ρ (trSL k) = 1 := by
  fin_cases k
  · exact rho_conj_one ρ h 1 1 _ (by decide) (Subtype.ext (by decide))
  · exact rho_conj_one ρ h (mkSL3 !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide))
      (mkSL3 !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide)) _ (by decide) (Subtype.ext (by decide))
  · exact rho_conj_one ρ h (mkSL3 !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide))
      (mkSL3 !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide)) _ (by decide) (Subtype.ext (by decide))
  · exact rho_conj_one ρ h (mkSL3 !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by decide))
      (mkSL3 !![0, 1, 0; 0, 0, 1; 1, 0, 0] (by decide)) _ (by decide) (Subtype.ext (by decide))
  · exact rho_conj_one ρ h (mkSL3 !![0, 1, 0; 0, 0, 1; 1, 0, 0] (by decide))
      (mkSL3 !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by decide)) _ (by decide) (Subtype.ext (by decide))
  · exact rho_conj_one ρ h (mkSL3 !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by decide))
      (mkSL3 !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by decide)) _ (by decide) (Subtype.ext (by decide))

private theorem rho_P0 {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (hT : ∀ k, ρ (trSL k) = 1) (s : SL3)
    (hs : s.1 *ᵥ e0v = e0v) : ρ s = 1 := by
  obtain ⟨w, -, hw⟩ := P0W_ok s.1 (mem_P0M_of s hs)
  have hsw : s = wordTSL w := Subtype.ext (by rw [wordTSL_coe, hw])
  rw [hsw]
  exact rho_wordTSL ρ hT w

private theorem rho_swap {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (hT : ∀ k, ρ (trSL k) = 1) : ρ swap01 = 1 := by
  have hsw : swap01 = wordTSL swapW := Subtype.ext (by
    show swapM = (wordTSL swapW).1
    rw [wordTSL_coe, swapW_ok])
  rw [hsw]
  exact rho_wordTSL ρ hT swapW

private theorem A0_fix : ∀ a ∈ A₀, a.1 *ᵥ e0v = e0v := by
  intro a ha
  have ha' : a ∈ Subgroup.closure ({ela₁, ela₂, rho₃} : Set SL3) := ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> decide
  | one => rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  | mul x y _ _ hx hy =>
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hy, hx]
  | inv x _ hx => exact inv_fix hx

private theorem rho_eq_one_of_ela {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (h : ρ ela₁ = 1) (g : SL3) : ρ g = 1 := by
  have hT := rho_trSL ρ h
  by_cases hg : g.1 *ᵥ e0v = e0v
  · exact rho_P0 ρ hT g hg
  · obtain ⟨s, hs, a, ha, rfl⟩ := cover_sl hg
    rw [map_mul, map_mul, rho_P0 ρ hT s hs, rho_swap ρ hT, rho_P0 ρ hT a (A0_fix a ha)]
    simp

theorem two_le_finrank_quot_fixed {F U : Type*} [Field F] [CharP F 2]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (ρ : SL3 →* Module.End F U) (v₀ : U)
    (hA : ∀ a ∈ A₀, ρ a v₀ = v₀)
    (hgen : Submodule.span F (Set.range fun g => ρ g v₀) = ⊤)
    (hnt : ∃ g, ρ g ≠ 1) :
    2 ≤ Module.finrank F (U ⧸ ⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) := by
  set C : Submodule F U := ⨅ e ∈ E₀, LinearMap.ker (ρ e - 1) with hCdef
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hone : ρ ela₁ = 1 := by
      refine LinearMap.ext fun u => ?_
      have hu : u ∈ C := by rw [htop]; exact Submodule.mem_top
      rw [Module.End.one_apply]
      exact (mem_fixedC ρ u).1 hu ela₁ ela₁_mem_E0
    obtain ⟨g, hg⟩ := hnt
    exact hg (rho_eq_one_of_ela ρ hone g)
  have hpos : 0 < Module.finrank F (U ⧸ C) := by
    haveI : Nontrivial (U ⧸ C) := Submodule.Quotient.nontrivial_iff.2 hCtop
    exact Module.finrank_pos
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hd : Module.finrank F (U ⧸ C) = 1 := by omega
  let e : (U ⧸ C) ≃ₗ[F] F := LinearEquiv.ofFinrankEq _ _ (by rw [hd, Module.finrank_self])
  obtain ⟨φ, hker, hsurj⟩ : ∃ φ : U →ₗ[F] F, LinearMap.ker φ = C ∧ Function.Surjective φ :=
    ⟨e.toLinearMap ∘ₗ C.mkQ, by ext u; simp [e], e.surjective.comp (Submodule.mkQ_surjective C)⟩
  obtain ⟨u₁, hu₁⟩ := hsurj 1
  have hv0C : v₀ ∈ C := (mem_fixedC ρ v₀).2 fun a ha => hA a (E0_le_A0 ha)
  have hφv0 : φ v₀ = 0 := by rw [← LinearMap.mem_ker, hker]; exact hv0C
  obtain ⟨f, hf⟩ : ∃ f : SL3 → F, ∀ g, f g = φ (ρ g v₀) := ⟨fun g => φ (ρ g v₀), fun _ => rfl⟩
  have hf1 : f 1 = 0 := by rw [hf, map_one, Module.End.one_apply, hφv0]
  have hV2 : ∀ s : SL3, s.1 *ᵥ e0v = e0v → ∀ g : SL3, f (s * g) = f g := by
    intro s hs g
    rw [hf, hf, rho_mul, scalar_formula ρ φ hker u₁ hu₁ hs, sc_eq_one ρ φ hker u₁ hu₁ hs, one_mul]
  have hV3 : ∀ g a : SL3, a ∈ A₀ → f (g * a) = f g := by
    intro g a ha
    rw [hf, hf, rho_mul, hA a ha]
  have hV4 : ∀ g : SL3, g.1 *ᵥ e0v ≠ e0v → f g = f swap01 := by
    intro g hg
    obtain ⟨s, hs, a, ha, rfl⟩ := cover_sl hg
    rw [mul_assoc, hV2 s hs, hV3 swap01 a ha]
  have hβne : f swap01 ≠ 0 := by
    intro h0
    have hall : ∀ g : SL3, f g = 0 := by
      intro g
      by_cases hg : g.1 *ᵥ e0v = e0v
      · have := hV2 g hg 1
        rw [mul_one, hf1] at this
        exact this
      · rw [hV4 g hg, h0]
    have hφ0 : φ = 0 := LinearMap.ext_on_range hgen fun g => by
      simp only [LinearMap.zero_apply]
      rw [← hf]
      exact hall g
    rw [hφ0, LinearMap.zero_apply] at hu₁
    exact zero_ne_one hu₁
  obtain ⟨x, hxdef⟩ : ∃ x : SL3, x = swap01 * ela₁ * swap01 := ⟨_, rfl⟩
  have hsw : swap01 * swap01 = 1 := Subtype.ext (by decide)
  have hρx : ∀ w : U, φ (ρ swap01 w) = 0 → ρ x w = w := by
    intro w hw
    have hC' : ρ swap01 w ∈ C := by
      rw [← hker]; exact LinearMap.mem_ker.2 hw
    have hfix : ρ ela₁ (ρ swap01 w) = ρ swap01 w := (mem_fixedC ρ _).1 hC' ela₁ ela₁_mem_E0
    calc ρ x w = ρ swap01 (ρ ela₁ (ρ swap01 w)) := by rw [hxdef, rho_mul, rho_mul]
      _ = ρ swap01 (ρ swap01 w) := by rw [hfix]
      _ = w := by rw [← rho_mul, hsw, map_one, Module.End.one_apply]
  have hdecomp : ∀ u : U, ρ x u = u + φ (ρ swap01 u) • (ρ x (ρ swap01 u₁) - ρ swap01 u₁) := by
    intro u
    have hΦ : φ (ρ swap01 (ρ swap01 u₁)) = 1 := by
      rw [← rho_mul, hsw, map_one, Module.End.one_apply, hu₁]
    have hw : φ (ρ swap01 (u - φ (ρ swap01 u) • ρ swap01 u₁)) = 0 := by
      simp only [map_sub, map_smul, hΦ, smul_eq_mul, mul_one, sub_self]
    have hfw := hρx _ hw
    have hsmul : ρ x (φ (ρ swap01 u) • ρ swap01 u₁) = φ (ρ swap01 u) • ρ x (ρ swap01 u₁) := by
      rw [map_smul]
    have key : ρ x (u - φ (ρ swap01 u) • ρ swap01 u₁) + ρ x (φ (ρ swap01 u) • ρ swap01 u₁)
        = ρ x u := by
      rw [← map_add, sub_add_cancel]
    rw [hsmul] at key
    rw [← key, hfw, smul_sub]
    abel
  obtain ⟨lam, hlam⟩ : ∃ lam : F, lam = φ (ρ x (ρ swap01 u₁) - ρ swap01 u₁) := ⟨_, rfl⟩
  have hstar : ∀ h : SL3, f (x * h) = f h + lam * f (swap01 * h) := by
    intro h
    rw [hf, hf, hf, rho_mul ρ x h v₀, rho_mul ρ swap01 h v₀, hdecomp, map_add, map_smul, smul_eq_mul,
      hlam]
    ring
  have hxc : x.1 *ᵥ e0v ≠ e0v := by rw [hxdef]; decide
  have hhrc : swap02.1 *ᵥ e0v ≠ e0v := by decide
  have hxhrc : (x * swap02).1 *ᵥ e0v ≠ e0v := by rw [hxdef]; decide
  have hswhrc : (swap01 * swap02).1 *ᵥ e0v ≠ e0v := by decide
  have e1 := hstar 1
  have e2 := hstar swap02
  rw [mul_one, mul_one, hf1, hV4 x hxc] at e1
  rw [hV4 (x * swap02) hxhrc, hV4 swap02 hhrc, hV4 (swap01 * swap02) hswhrc] at e2
  have h3 : lam * f swap01 = 0 := by linear_combination -e2
  exact hβne (by linear_combination e1 + h3)

end CFSG.Quasithin.H13.A6.L32HatM
