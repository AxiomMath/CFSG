module

public import CFSG.Quasithin.Background.SmithCurtisMain
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthSL2
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Indep
import CFSG.RepresentationTheory.SL2NatSum.Interpolation
public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.LinearPilot (diagUnit)
open scoped MatrixGroups

private lemma spCI_coe_sl2Upper {K : Type*} [Field K] (c : K) :
    (sl2Upper c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

private lemma spCI_coe_sl2Lower {K : Type*} [Field K] (c : K) :
    (sl2Lower c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem sl2Upper_mul_sl2Lower_of_ne {K : Type*} [Field K] {a b : K} (h : 1 + a * b ≠ 0) :
    sl2Upper a * sl2Lower b =
      sl2Lower (b / (1 + a * b)) * diagUnit (Units.mk0 (1 + a * b) h) *
        sl2Upper (a / (1 + a * b)) := by
  have hba : 1 + b * a ≠ 0 := by
    rw [mul_comm b a]
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, spCI_coe_sl2Upper, spCI_coe_sl2Lower,
      CFSG.SeitzReduction.LinearPilot.coe_diagUnit, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_mk0] <;>
    field_simp [hba]; ring

theorem sl2Upper_mul_sl2Lower_of_eq {K : Type*} [Field K] {a b : K} (ha : a ≠ 0)
    (h : 1 + a * b = 0) :
    sl2Upper a * sl2Lower b =
      sl2Upper 1 * sl2Lower (-1) * sl2Upper 1 * diagUnit (Units.mk0 a ha)⁻¹ * sl2Upper (-a) := by
  have hb : b = -a⁻¹ := by
    field_simp [ha]
    linear_combination h
  rw [hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, spCI_coe_sl2Upper, spCI_coe_sl2Lower,
      CFSG.SeitzReduction.LinearPilot.coe_diagUnit, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_mk0, Units.val_inv_eq_inv_val] <;>
    field_simp [ha]; ring

theorem form_mul_nW_mul_mul {G : Type*} [Group G] [Finite G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs p}
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V} {y : V}
    {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ D.L, f z = 0) (hfy : f y = 1) {ω : List B} (hω : cs.IsReduced ω)
    {l h u : G} (hl : l ∈ D.L) (hh : h ∈ D.H) (hu : u ∈ D.U) :
    f (ρ (l * D.nW (cs.wordProd ω) * h * u) y) = χ h * D.coinvScalar χ μ ω := by
  have hu_fix : ρ u y = y := ht.1 u hu
  have hl_fix : f (ρ l (ρ (D.nW (cs.wordProd ω) * h) y)) =
      f (ρ (D.nW (cs.wordProd ω) * h) y) := by
    have h0 := hf _ (sub_mem_augSub ρ hl (ρ (D.nW (cs.wordProd ω) * h) y))
    rwa [map_sub, sub_eq_zero] at h0
  calc f (ρ (l * D.nW (cs.wordProd ω) * h * u) y)
      = f (ρ l (ρ (D.nW (cs.wordProd ω) * h) y)) := by
        rw [show l * D.nW (cs.wordProd ω) * h * u =
            l * (D.nW (cs.wordProd ω) * h) * u by group, ← act_mul, hu_fix, ← act_mul]
    _ = f (ρ (D.nW (cs.wordProd ω) * h) y) := hl_fix
    _ = χ h * D.coinvScalar χ μ ω :=
        CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.form_nW_mul D ρ ht hf hfy hω hh

private theorem spCI_nW_simple {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p) (s : B) :
    D.nW (cs.simple s) = D.n s := by
  have hlen : cs.length (cs.simple s * (1 : W)) = cs.length (1 : W) + 1 := by
    simp [cs.length_simple]
  have hh := D.nW_simple_mul (1 : W) s hlen
  rwa [mul_one, D.nW_one, mul_one] at hh

theorem form_sl2Upper_mul_sl2Lower {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    {D : CurtisDatum G cs p} {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {y₀ : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V} (hf : ∀ z ∈ augSub ρ D.L, f z = 0)
    (hfy : f y₀ = 1) {K : Type*} [Field K] (ι : K →+* k) (σ : SL(2, K) →* G) {s : B}
    (hU : ∀ c, σ (sl2Upper c) ∈ D.U) (hL : ∀ c, σ (sl2Lower c) ∈ D.L)
    (hH : ∀ u, σ (diagUnit u) ∈ D.H)
    (hn : ∃ h ∈ D.H, σ (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) = D.n s * h)
    (hμ : μ s = D.dScalar χ s) {c : ℕ} (hc : 1 ≤ c)
    (hχ : ∀ u : Kˣ, χ (σ (diagUnit u)) = ι (u : K) ^ c) (a b : K) :
    f (ρ (σ (sl2Upper a) * σ (sl2Lower b)) y₀) = (1 + ι a * ι b) ^ c := by
  by_cases h : 1 + a * b ≠ 0
  · have hσ : σ (sl2Upper a) * σ (sl2Lower b) =
        σ (sl2Lower (b / (1 + a * b))) * σ (diagUnit (Units.mk0 (1 + a * b) h)) *
          σ (sl2Upper (a / (1 + a * b))) := by
      rw [← map_mul, sl2Upper_mul_sl2Lower_of_ne h, map_mul, map_mul]
    rw [hσ]
    have key := form_mul_nW_mul_mul (D := D) (cs := cs) (ω := [])
      (l := σ (sl2Lower (b / (1 + a * b))))
      (h := σ (diagUnit (Units.mk0 (1 + a * b) h)))
      (u := σ (sl2Upper (a / (1 + a * b)))) ht hf hfy
      (by simp [CoxeterSystem.IsReduced]) (hL _) (hH _) (hU _)
    rw [cs.wordProd_nil, D.nW_one, mul_one] at key
    rw [key, show D.coinvScalar χ μ [] = 1 by simp [CurtisDatum.coinvScalar], mul_one,
      hχ (Units.mk0 (1 + a * b) h)]
    simp only [Units.val_mk0, map_add, map_mul, map_one]
  · have ha : a ≠ 0 := by rintro rfl; exact h (by simp)
    have h0 : 1 + a * b = 0 := of_not_not h
    obtain ⟨h₀, hh₀, e₀⟩ := hn
    have hnW : D.nW (cs.simple s) = D.n s := spCI_nW_simple D s
    have key := form_mul_nW_mul_mul (D := D) (cs := cs) (ω := [s])
      (l := (1 : G)) (h := h₀ * σ (diagUnit (Units.mk0 a ha)⁻¹))
      (u := σ (sl2Upper (-a))) ht hf hfy
      (by simp [CoxeterSystem.IsReduced, cs.length_simple]) (one_mem D.L) (mul_mem hh₀ (hH _))
      (hU _)
    rw [cs.wordProd_singleton, hnW] at key
    rw [← map_mul, sl2Upper_mul_sl2Lower_of_eq ha h0, map_mul, map_mul, map_mul, map_mul,
      ← map_mul, ← map_mul, e₀]
    rw [show (D.n s * h₀) * σ (diagUnit (Units.mk0 a ha)⁻¹) * σ (sl2Upper (-a)) =
        1 * D.n s * (h₀ * σ (diagUnit (Units.mk0 a ha)⁻¹)) * σ (sl2Upper (-a)) by group]
    rw [key, ht.chi_mul hh₀ (hH _),
      show D.coinvScalar χ μ [s] = 0 by simp [CurtisDatum.coinvScalar, hμ], mul_zero]
    rw [show 1 + ι a * ι b = 0 by
        simpa [map_add, map_mul, map_one, map_zero] using congrArg ι h0,
      zero_pow (by omega : c ≠ 0)]

private theorem spCI_coeff_eq_zero {F k V : Type*} [Field F] [Fintype F] [Field k]
    [AddCommGroup V] [Module k V] (ι : F →+* k) {u : ℕ → V}
    (h : ∀ t : F, ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • u j = 0) :
    ∀ j < Fintype.card F, u j = 0 := by
  let _ : Module F V := Module.compHom V ι
  refine CFSG.RepresentationTheory.SL2NatSum.coeff_eq_zero_of_forall_sum_eq_zero (K := F)
    (M := V) u ?_
  intro t
  rw [show (∑ j ∈ Finset.range (Fintype.card F), t ^ j • u j) =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • u j by
    refine Finset.sum_congr rfl fun j _ => ?_
    show ι (t ^ j) • u j = (ι t) ^ j • u j
    rw [map_pow]]
  exact h t

private theorem spCI_interp_w {G : Type*} [Group G] {F k V : Type*} [Field F] [Fintype F]
    [Field k] [AddCommGroup V] [Module k V] (ι : F →+* k) (ρ : Representation k G V)
    (Y : F → G) (v₀ : V) :
    ∃ w : ℕ → V, ∀ t : F, ρ (Y t) v₀ =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • w j := by
  let _ : Module F V := Module.compHom V ι
  obtain ⟨c', hc'0, hc'⟩ := CFSG.RepresentationTheory.SL2NatSum.exists_coeff (K := F) (M := V)
    (fun t : F => ρ (Y t) v₀ - ρ (Y 0) v₀) (sub_self _)
  refine ⟨fun j => c' j + if j = 0 then ρ (Y 0) v₀ else 0, fun t => ?_⟩
  have hc't : ρ (Y t) v₀ - ρ (Y 0) v₀ =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • c' j := by
    have h := hc' t
    rw [show (∑ j ∈ Finset.range (Fintype.card F), t ^ j • c' j) =
        ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • c' j by
      refine Finset.sum_congr rfl fun j _ => ?_
      show ι (t ^ j) • c' j = (ι t) ^ j • c' j
      rw [map_pow]] at h
    exact h
  have hsum0 : (∑ j ∈ Finset.range (Fintype.card F),
      (ι t) ^ j • (if j = 0 then ρ (Y 0) v₀ else (0 : V))) = ρ (Y 0) v₀ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      rw [if_neg hb, smul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Fintype.card_pos)) h0
  calc ρ (Y t) v₀ = (ρ (Y t) v₀ - ρ (Y 0) v₀) + ρ (Y 0) v₀ := by abel
    _ = (∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • c' j) + ρ (Y 0) v₀ := by rw [hc't]
    _ = (∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • c' j) +
          (∑ j ∈ Finset.range (Fintype.card F),
            (ι t) ^ j • (if j = 0 then ρ (Y 0) v₀ else (0 : V))) := by rw [hsum0]
    _ = ∑ j ∈ Finset.range (Fintype.card F),
          (ι t) ^ j • (c' j + if j = 0 then ρ (Y 0) v₀ else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_add]

private theorem spCI_interp_coeff2 {G : Type*} [Group G] {F k V : Type*} [Field F] [Fintype F]
    [Field k] [AddCommGroup V] [Module k V] (ι : F →+* k) (ρ : Representation k G V)
    (X Y : F → G) (v₀ : V) (φ : Module.Dual k V) {c : ℕ} (hc : c < Fintype.card F)
    (hcoeff : ∀ s t : F, φ (ρ (X s * Y t) v₀) = (1 + ι s * ι t) ^ c) (w : ℕ → V)
    (hw1 : ∀ t : F, ρ (Y t) v₀ =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • w j) :
    ∀ (j : Fin (Fintype.card F)) (s : F),
      φ (ρ (X s) (w j.val)) = (Nat.choose c j.val : k) * (ι s) ^ j.val := by
  intro j s
  have hsum : ∀ t : F, ∑ i ∈ Finset.range (Fintype.card F),
      (ι t) ^ i • (φ (ρ (X s) (w i)) - (Nat.choose c i : k) * (ι s) ^ i) = 0 := by
    intro t
    have hbin : (1 + ι s * ι t) ^ c =
        ∑ i ∈ Finset.range (Fintype.card F), (ι s * ι t) ^ i * (c.choose i : k) := by
      have h1 : (1 + ι s * ι t) ^ c =
          ∑ i ∈ Finset.range (c + 1), (ι s * ι t) ^ i * (c.choose i : k) := by
        rw [show (1 + ι s * ι t) ^ c = (ι s * ι t + 1) ^ c by rw [add_comm]]
        rw [add_pow]
        simp
      rw [h1]
      refine Finset.sum_subset (fun i hi => Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hi; omega)) ?_
      intro i _ hi
      rw [Nat.choose_eq_zero_of_lt (by
        simp only [Finset.mem_range] at hi; omega), Nat.cast_zero, mul_zero]
    have hφ : (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • φ (ρ (X s) (w i))) =
        φ (ρ (X s) (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • w i)) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul]
    have hsplit : (∑ i ∈ Finset.range (Fintype.card F),
          (ι t) ^ i • (φ (ρ (X s) (w i)) - (Nat.choose c i : k) * (ι s) ^ i)) =
        (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • φ (ρ (X s) (w i))) -
          ∑ i ∈ Finset.range (Fintype.card F),
            (ι t) ^ i • ((Nat.choose c i : k) * (ι s) ^ i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
    rw [hsplit, hφ, ← hw1 t, act_mul, hcoeff s t, hbin, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
  exact sub_eq_zero.mp ((spCI_coeff_eq_zero (V := k) ι hsum) j.val j.isLt)

private theorem spCI_interp_hρ {G E : Type*} [Group G] [Group E] {F k V : Type*} [Field F]
    [Fintype F] [Field k] [AddCommGroup V] [Module k V] (ι : F →+* k)
    (ρ : Representation k G V) (τ : E →* G) (Y : F → G) (v₀ : V) (χ : E →* kˣ)
    (α : E →* Fˣ) (hweight : ∀ e : E, ρ (τ e) v₀ = (χ e : k) • v₀)
    (hconj : ∀ (e : E) (t : F), τ e * Y t * (τ e)⁻¹ = Y ((α e : F)⁻¹ * t)) (w : ℕ → V)
    (hw1 : ∀ t : F, ρ (Y t) v₀ =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • w j) (e : E) (t : F) :
    (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • ρ (τ e) (w i)) =
      (χ e : k) • (∑ i ∈ Finset.range (Fintype.card F),
        (ι ((α e : F)⁻¹ * t)) ^ i • w i) := by
  calc ∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • ρ (τ e) (w i)
      = ρ (τ e) (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • w i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    _ = ρ (τ e) (ρ (Y t) v₀) := by rw [hw1 t]
    _ = ρ (τ e * Y t) v₀ := by rw [act_mul]
    _ = ρ (Y ((α e : F)⁻¹ * t) * τ e) v₀ := by
          rw [show τ e * Y t = Y ((α e : F)⁻¹ * t) * τ e by
            rw [← mul_inv_eq_iff_eq_mul, hconj]]
    _ = ρ (Y ((α e : F)⁻¹ * t)) (ρ (τ e) v₀) := by rw [act_mul]
    _ = ρ (Y ((α e : F)⁻¹ * t)) ((χ e : k) • v₀) := by rw [hweight e]
    _ = (χ e : k) • ρ (Y ((α e : F)⁻¹ * t)) v₀ := by rw [map_smul]
    _ = (χ e : k) • (∑ i ∈ Finset.range (Fintype.card F),
          (ι ((α e : F)⁻¹ * t)) ^ i • w i) := by rw [hw1 ((α e : F)⁻¹ * t)]

private theorem spCI_interp_weight2 {G E : Type*} [Group G] [Group E] {F k V : Type*} [Field F]
    [Fintype F] [Field k] [AddCommGroup V] [Module k V] (ι : F →+* k)
    (ρ : Representation k G V) (τ : E →* G) (Y : F → G) (v₀ : V) (χ : E →* kˣ)
    (α : E →* Fˣ) (hweight : ∀ e : E, ρ (τ e) v₀ = (χ e : k) • v₀)
    (hconj : ∀ (e : E) (t : F), τ e * Y t * (τ e)⁻¹ = Y ((α e : F)⁻¹ * t)) (w : ℕ → V)
    (hw1 : ∀ t : F, ρ (Y t) v₀ =
      ∑ j ∈ Finset.range (Fintype.card F), (ι t) ^ j • w j) :
    ∀ (j : Fin (Fintype.card F)) (e : E),
      ρ (τ e) (w j.val) = ((χ e : k) * (ι (α e : F))⁻¹ ^ j.val) • w j.val := by
  intro j e
  have hsum : ∀ t : F, ∑ i ∈ Finset.range (Fintype.card F),
      (ι t) ^ i • (ρ (τ e) (w i) - ((χ e : k) * (ι (α e : F))⁻¹ ^ i) • w i) = 0 := by
    intro t
    have hρ := spCI_interp_hρ ι ρ τ Y v₀ χ α hweight hconj w hw1 e t
    have hsmul : (∑ i ∈ Finset.range (Fintype.card F),
          (ι t) ^ i • (((χ e : k) * (ι (α e : F))⁻¹ ^ i) • w i)) =
        (χ e : k) • (∑ i ∈ Finset.range (Fintype.card F),
          (ι ((α e : F)⁻¹ * t)) ^ i • w i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [smul_smul]
        congr 1
        rw [map_mul, map_inv₀, mul_pow]
        ring
    have hsplit : (∑ i ∈ Finset.range (Fintype.card F),
          (ι t) ^ i • (ρ (τ e) (w i) - ((χ e : k) * (ι (α e : F))⁻¹ ^ i) • w i)) =
        (∑ i ∈ Finset.range (Fintype.card F), (ι t) ^ i • ρ (τ e) (w i)) -
          ∑ i ∈ Finset.range (Fintype.card F),
            (ι t) ^ i • (((χ e : k) * (ι (α e : F))⁻¹ ^ i) • w i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
    rw [hsplit, hρ, hsmul, sub_self]
  exact sub_eq_zero.mp ((spCI_coeff_eq_zero ι hsum) j.val j.isLt)

theorem exists_root_interpolation {G E : Type*} [Group G] [Group E] {F k V : Type*} [Field F]
    [Fintype F] [Field k] [AddCommGroup V] [Module k V] (ι : F →+* k)
    (ρ : Representation k G V) (τ : E →* G) (X Y : F → G) (v₀ : V) (φ : Module.Dual k V)
    (χ : E →* kˣ) (α : E →* Fˣ) {c : ℕ} (hc : c < Fintype.card F)
    (hweight : ∀ e : E, ρ (τ e) v₀ = (χ e : k) • v₀)
    (hconj : ∀ (e : E) (t : F), τ e * Y t * (τ e)⁻¹ = Y ((α e : F)⁻¹ * t))
    (hcoeff : ∀ s t : F, φ (ρ (X s * Y t) v₀) = (1 + ι s * ι t) ^ c) :
    ∃ w : Fin (Fintype.card F) → V,
      (∀ t : F, ρ (Y t) v₀ = ∑ j, (ι t) ^ j.val • w j) ∧
      (∀ (j : Fin (Fintype.card F)) (s : F),
        φ (ρ (X s) (w j)) = (Nat.choose c j.val : k) * (ι s) ^ j.val) ∧
      (∀ (j : Fin (Fintype.card F)) (e : E),
        ρ (τ e) (w j) = ((χ e : k) * (ι (α e : F))⁻¹ ^ j.val) • w j) ∧
      (∀ j : Fin (Fintype.card F), (Nat.choose c j.val : k) ≠ 0 → w j ≠ 0) := by
  obtain ⟨w, hw1'⟩ := spCI_interp_w ι ρ Y v₀
  have hw1 : ∀ t : F, ρ (Y t) v₀ = ∑ j : Fin (Fintype.card F), (ι t) ^ j.val • w j.val := by
    intro t
    rw [Fin.sum_univ_eq_sum_range (fun j => (ι t) ^ j • w j) (Fintype.card F)]
    exact hw1' t
  have hcoeff2 := spCI_interp_coeff2 ι ρ X Y v₀ φ hc hcoeff w hw1'
  have hweight2 := spCI_interp_weight2 ι ρ τ Y v₀ χ α hweight hconj w hw1'
  have hneq : ∀ j : Fin (Fintype.card F), (Nat.choose c j.val : k) ≠ 0 → w j.val ≠ 0 := by
    intro j hj hw0
    have h := hcoeff2 j 1
    rw [hw0, map_zero, map_zero] at h
    simp only [map_one, one_pow, mul_one] at h
    exact hj h.symm
  exact ⟨fun j => w j.val, hw1, hcoeff2, hweight2, hneq⟩

theorem curtis_root_interpolation {G : Type} [Group G] (H : Subgroup G)
    {F k V : Type} [Field F] [Fintype F] [Field k] [AddCommGroup V] [Module k V]
    (ι : F →+* k) (ρ : Representation k G V) (X Y : F → G)
    (v₀ : V) (φ : Module.Dual k V) (χ : H →* kˣ) (α : H →* Fˣ)
    {c : ℕ} (hc : c < Fintype.card F)
    (hweight : ∀ h : H, ρ (h : G) v₀ = (χ h : k) • v₀)
    (hconj : ∀ (h : H) (t : F),
      (h : G) * Y t * (h : G)⁻¹ = Y ((α h : F)⁻¹ * t))
    (hcoeff : ∀ s t : F,
      φ (ρ (X s * Y t) v₀) = (1 + ι s * ι t) ^ c) :
    ∃ w : Fin (Fintype.card F) → V,
      (∀ t : F, ρ (Y t) v₀ = ∑ j, (ι t) ^ j.val • w j) ∧
      (∀ (j : Fin (Fintype.card F)) (s : F),
        φ (ρ (X s) (w j)) = (Nat.choose c j.val : k) * (ι s) ^ j.val) ∧
      (∀ (j : Fin (Fintype.card F)) (h : H),
        ρ (h : G) (w j) = ((χ h : k) * (ι (α h : F))⁻¹ ^ j.val) • w j) ∧
      (∀ j : Fin (Fintype.card F), (Nat.choose c j.val : k) ≠ 0 → w j ≠ 0) := by
  exact exists_root_interpolation ι ρ H.subtype X Y v₀ φ χ α hc hweight hconj hcoeff

theorem mem_weightSpace_of_isCurtisType {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    {D : CurtisDatum G cs p} {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {y₀ : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y₀ χ μ) {E : Type*} [Group E] (τ : E →* G) (hτ : ∀ e, τ e ∈ D.H)
    (ψ : E →* kˣ) (hψ : ∀ e, (ψ e : k) = χ (τ e)) : y₀ ∈ weightSpace (ρ.comp τ) ψ := by
  rw [mem_weightSpace]
  intro e
  change ρ (τ e) y₀ = (ψ e : k) • y₀
  rw [hψ e, ht.2.2.1 (τ e) (hτ e)]

theorem exists_ne_zero_mem_weightSpace_of_choose {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    {D : CurtisDatum G cs p} {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {y₀ : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V} (hf : ∀ z ∈ augSub ρ D.L, f z = 0)
    (hfy : f y₀ = 1) {K : Type*} [Field K] [Finite K] (ι : K →+* k)
    (σ : SL(2, K) →* G) {s : B} (hU : ∀ c, σ (sl2Upper c) ∈ D.U)
    (hL : ∀ c, σ (sl2Lower c) ∈ D.L) (hH : ∀ u, σ (diagUnit u) ∈ D.H)
    (hn : ∃ h ∈ D.H, σ (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) = D.n s * h)
    (hμ : μ s = D.dScalar χ s) {c : ℕ} (hc : 1 ≤ c) (hcq : c < Nat.card K)
    (hχ : ∀ u : Kˣ, χ (σ (diagUnit u)) = ι (u : K) ^ c) {E : Type*} [Group E] (τ : E →* G)
    (hτ : ∀ e, τ e ∈ D.H) (α : E →* Kˣ)
    (hα : ∀ e t, τ e * σ (sl2Lower t) * (τ e)⁻¹ = σ (sl2Lower ((α e : K) * t))) (ψ : E →* kˣ)
    (hψ : ∀ e, (ψ e : k) = χ (τ e)) {j : ℕ} (hjq : j < Nat.card K)
    (hchoose : (c.choose j : k) ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ v ∈ weightSpace (ρ.comp τ) (ψ * ((Units.map ι.toMonoidHom).comp α) ^ j) := by
  let _ : Fintype K := Fintype.ofFinite K
  have hcq' : c < Fintype.card K := by simpa only [Nat.card_eq_fintype_card] using hcq
  have hjq' : j < Fintype.card K := by simpa only [Nat.card_eq_fintype_card] using hjq
  have hweight : ∀ e : E, ρ (τ e) y₀ = (ψ e : k) • y₀ :=
    fun e => (mem_weightSpace (ρ.comp τ) ψ y₀).mp
      (mem_weightSpace_of_isCurtisType ht τ hτ ψ hψ) e
  have hconj : ∀ (e : E) (t : K), τ e * σ (sl2Lower t) * (τ e)⁻¹ =
      σ (sl2Lower (((α⁻¹ : E →* Kˣ) e : K)⁻¹ * t)) := by
    intro e t
    rw [hα e t]
    simp [MonoidHom.inv_apply]
  have hcoeff : ∀ s t : K, f (ρ (σ (sl2Upper s) * σ (sl2Lower t)) y₀) =
      (1 + ι s * ι t) ^ c :=
    fun s t => form_sl2Upper_mul_sl2Lower ht hf hfy ι σ hU hL hH hn hμ hc hχ s t
  obtain ⟨w, -, -, hw3, hw4⟩ := exists_root_interpolation ι ρ τ
    (fun s => σ (sl2Upper s)) (fun t => σ (sl2Lower t)) y₀ f ψ (α⁻¹) hcq' hweight hconj hcoeff
  refine ⟨w ⟨j, hjq'⟩, hw4 ⟨j, hjq'⟩ (by simpa using hchoose), ?_⟩
  rw [mem_weightSpace]
  intro e
  change ρ (τ e) (w ⟨j, hjq'⟩) =
    ((ψ * ((Units.map ι.toMonoidHom).comp α) ^ j) e : k) • w ⟨j, hjq'⟩
  rw [hw3 ⟨j, hjq'⟩ e]
  congr 1
  simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.coe_map,
    MonoidHom.inv_apply, map_inv₀, inv_inv]

private theorem spCI_sum_pow_card_sub_one {K : Type*} [Field K] [Fintype K] :
    ∑ t : K, t ^ (Fintype.card K - 1) = -1 := by
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {(0 : K)} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact Units.ne_zero y
    · intro hx
      exact ⟨Units.mk0 x hx, Units.val_mk0 hx⟩
  calc ∑ t : K, t ^ (Fintype.card K - 1)
      = ∑ t ∈ Finset.univ \ {(0 : K)}, t ^ (Fintype.card K - 1) := by
        rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ (0 : K))),
          Finset.sum_singleton, zero_pow (by omega : Fintype.card K - 1 ≠ 0), add_zero]
    _ = ∑ t : Kˣ, ((t : K) ^ (Fintype.card K - 1)) := by
        rw [← hmap, Finset.sum_map]
        rfl
    _ = -1 := by
        rw [FiniteField.sum_pow_units]
        simp

private theorem spCI_sum_pow_add {K : Type*} [Field K] [Fintype K] {r : ℕ} (hr : 0 < r)
    (hrq : r < Fintype.card K - 1) :
    ∑ t : K, t ^ (Fintype.card K - 1 + r) = 0 := by
  have h : (∑ t : K, t ^ (Fintype.card K - 1 + r)) = ∑ t : K, t ^ r := by
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t = 0
    · subst ht
      rw [zero_pow (by omega : Fintype.card K - 1 + r ≠ 0), zero_pow hr.ne']
    · rw [pow_add, FiniteField.pow_card_sub_one_eq_one t ht, one_mul]
  rw [h]
  exact FiniteField.sum_pow_lt_card_sub_one K r hrq

private theorem spCI_sum_pow {K : Type*} [Field K] [Fintype K] {m : ℕ} (_hm : 0 < m)
    (hmq : m < 2 * (Fintype.card K - 1)) :
    ∑ t : K, t ^ m = if m = Fintype.card K - 1 then -1 else 0 := by
  by_cases h : m = Fintype.card K - 1
  · rw [if_pos h, h]; exact spCI_sum_pow_card_sub_one
  · rw [if_neg h]
    by_cases hlt : m < Fintype.card K - 1
    · exact FiniteField.sum_pow_lt_card_sub_one K m hlt
    · have hgt : Fintype.card K - 1 < m := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
      obtain ⟨r, hr⟩ : ∃ r, m = Fintype.card K - 1 + r := ⟨m - (Fintype.card K - 1), by omega⟩
      rw [hr]
      exact spCI_sum_pow_add (by omega) (by omega)

theorem sum_pow_mul_one_add_pow {K : Type*} [Field K] [Fintype K] {j c : ℕ} (hj : 1 ≤ j)
    (hjq : j + 1 < Nat.card K) (hc : c < Nat.card K) :
    ∑ t : K, t ^ (Nat.card K - 1 - j) * (1 + t) ^ c = -(c.choose j : K) := by
  rw [Nat.card_eq_fintype_card]
  have hjq' : j + 1 < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]; exact hjq
  have hc' : c < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]; exact hc
  have hexp : ∀ t : K, (1 + t) ^ c =
      ∑ i ∈ Finset.range (c + 1), t ^ i * (c.choose i : K) := by
    intro t
    rw [add_comm 1 t, add_pow]
    simp
  calc ∑ t : K, t ^ (Fintype.card K - 1 - j) * (1 + t) ^ c
      = ∑ t : K, t ^ (Fintype.card K - 1 - j) *
          ∑ i ∈ Finset.range (c + 1), t ^ i * (c.choose i : K) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hexp t]
    _ = ∑ t : K, ∑ i ∈ Finset.range (c + 1),
          (t ^ (Fintype.card K - 1 - j) * t ^ i) * (c.choose i : K) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i ∈ Finset.range (c + 1), ∑ t : K,
          (t ^ (Fintype.card K - 1 - j) * t ^ i) * (c.choose i : K) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (c + 1), (c.choose i : K) *
          ∑ t : K, t ^ (Fintype.card K - 1 - j + i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← pow_add]
        ring
    _ = (c.choose j : K) * (∑ t : K, t ^ (Fintype.card K - 1)) := by
        refine (Finset.sum_eq_single j ?_ ?_).trans ?_
        · intro i hi hij
          have hm : 0 < Fintype.card K - 1 - j + i := by
            have := Finset.mem_range.mp hi; omega
          have hmq : Fintype.card K - 1 - j + i < 2 * (Fintype.card K - 1) := by
            have := Finset.mem_range.mp hi; omega
          rw [spCI_sum_pow hm hmq, if_neg (by rintro h; exact hij (by omega)), mul_zero]
        · intro hj'
          rw [Nat.choose_eq_zero_of_lt (by
            simp only [Finset.mem_range] at hj'; omega), Nat.cast_zero, zero_mul]
        · rw [show Fintype.card K - 1 - j + j = Fintype.card K - 1 by omega]
    _ = (c.choose j : K) * (-1) := by rw [spCI_sum_pow_card_sub_one]
    _ = -(c.choose j : K) := by ring

end CFSG.LocalAnalysis.WeakClosure81
