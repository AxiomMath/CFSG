module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowLin
import CFSG.LocalAnalysis.StandardType.GGNineDepRestrictAux
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Ring.Parity

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggNineDepRowLinAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private noncomputable def ggNineDepRowLinAux_flipL {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) :
    M →ₗ[ZMod 3] M :=
  LinearMap.id - (2 : ZMod 3) • ∑ i ∈ S, (fb.coord i).smulRight (fb i)

private lemma ggNineDepRowLinAux_flipL_apply_fb {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) (k : Fin d) :
    ggNineDepRowLinAux_flipL fb S (fb k) = if k ∈ S then -fb k else fb k := by
  simp only [ggNineDepRowLinAux_flipL, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hc : ∀ i, fb.coord i (fb k) = if i = k then 1 else 0 := by
    intro i
    by_cases h : i = k
    · subst h; simp [Basis.coord_apply]
    · simp [Basis.coord_apply, h]
  simp only [hc]
  have hsum : ∑ x ∈ S, (if x = k then (1 : ZMod 3) else 0) • fb x =
      if k ∈ S then fb k else 0 := by
    by_cases hk : k ∈ S
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro x _ hxk; simp [hxk]
      · intro h; exact absurd hk h
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro x hx
      have hxk : x ≠ k := fun h => hk (h ▸ hx)
      simp [hxk]
  rw [hsum]
  by_cases hk : k ∈ S
  · simp only [hk, if_true]
    module
  · simp [hk]

private lemma ggNineDepRowLinAux_flipL_det {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] [Module.Finite (ZMod 3) M]
    (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) :
    LinearMap.det (ggNineDepRowLinAux_flipL fb S) =
      ∏ k : Fin d, (if k ∈ S then (-1 : ZMod 3) else 1) := by
  rw [← LinearMap.det_toMatrix fb (ggNineDepRowLinAux_flipL fb S)]
  have hmat : LinearMap.toMatrix fb fb (ggNineDepRowLinAux_flipL fb S) =
      Matrix.diagonal (fun k : Fin d => if k ∈ S then (-1 : ZMod 3) else 1) := by
    ext k j
    rw [LinearMap.toMatrix_apply, ggNineDepRowLinAux_flipL_apply_fb, Matrix.diagonal_apply]
    by_cases hkj : k = j
    · subst hkj
      by_cases hk : k ∈ S <;> simp [hk]
    · by_cases hj : j ∈ S <;> simp [hkj, hj]
  rw [hmat, Matrix.det_diagonal]

private lemma ggNineDepRowLinAux_hflip {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) (y : M) :
    ggNineDepRowLinAux_flipL fb S (ggNineDepRowLinAux_flipL fb S y) = y := by
  have hcomp : (ggNineDepRowLinAux_flipL fb S).comp (ggNineDepRowLinAux_flipL fb S) =
      LinearMap.id := by
    apply fb.ext
    intro k
    rw [LinearMap.comp_apply, ggNineDepRowLinAux_flipL_apply_fb, LinearMap.id_apply]
    by_cases hk : k ∈ S
    · rw [if_pos hk, map_neg, ggNineDepRowLinAux_flipL_apply_fb, if_pos hk, neg_neg]
    · rw [if_neg hk, ggNineDepRowLinAux_flipL_apply_fb, if_neg hk]
  have h := LinearMap.congr_fun hcomp y
  simpa [LinearMap.comp_apply] using h

private noncomputable def ggNineDepRowLinAux_flip {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) :
    M ≃ₗ[ZMod 3] M where
  toFun := ggNineDepRowLinAux_flipL fb S
  invFun := ggNineDepRowLinAux_flipL fb S
  map_add' := (ggNineDepRowLinAux_flipL fb S).map_add
  map_smul' := (ggNineDepRowLinAux_flipL fb S).map_smul
  left_inv := ggNineDepRowLinAux_hflip fb S
  right_inv := ggNineDepRowLinAux_hflip fb S

private lemma ggNineDepRowLinAux_flip_apply_fb {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) (k : Fin d) :
    ggNineDepRowLinAux_flip fb S (fb k) = if k ∈ S then -fb k else fb k :=
  ggNineDepRowLinAux_flipL_apply_fb fb S k

private lemma ggNineDepRowLinAux_flip_comm {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S T : Finset (Fin d)) :
    ggNineDepRowLinAux_flip fb S * ggNineDepRowLinAux_flip fb T =
      ggNineDepRowLinAux_flip fb T * ggNineDepRowLinAux_flip fb S := by
  apply LinearEquiv.ext
  intro y
  have key : ∀ k : Fin d,
      (ggNineDepRowLinAux_flip fb S) ((ggNineDepRowLinAux_flip fb T) (fb k)) =
      (ggNineDepRowLinAux_flip fb T) ((ggNineDepRowLinAux_flip fb S) (fb k)) := by
    intro k
    rw [ggNineDepRowLinAux_flip_apply_fb fb T k, ggNineDepRowLinAux_flip_apply_fb fb S k]
    by_cases hT : k ∈ T <;> by_cases hS : k ∈ S <;>
      simp [hT, hS, map_neg, ggNineDepRowLinAux_flip_apply_fb]
  have hlin : ((ggNineDepRowLinAux_flip fb S * ggNineDepRowLinAux_flip fb T : M ≃ₗ[ZMod 3] M) :
        M →ₗ[ZMod 3] M) =
      ((ggNineDepRowLinAux_flip fb T * ggNineDepRowLinAux_flip fb S : M ≃ₗ[ZMod 3] M) :
        M →ₗ[ZMod 3] M) := by
    apply fb.ext
    intro k
    change (ggNineDepRowLinAux_flip fb S) ((ggNineDepRowLinAux_flip fb T) (fb k)) =
      (ggNineDepRowLinAux_flip fb T) ((ggNineDepRowLinAux_flip fb S) (fb k))
    exact key k
  exact LinearMap.congr_fun hlin y

private lemma ggNineDepRowLinAux_flip_fix_coord {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) {t : M}
    (ht : ggNineDepRowLinAux_flip fb S t = t) {k : Fin d} (hk : k ∈ S) : fb.coord k t = 0 := by
  have h : ggNineDepRowLinAux_flipL fb S t = t := ht
  rw [ggNineDepRowLinAux_flipL] at h
  have h2 : (2 : ZMod 3) • (∑ i ∈ S, (fb.coord i t) • fb i) = 0 := by
    have hh := congrArg (fun z => z - t) h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
  have hsum0 : (∑ i ∈ S, (fb.coord i t) • fb i) = 0 := by
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ggNineDepRowLinAux_two_ne_zero
    · exact h3
  have h3 := congrArg (fb.coord k) hsum0
  rw [map_sum, map_zero] at h3
  simp only [map_smul, smul_eq_mul] at h3
  have hc : ∀ i, fb.coord k (fb i) = if i = k then 1 else 0 := by
    intro i
    by_cases h : i = k
    · subst h; simp [Basis.coord_apply]
    · simp [Basis.coord_apply, h]
  simp only [hc] at h3
  have hsum_eq : ∑ i ∈ S, (fb.coord i t) * (if i = k then (1 : ZMod 3) else 0) =
      fb.coord k t := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik]
    · intro hk'; exact absurd hk hk'
  rw [hsum_eq] at h3
  exact h3

private lemma ggNineDepRowLinAux_flip_fix_both {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) {S T : Finset (Fin d)}
    (hcover : S ∪ T = Finset.univ) {t : M}
    (h1 : ggNineDepRowLinAux_flip fb S t = t) (h2 : ggNineDepRowLinAux_flip fb T t = t) :
    t = 0 := by
  rw [← fb.forall_coord_eq_zero_iff]
  intro k
  have hk : k ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ k
  rcases Finset.mem_union.mp hk with hk1 | hk2
  · exact ggNineDepRowLinAux_flip_fix_coord fb S h1 hk1
  · exact ggNineDepRowLinAux_flip_fix_coord fb T h2 hk2

private lemma ggNineDepRowLinAux_flip_det_even {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] [Module.Finite (ZMod 3) M]
    (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) (hS : Even S.card) :
    (LinearEquiv.det (ggNineDepRowLinAux_flip fb S) : ZMod 3) = 1 := by
  rw [LinearEquiv.coe_det]
  change LinearMap.det (ggNineDepRowLinAux_flipL fb S) = 1
  rw [ggNineDepRowLinAux_flipL_det]
  have h1 : ∏ k : Fin d, (if k ∈ S then (-1 : ZMod 3) else 1) = (-1 : ZMod 3) ^ S.card := by
    rw [← Finset.prod_filter (fun k => k ∈ S) (fun _ => (-1 : ZMod 3))]
    rw [Finset.prod_const]
    congr 1
    simp
  rw [h1, hS.neg_one_pow]

private lemma ggNineDepRowLinAux_flip_sq {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) :
    ggNineDepRowLinAux_flip fb S * ggNineDepRowLinAux_flip fb S = 1 := by
  apply LinearEquiv.ext
  intro y
  exact ggNineDepRowLinAux_hflip fb S y

private lemma ggNineDepRowLinAux_sup_fix {M : Type} [AddCommGroup M] [Module (ZMod 3) M]
    (S : Submodule (ZMod 3) M) (a b : M ≃ₗ[ZMod 3] M)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (haS : ∀ v, a v - v ∈ S) (hbS : ∀ v, b v - v ∈ S) :
    S ⊔ ggLinFix ({a, b} : Set (M ≃ₗ[ZMod 3] M)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  let Pa : M := (2 : ZMod 3)⁻¹ • (v + a v)
  let w : M := (2 : ZMod 3)⁻¹ • (Pa + b Pa)
  have htwo : (2 : ZMod 3)⁻¹ + (2 : ZMod 3)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ ggNineDepRowLinAux_two_ne_zero]
  have hce_a : (2 : ZMod 3)⁻¹ • v + (2 : ZMod 3)⁻¹ • v = v := by
    rw [← add_smul, htwo, one_smul]
  have hce_Pa : (2 : ZMod 3)⁻¹ • Pa + (2 : ZMod 3)⁻¹ • Pa = Pa := by
    rw [← add_smul, htwo, one_smul]
  have haa : a (a v) = v := by
    have h := congrArg (fun e : M ≃ₗ[ZMod 3] M => e v) ha
    simpa using h
  have hbb : b (b Pa) = Pa := by
    have h := congrArg (fun e : M ≃ₗ[ZMod 3] M => e Pa) hb
    simpa using h
  have hPa_fix : a Pa = Pa := by
    dsimp [Pa]
    rw [map_smul, map_add, haa, add_comm]
  have haPa : a (b Pa) = b Pa := by
    have hcomm : a (b Pa) = b (a Pa) := by
      have h := congrArg (fun e : M ≃ₗ[ZMod 3] M => e Pa) hab
      simpa [LinearEquiv.mul_apply] using h
    rw [hcomm, hPa_fix]
  have hw_fix_a : a w = w := by
    dsimp [w]
    rw [map_smul, map_add, hPa_fix, haPa]
  have hw_fix_b : b w = w := by
    dsimp [w]
    rw [map_smul, map_add, hbb, add_comm]
  have hw_mem : w ∈ ggLinFix ({a, b} : Set (M ≃ₗ[ZMod 3] M)) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hw_fix_a
    · exact hw_fix_b
  have hvsub : v - Pa ∈ S := by
    have h : v - Pa = (2 : ZMod 3)⁻¹ • (v - a v) := by
      dsimp [Pa]
      rw [smul_add, smul_sub]
      calc v - ((2 : ZMod 3)⁻¹ • v + (2 : ZMod 3)⁻¹ • (a v))
          = ((2 : ZMod 3)⁻¹ • v + (2 : ZMod 3)⁻¹ • v)
              - ((2 : ZMod 3)⁻¹ • v + (2 : ZMod 3)⁻¹ • (a v)) := by rw [hce_a]
        _ = (2 : ZMod 3)⁻¹ • v - (2 : ZMod 3)⁻¹ • (a v) := by abel
    rw [h]
    exact S.smul_mem _ (by simpa using S.neg_mem (haS v))
  have hPaw : Pa - w ∈ S := by
    have h : Pa - w = (2 : ZMod 3)⁻¹ • (Pa - b Pa) := by
      dsimp [w]
      rw [smul_add, smul_sub]
      calc Pa - ((2 : ZMod 3)⁻¹ • Pa + (2 : ZMod 3)⁻¹ • (b Pa))
          = ((2 : ZMod 3)⁻¹ • Pa + (2 : ZMod 3)⁻¹ • Pa)
              - ((2 : ZMod 3)⁻¹ • Pa + (2 : ZMod 3)⁻¹ • (b Pa)) := by rw [hce_Pa]
        _ = (2 : ZMod 3)⁻¹ • Pa - (2 : ZMod 3)⁻¹ • (b Pa) := by abel
    rw [h]
    exact S.smul_mem _ (by simpa using S.neg_mem (hbS Pa))
  have hvw : v - w ∈ S := by
    have h : v - w = (v - Pa) + (Pa - w) := by abel
    rw [h]
    exact S.add_mem hvsub hPaw
  exact Submodule.mem_sup.mpr ⟨v - w, hvw, w, hw_mem, by abel⟩

private lemma ggNineDepRowLinAux_inf_fix {M : Type} [AddCommGroup M] [Module (ZMod 3) M]
    (S : Submodule (ZMod 3) M) (a b : M ≃ₗ[ZMod 3] M)
    (hfix : ∀ t ∈ S, a t = t → b t = t → t = 0) :
    S ⊓ ggLinFix ({a, b} : Set (M ≃ₗ[ZMod 3] M)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  obtain ⟨htS, htfix⟩ := Submodule.mem_inf.mp ht
  exact hfix t htS (htfix a (by simp)) (htfix b (by simp))

private lemma ggNineDepRowLinAux_flip_coord {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d)) (k : Fin d)
    (t : M) :
    fb.coord k (ggNineDepRowLinAux_flip fb S t) =
      (if k ∈ S then (-1 : ZMod 3) else 1) * fb.coord k t := by
  have h : ggNineDepRowLinAux_flip fb S t =
      t - (2 : ZMod 3) • (∑ i ∈ S, (fb.coord i t) • fb i) := by
    change ggNineDepRowLinAux_flipL fb S t = _
    rw [ggNineDepRowLinAux_flipL]
    simp [LinearMap.sub_apply]
  rw [h, map_sub, map_smul, smul_eq_mul]
  have hc : ∀ i, fb.coord k (fb i) = if i = k then 1 else 0 := by
    intro i
    by_cases h : i = k
    · subst h; simp [Basis.coord_apply]
    · simp [Basis.coord_apply, h]
  have hsum : fb.coord k (∑ i ∈ S, (fb.coord i t) • fb i) =
      if k ∈ S then fb.coord k t else 0 := by
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, hc]
    by_cases hk : k ∈ S
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [hik]
      · intro h; exact absurd hk h
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro i hi
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      simp [hik]
  rw [hsum]
  by_cases hk : k ∈ S
  · simp only [hk, if_true]
    ring_nf
  · simp [hk]

private lemma ggNineDepRowLinAux_transvection_comm_flip {d : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod 3) M] (fb : Basis (Fin d) (ZMod 3) M) (S : Finset (Fin d))
    {i0 i1 : Fin d} (h01 : (i0 ∈ S) ↔ (i1 ∈ S))
    (hfv : fb.coord i1 (fb i0) = 0) :
    LinearEquiv.transvection hfv * ggNineDepRowLinAux_flip fb S =
      ggNineDepRowLinAux_flip fb S * LinearEquiv.transvection hfv := by
  apply LinearEquiv.ext
  intro y
  have hlin : ((LinearEquiv.transvection hfv * ggNineDepRowLinAux_flip fb S : M ≃ₗ[ZMod 3] M) :
        M →ₗ[ZMod 3] M) =
      ((ggNineDepRowLinAux_flip fb S * LinearEquiv.transvection hfv : M ≃ₗ[ZMod 3] M) :
        M →ₗ[ZMod 3] M) := by
    apply fb.ext
    intro k
    change LinearEquiv.transvection hfv (ggNineDepRowLinAux_flip fb S (fb k)) =
      ggNineDepRowLinAux_flip fb S (LinearEquiv.transvection hfv (fb k))
    rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply]
    rw [map_add, map_smul, ggNineDepRowLinAux_flip_apply_fb fb S i0,
      ggNineDepRowLinAux_flip_coord fb S i1 (fb k)]
    have hck : fb.coord i1 (fb k) = if k = i1 then 1 else 0 := by
      by_cases h : k = i1
      · subst h; simp [Basis.coord_apply]
      · simp [Basis.coord_apply, h]
    rw [hck]
    by_cases hk1 : k = i1
    · rw [if_pos hk1]
      by_cases hS1 : i1 ∈ S
      · have hS0 : i0 ∈ S := h01.mpr hS1
        simp only [hS1, hS0, if_true]
        module
      · have hS0 : i0 ∉ S := fun h => hS1 (h01.mp h)
        simp only [hS1, hS0, if_false]
        module
    · rw [if_neg hk1]
      simp
  exact LinearMap.congr_fun hlin y

private theorem ggNineDepRowLinAux_main
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}
    (X : GGNineDepCtx h α r s x)
    (hQ : ∀ g : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s),
      LinearEquiv.det g = 1 → g ∈ ggNineQ X)
    {d : ℕ} (fb : Basis (Fin d) (ZMod 3) ↥(ggFixLineT r s))
    (i0 i1 : Fin d) (hi01 : i0 ≠ i1)
    (S1 S2 : Finset (Fin d)) (hS1 : Even S1.card) (hS2 : Even S2.card)
    (hcover : S1 ∪ S2 = Finset.univ)
    (h01_1 : (i0 ∈ S1) ↔ (i1 ∈ S1))
    (h01_2 : (i0 ∈ S2) ↔ (i1 ∈ S2)) : False := by
  classical
  let Tr := ggFixLineT r s
  let A := ggLargeGrp r s
  let ρ : ↥A →* (↥Tr ≃ₗ[ZMod 3] ↥Tr) := ggLargeRho r s X.hA
  have hρinj : Function.Injective ρ := X.restr.1
  have hfinV : Module.Finite (ZMod 3) V := l04nD2_finite X.case
  have hfinTr : Module.Finite (ZMod 3) ↥Tr :=
    Module.Finite.of_injective Tr.subtype Subtype.val_injective
  have hdispA : ∀ g ∈ A, ∀ v : V, g v - v ∈ Tr :=
    fun g hg v => l04nD2_disp X.case g hg v
  have hR_apply : ∀ (a : ↥A) (y : ↥Tr),
      (a : V ≃ₗ[ZMod 3] V) (y : V) = (((ρ a) y : ↥Tr) : V) := by
    intro a y
    have hh := l04nD2_restrict_apply (V := V) Tr (Subgroup.inclusion X.hA a) y
    simpa [ρ, ggLargeRho, Subgroup.coe_inclusion] using hh.symm
  let δ1 : ↥Tr ≃ₗ[ZMod 3] ↥Tr := ggNineDepRowLinAux_flip fb S1
  let δ2 : ↥Tr ≃ₗ[ZMod 3] ↥Tr := ggNineDepRowLinAux_flip fb S2
  have hδ1det : LinearEquiv.det δ1 = 1 := by
    apply Units.ext
    simpa [δ1] using ggNineDepRowLinAux_flip_det_even fb S1 hS1
  have hδ2det : LinearEquiv.det δ2 = 1 := by
    apply Units.ext
    simpa [δ2] using ggNineDepRowLinAux_flip_det_even fb S2 hS2
  have hδ1Q : δ1 ∈ ggNineQ X := hQ δ1 hδ1det
  have hδ2Q : δ2 ∈ ggNineQ X := hQ δ2 hδ2det
  change δ1 ∈ ρ.range at hδ1Q
  change δ2 ∈ ρ.range at hδ2Q
  obtain ⟨d1, hd1⟩ := MonoidHom.mem_range.mp hδ1Q
  obtain ⟨d2, hd2⟩ := MonoidHom.mem_range.mp hδ2Q
  have hδ1sq : δ1 * δ1 = 1 := by simpa [δ1] using ggNineDepRowLinAux_flip_sq fb S1
  have hδ2sq : δ2 * δ2 = 1 := by simpa [δ2] using ggNineDepRowLinAux_flip_sq fb S2
  have hδ12 : δ1 * δ2 = δ2 * δ1 := by
    simpa [δ1, δ2] using ggNineDepRowLinAux_flip_comm fb S1 S2
  have hd1sq : d1 * d1 = 1 := by
    apply hρinj
    rw [map_mul, hd1, hδ1sq, map_one]
  have hd2sq : d2 * d2 = 1 := by
    apply hρinj
    rw [map_mul, hd2, hδ2sq, map_one]
  have hd12 : d1 * d2 = d2 * d1 := by
    apply hρinj
    rw [map_mul, map_mul, hd1, hd2, hδ12]
  have hfv : fb.coord i1 (fb i0) = 0 := by
    rw [Basis.coord_apply, Basis.repr_self_apply, if_neg hi01]
  let u : ↥Tr ≃ₗ[ZMod 3] ↥Tr := LinearEquiv.transvection hfv
  have hu_apply : ∀ y : ↥Tr, u y = y + fb.coord i1 y • fb i0 :=
    fun y => LinearEquiv.transvection.apply hfv y
  have hu_det : LinearEquiv.det u = 1 := LinearEquiv.transvection.det_eq_one hfv
  have huQ : u ∈ ggNineQ X := hQ u hu_det
  change u ∈ ρ.range at huQ
  obtain ⟨uhat, huhat⟩ := MonoidHom.mem_range.mp huQ
  have hu_comm_δ1 : u * δ1 = δ1 * u := by
    simpa [u, δ1] using ggNineDepRowLinAux_transvection_comm_flip fb S1 h01_1 hfv
  have hu_comm_δ2 : u * δ2 = δ2 * u := by
    simpa [u, δ2] using ggNineDepRowLinAux_transvection_comm_flip fb S2 h01_2 hfv
  have huhat_d1 : uhat * d1 = d1 * uhat := by
    apply hρinj
    rw [map_mul, map_mul, huhat, hd1, hu_comm_δ1]
  have huhat_d2 : uhat * d2 = d2 * uhat := by
    apply hρinj
    rw [map_mul, map_mul, huhat, hd2, hu_comm_δ2]
  have hd1sqV : (d1 : V ≃ₗ[ZMod 3] V) * (d1 : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod 3] V)) hd1sq
  have hd2sqV : (d2 : V ≃ₗ[ZMod 3] V) * (d2 : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod 3] V)) hd2sq
  have hd12V : (d1 : V ≃ₗ[ZMod 3] V) * (d2 : V ≃ₗ[ZMod 3] V) =
      (d2 : V ≃ₗ[ZMod 3] V) * (d1 : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod 3] V)) hd12
  have hd1disp : ∀ v : V, (d1 : V ≃ₗ[ZMod 3] V) v - v ∈ Tr :=
    fun v => hdispA d1.1 d1.2 v
  have hd2disp : ∀ v : V, (d2 : V ≃ₗ[ZMod 3] V) v - v ∈ Tr :=
    fun v => hdispA d2.1 d2.2 v
  let W : Submodule (ZMod 3) V :=
    ggLinFix ({(d1 : V ≃ₗ[ZMod 3] V), (d2 : V ≃ₗ[ZMod 3] V)} : Set (V ≃ₗ[ZMod 3] V))
  have hsup : Tr ⊔ W = ⊤ :=
    ggNineDepRowLinAux_sup_fix Tr (d1 : V ≃ₗ[ZMod 3] V) (d2 : V ≃ₗ[ZMod 3] V)
      hd1sqV hd2sqV hd12V hd1disp hd2disp
  have hfixTr : ∀ t : ↥Tr, δ1 t = t → δ2 t = t → t = 0 := by
    intro t ht1 ht2
    exact ggNineDepRowLinAux_flip_fix_both fb hcover (by simpa [δ1] using ht1)
      (by simpa [δ2] using ht2)
  have hfixS : ∀ t ∈ Tr, (d1 : V ≃ₗ[ZMod 3] V) t = t →
      (d2 : V ≃ₗ[ZMod 3] V) t = t → t = 0 := by
    intro t ht h1 h2
    have ht1 : δ1 ⟨t, ht⟩ = ⟨t, ht⟩ := by
      apply Subtype.ext
      rw [← hd1]
      change (((ρ d1) ⟨t, ht⟩ : ↥Tr) : V) = t
      rw [← hR_apply d1 ⟨t, ht⟩]
      exact h1
    have ht2 : δ2 ⟨t, ht⟩ = ⟨t, ht⟩ := by
      apply Subtype.ext
      rw [← hd2]
      change (((ρ d2) ⟨t, ht⟩ : ↥Tr) : V) = t
      rw [← hR_apply d2 ⟨t, ht⟩]
      exact h2
    have h0 : (⟨t, ht⟩ : ↥Tr) = 0 := hfixTr ⟨t, ht⟩ ht1 ht2
    simpa using congrArg Subtype.val h0
  have hinf : Tr ⊓ W = ⊥ :=
    ggNineDepRowLinAux_inf_fix Tr (d1 : V ≃ₗ[ZMod 3] V) (d2 : V ≃ₗ[ZMod 3] V) hfixS
  have hcommV1 : (d1 : V ≃ₗ[ZMod 3] V) * (uhat : V ≃ₗ[ZMod 3] V) =
      (uhat : V ≃ₗ[ZMod 3] V) * (d1 : V ≃ₗ[ZMod 3] V) := by
    have hh := congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod 3] V)) huhat_d1
    simpa [LinearEquiv.mul_apply] using hh.symm
  have hcommV2 : (d2 : V ≃ₗ[ZMod 3] V) * (uhat : V ≃ₗ[ZMod 3] V) =
      (uhat : V ≃ₗ[ZMod 3] V) * (d2 : V ≃ₗ[ZMod 3] V) := by
    have hh := congrArg (fun a : ↥A => (a : V ≃ₗ[ZMod 3] V)) huhat_d2
    simpa [LinearEquiv.mul_apply] using hh.symm
  have huhat_fix_W : ∀ w ∈ W, (uhat : V ≃ₗ[ZMod 3] V) w = w := by
    intro w hw
    have hmem : (uhat : V ≃ₗ[ZMod 3] V) w - w ∈ Tr :=
      hdispA uhat.1 uhat.2 w
    have hfix1 : (d1 : V ≃ₗ[ZMod 3] V) ((uhat : V ≃ₗ[ZMod 3] V) w - w) =
        (uhat : V ≃ₗ[ZMod 3] V) w - w := by
      have hcw : (d1 : V ≃ₗ[ZMod 3] V) ((uhat : V ≃ₗ[ZMod 3] V) w) =
          (uhat : V ≃ₗ[ZMod 3] V) ((d1 : V ≃ₗ[ZMod 3] V) w) := by
        have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => e w) hcommV1
        simpa [LinearEquiv.mul_apply] using hh
      rw [map_sub, hcw, hw (d1 : V ≃ₗ[ZMod 3] V) (by simp)]
    have hfix2 : (d2 : V ≃ₗ[ZMod 3] V) ((uhat : V ≃ₗ[ZMod 3] V) w - w) =
        (uhat : V ≃ₗ[ZMod 3] V) w - w := by
      have hcw : (d2 : V ≃ₗ[ZMod 3] V) ((uhat : V ≃ₗ[ZMod 3] V) w) =
          (uhat : V ≃ₗ[ZMod 3] V) ((d2 : V ≃ₗ[ZMod 3] V) w) := by
        have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => e w) hcommV2
        simpa [LinearEquiv.mul_apply] using hh
      rw [map_sub, hcw, hw (d2 : V ≃ₗ[ZMod 3] V) (by simp)]
    have hmemW : (uhat : V ≃ₗ[ZMod 3] V) w - w ∈ W := by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hfix1
      · exact hfix2
    have hbot : (uhat : V ≃ₗ[ZMod 3] V) w - w ∈ (⊥ : Submodule (ZMod 3) V) := by
      rw [← hinf]
      exact Submodule.mem_inf.mpr ⟨hmem, hmemW⟩
    exact sub_eq_zero.mp (by simpa using hbot)
  have huhat_Tr : ∀ y : ↥Tr, (uhat : V ≃ₗ[ZMod 3] V) (y : V) = ((u y : ↥Tr) : V) := by
    intro y
    rw [hR_apply uhat y, huhat]
  have hu_move : ∀ y : ↥Tr, u y - y = (fb.coord i1 y) • fb i0 := by
    intro y
    rw [hu_apply]
    abel
  have hu_fb0 : u (fb i0) = fb i0 := by
    rw [hu_apply, hfv, zero_smul, add_zero]
  have hu_fix_move : ∀ y : ↥Tr, u (u y - y) = u y - y := by
    intro y
    rw [hu_move y, map_smul, hu_fb0]
  have hdisp : ∀ v : V, (uhat : V ≃ₗ[ZMod 3] V) v - v ∈
      Submodule.span (ZMod 3) ({(fb i0 : V)} : Set V) := by
    intro v
    have hv : v ∈ Tr ⊔ W := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨t, ht, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hwfix : (uhat : V ≃ₗ[ZMod 3] V) w = w := huhat_fix_W w hw
    have htapply : (uhat : V ≃ₗ[ZMod 3] V) (t : V) = ((u ⟨t, ht⟩ : ↥Tr) : V) :=
      huhat_Tr ⟨t, ht⟩
    have hval : (uhat : V ≃ₗ[ZMod 3] V) ((t : V) + w) - ((t : V) + w) =
        ((u ⟨t, ht⟩ - ⟨t, ht⟩ : ↥Tr) : V) := by
      rw [map_add, htapply, hwfix]
      simp only [Submodule.coe_sub]
      abel
    rw [hval]
    have hd : ((u ⟨t, ht⟩ - ⟨t, ht⟩ : ↥Tr) : V) =
        (fb.coord i1 ⟨t, ht⟩) • (fb i0 : V) := by
      rw [hu_apply]
      simp
    rw [hd]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hfb0_mem : (fb i0 : V) ∈ ggLinMove (uhat : V ≃ₗ[ZMod 3] V) := by
    rw [ggLinMove]
    refine ⟨(fb i1 : V), ?_⟩
    change (uhat : V ≃ₗ[ZMod 3] V) (fb i1 : V) - (fb i1 : V) = (fb i0 : V)
    rw [huhat_Tr (fb i1)]
    have h2 : u (fb i1) = fb i1 + fb i0 := by
      rw [hu_apply, Basis.coord_apply, Basis.repr_self_apply, if_pos rfl, one_smul]
    rw [h2]
    simp
  have hmove : ggLinMove (uhat : V ≃ₗ[ZMod 3] V) =
      Submodule.span (ZMod 3) ({(fb i0 : V)} : Set V) := by
    apply le_antisymm
    · rw [ggLinMove]
      rintro y ⟨w, rfl⟩
      exact hdisp w
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hfb0_mem
  have hrank : Module.finrank (ZMod 3) (ggLinMove (uhat : V ≃ₗ[ZMod 3] V)) = 1 := by
    rw [hmove, finrank_span_singleton]
    intro h0
    exact fb.ne_zero i0 (by simpa using (Subtype.ext h0 : (fb i0 : ↥Tr) = 0))
  have hfixed : ∀ w, (uhat : V ≃ₗ[ZMod 3] V)
      ((uhat : V ≃ₗ[ZMod 3] V) w - w) = (uhat : V ≃ₗ[ZMod 3] V) w - w := by
    intro w
    have hv : w ∈ Tr ⊔ W := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have hwfix : (uhat : V ≃ₗ[ZMod 3] V) w' = w' := huhat_fix_W w' hw'
    have htapply : (uhat : V ≃ₗ[ZMod 3] V) (t : V) = ((u ⟨t, ht⟩ : ↥Tr) : V) :=
      huhat_Tr ⟨t, ht⟩
    have hval : (uhat : V ≃ₗ[ZMod 3] V) ((t : V) + w') - ((t : V) + w') =
        ((u ⟨t, ht⟩ - ⟨t, ht⟩ : ↥Tr) : V) := by
      rw [map_add, htapply, hwfix]
      simp only [Submodule.coe_sub]
      abel
    rw [hval]
    have hval' : (uhat : V ≃ₗ[ZMod 3] V)
        (((u ⟨t, ht⟩ - ⟨t, ht⟩ : ↥Tr) : V)) =
        ((u (u ⟨t, ht⟩ - ⟨t, ht⟩) : ↥Tr) : V) :=
      huhat_Tr (u ⟨t, ht⟩ - ⟨t, ht⟩)
    rw [hval', hu_fix_move ⟨t, ht⟩]
  exact X.case.lin.no_transv (uhat : V ≃ₗ[ZMod 3] V) uhat.2 ⟨hrank, hfixed⟩

theorem ggNineDepRowLin_holds : GGNineDepRowLinInput := by
  intro V _ _ h α r T s x X hQ
  classical
  have hfinV : Module.Finite (ZMod 3) V := l04nD2_finite X.case
  have hfinTr : Module.Finite (ZMod 3) ↥(ggFixLineT r s) :=
    Module.Finite.of_injective (ggFixLineT r s).subtype Subtype.val_injective
  have hcases : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 7 ∨
      Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 8 ∨
      Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 9 := by
    have h1 := X.d_ge
    have h2 := X.d_le
    omega
  rcases hcases with hd | hd | hd
  · let fb := Module.finBasisOfFinrankEq (ZMod 3) ↥(ggFixLineT r s) hd
    exact ggNineDepRowLinAux_main X hQ.1 fb ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by decide)
      ({2, 3, 4, 5} : Finset (Fin 7)) ({0, 1, 2, 6} : Finset (Fin 7))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · let fb := Module.finBasisOfFinrankEq (ZMod 3) ↥(ggFixLineT r s) hd
    exact ggNineDepRowLinAux_main X hQ.1 fb ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by decide)
      ({2, 3, 4, 5, 6, 7} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · let fb := Module.finBasisOfFinrankEq (ZMod 3) ↥(ggFixLineT r s) hd
    exact ggNineDepRowLinAux_main X hQ.1 fb ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by decide)
      ({2, 3, 4, 5, 6, 7} : Finset (Fin 9)) ({0, 1, 2, 8} : Finset (Fin 9))
      (by decide) (by decide) (by decide) (by decide) (by decide)

end CFSG.StandardType

end
