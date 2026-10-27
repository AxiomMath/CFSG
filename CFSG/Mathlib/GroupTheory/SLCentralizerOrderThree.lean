module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace CFSG.SLCentralizerOrderThree

open scoped MatrixGroups

private lemma two_end {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    (2 : Module.End (ZMod 2) V) = 0 := by
  rw [show (2 : Module.End (ZMod 2) V) = algebraMap (ZMod 2) (Module.End (ZMod 2) V) 2 by
    rw [map_ofNat]]
  rw [show (2 : ZMod 2) = 0 by decide, map_zero]

private lemma add_self_eq_zero_V {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

private lemma toLin_pow_three {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) : g.toLinearMap ^ 3 = 1 := by
  change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom g) ^ 3 = 1
  rw [← map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) g 3, hg, map_one]

private lemma f_mul_poly {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) :
    (g.toLinearMap - 1) * (g.toLinearMap ^ 2 + g.toLinearMap + 1) = 0 := by
  have hG3 := toLin_pow_three g hg
  have h : (g.toLinearMap - 1) * (g.toLinearMap ^ 2 + g.toLinearMap + 1)
      = g.toLinearMap ^ 3 - 1 := by noncomm_ring
  rw [h, hG3, sub_self]

private lemma f_mul_poly' {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) :
    (g.toLinearMap ^ 2 + g.toLinearMap + 1) * (g.toLinearMap - 1) = 0 := by
  have hG3 := toLin_pow_three g hg
  have h : (g.toLinearMap ^ 2 + g.toLinearMap + 1) * (g.toLinearMap - 1)
      = g.toLinearMap ^ 3 - 1 := by noncomm_ring
  rw [h, hG3, sub_self]

private lemma poly_add_f {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) :
    (g.toLinearMap ^ 2 + g.toLinearMap + (1 : Module.End (ZMod 2) V))
      + g.toLinearMap * (g.toLinearMap - 1) = 1 := by
  have h2 := two_end (V := V)
  have h : (g.toLinearMap ^ 2 + g.toLinearMap + (1 : Module.End (ZMod 2) V))
      + g.toLinearMap * (g.toLinearMap - 1)
      = 1 + 2 * g.toLinearMap ^ 2 := by noncomm_ring
  rw [h, h2, zero_mul, add_zero]

private lemma decomp_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (v : V) :
    v = (g.toLinearMap ^ 2 + g.toLinearMap + (1 : Module.End (ZMod 2) V)) v
      + g.toLinearMap ((g.toLinearMap - 1) v) := by
  have h := LinearMap.congr_fun (poly_add_f g) v
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using h.symm

private lemma f_sq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) :
    (g.toLinearMap - 1) * (g.toLinearMap - 1) = g.toLinearMap ^ 2 + 1 := by
  have h2 := two_end (V := V)
  have h : (g.toLinearMap - 1) * (g.toLinearMap - 1)
      = g.toLinearMap ^ 2 - 2 * g.toLinearMap + 1 := by noncomm_ring
  rw [h, h2, zero_mul, sub_zero]

private lemma g_mul_f {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) :
    g.toLinearMap * (g.toLinearMap - 1) = (g.toLinearMap - 1) * g.toLinearMap := by
  noncomm_ring

private lemma poly_mem_ker {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) (v : V) :
    (g.toLinearMap ^ 2 + g.toLinearMap + (1 : Module.End (ZMod 2) V)) v
      ∈ LinearMap.ker (g.toLinearMap - 1) := by
  rw [LinearMap.mem_ker, ← Module.End.mul_apply, f_mul_poly g hg, LinearMap.zero_apply]

private lemma f_mem_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (v : V) :
    g.toLinearMap ((g.toLinearMap - 1) v) ∈ LinearMap.range (g.toLinearMap - 1) := by
  refine ⟨g.toLinearMap v, ?_⟩
  show (g.toLinearMap - 1) (g.toLinearMap v) = g.toLinearMap ((g.toLinearMap - 1) v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, g_mul_f]

private lemma decomp_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) (v : V) :
    v ∈ LinearMap.ker (g.toLinearMap - 1) ⊔ LinearMap.range (g.toLinearMap - 1) := by
  rw [Submodule.mem_sup]
  exact ⟨_, poly_mem_ker g hg v, _, f_mem_range g v, (decomp_apply g v).symm⟩

private lemma disjoint_ker_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) :
    LinearMap.ker (g.toLinearMap - 1) ⊓ LinearMap.range (g.toLinearMap - 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, LinearMap.mem_ker] at hv
  obtain ⟨u, hu⟩ := hv.2
  have h1 : (g.toLinearMap ^ 2 + (1 : Module.End (ZMod 2) V)) u = 0 := by
    have h := hv.1
    rw [← hu, ← Module.End.mul_apply, f_sq g] at h
    exact h
  have hzero : (g.toLinearMap ^ 2) u + u = 0 := by
    simpa only [LinearMap.add_apply, Module.End.one_apply] using h1
  have hu2 : u + u = 0 := add_self_eq_zero_V u
  have h2 : (g.toLinearMap ^ 2) u = u := by
    calc (g.toLinearMap ^ 2) u = (g.toLinearMap ^ 2) u + (u + u) := by rw [hu2, add_zero]
      _ = ((g.toLinearMap ^ 2) u + u) + u := by rw [add_assoc]
      _ = 0 + u := by rw [hzero]
      _ = u := zero_add u
  have hGu : g.toLinearMap u = u := by
    have h3 : g.toLinearMap ((g.toLinearMap ^ 2) u) = u := by
      rw [← Module.End.mul_apply, (pow_succ' g.toLinearMap 2).symm, toLin_pow_three g hg,
        Module.End.one_apply]
    rwa [h2] at h3
  rw [← hu, LinearMap.sub_apply, Module.End.one_apply, hGu, sub_self]

private lemma isCompl_ker_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) :
    IsCompl (LinearMap.ker (g.toLinearMap - 1)) (LinearMap.range (g.toLinearMap - 1)) := by
  refine ⟨disjoint_iff_inf_le.mpr (le_of_eq (disjoint_ker_range g hg)), ?_⟩
  rw [codisjoint_iff, Submodule.eq_top_iff']
  intro v
  exact decomp_mem g hg v

private lemma g_mem_ker {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) {w : V}
    (hw : w ∈ LinearMap.ker (g.toLinearMap - 1)) : g.toLinearMap w = w := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hw
  exact sub_eq_zero.mp hw

private lemma poly_eq_zero_on_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) {p : V}
    (hp : p ∈ LinearMap.range (g.toLinearMap - 1)) :
    (g.toLinearMap ^ 2 + g.toLinearMap + (1 : Module.End (ZMod 2) V)) p = 0 := by
  obtain ⟨u, rfl⟩ := hp
  rw [← Module.End.mul_apply, f_mul_poly' g hg, LinearMap.zero_apply]

private lemma g_sq_on_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1) {p : V}
    (hp : p ∈ LinearMap.range (g.toLinearMap - 1)) :
    (g.toLinearMap ^ 2) p = p + g.toLinearMap p := by
  have h := poly_eq_zero_on_range g hg hp
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply] at h
  have hx : (g.toLinearMap ^ 2) p + g.toLinearMap p = p := by
    have hp2 : p + p = 0 := add_self_eq_zero_V p
    calc (g.toLinearMap ^ 2) p + g.toLinearMap p
        = (g.toLinearMap ^ 2) p + g.toLinearMap p + (p + p) := by rw [hp2, add_zero]
      _ = ((g.toLinearMap ^ 2) p + g.toLinearMap p + p) + p := by
            conv_rhs => rw [add_assoc]
      _ = 0 + p := by rw [h]
      _ = p := zero_add p
  calc (g.toLinearMap ^ 2) p
      = ((g.toLinearMap ^ 2) p + g.toLinearMap p) + g.toLinearMap p := by
        conv_rhs => rw [add_assoc, add_self_eq_zero_V, add_zero]
    _ = p + g.toLinearMap p := by rw [hx]

private lemma zmod_two_dichotomy (s : ZMod 2) : s = 0 ∨ s = 1 := by
  have h := ZMod.val_lt s
  have h01 : s.val = 0 ∨ s.val = 1 := by omega
  rcases h01 with h0 | h1
  · exact Or.inl ((ZMod.val_eq_zero s).mp h0)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num) s).mp h1)

private lemma toLin_pow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (i : ℕ) : (g ^ i).toLinearMap = g.toLinearMap ^ i := by
  simpa using map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) g i

private lemma comm_preserves_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g a : V ≃ₗ[ZMod 2] V)
    (ha : a.toLinearMap * g.toLinearMap = g.toLinearMap * a.toLinearMap) {w : V}
    (hw : w ∈ LinearMap.range (g.toLinearMap - 1)) :
    a.toLinearMap w ∈ LinearMap.range (g.toLinearMap - 1) := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨a.toLinearMap u, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have hAf : a.toLinearMap * (g.toLinearMap - 1) = (g.toLinearMap - 1) * a.toLinearMap := by
    rw [mul_sub, sub_mul, ha, mul_one, one_mul]
  rw [hAf, Module.End.mul_apply]

private lemma span_pair_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1)
    (hP2 : Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - 1)) = 2)
    {v : V} (hv : v ∈ LinearMap.range (g.toLinearMap - 1)) (hv0 : v ≠ 0) :
    Submodule.span (ZMod 2) ({v, g.toLinearMap v} : Set V)
      = LinearMap.range (g.toLinearMap - 1) := by
  have hgv : g.toLinearMap v ∈ LinearMap.range (g.toLinearMap - 1) := by
    obtain ⟨u, rfl⟩ := hv
    exact f_mem_range g u
  have hgv0 : g.toLinearMap v ≠ 0 := by
    intro h
    exact hv0 (g.injective (by rw [map_zero]; exact h))
  have hgvv : g.toLinearMap v ≠ v := by
    intro h
    have hker : v ∈ LinearMap.ker (g.toLinearMap - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
    have hbot : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← disjoint_ker_range g hg]
      exact ⟨hker, hv⟩
    exact hv0 (by simpa using hbot)
  have hli : LinearIndependent (ZMod 2) ![v, g.toLinearMap v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod_two_dichotomy s with rfl | rfl <;>
      rcases zmod_two_dichotomy t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      exact hgv0 (by simpa using hst)
    · exfalso
      exact hv0 (by simpa using hst)
    · exfalso
      apply hgvv
      have h2 : v + g.toLinearMap v = 0 := by simpa using hst
      have hv2 : v + v = 0 := add_self_eq_zero_V v
      calc g.toLinearMap v = g.toLinearMap v + (v + v) := by rw [hv2, add_zero]
        _ = (g.toLinearMap v + v) + v := by conv_rhs => rw [add_assoc]
        _ = 0 + v := by rw [add_comm (g.toLinearMap v) v, h2]
        _ = v := zero_add v
  have hle : Submodule.span (ZMod 2) ({v, g.toLinearMap v} : Set V)
      ≤ LinearMap.range (g.toLinearMap - 1) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hgv
  have hrange : Set.range ![v, g.toLinearMap v] = ({v, g.toLinearMap v} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hP2, ← hrange, finrank_span_eq_card hli]
  simp

private lemma eq_on_range_of_eq_on_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {v : V} (g : V ≃ₗ[ZMod 2] V)
    (hspan : Submodule.span (ZMod 2) ({v, g.toLinearMap v} : Set V)
      = LinearMap.range (g.toLinearMap - 1))
    {A B : V →ₗ[ZMod 2] V} (h1 : A v = B v)
    (h2 : A (g.toLinearMap v) = B (g.toLinearMap v)) :
    ∀ w ∈ LinearMap.range (g.toLinearMap - 1), A w = B w := by
  intro w hw
  rw [← hspan, Submodule.mem_span_pair] at hw
  obtain ⟨d1, d2, hd⟩ := hw
  calc A w = A (d1 • v + d2 • g.toLinearMap v) := by rw [← hd]
    _ = d1 • A v + d2 • A (g.toLinearMap v) := by rw [map_add, map_smul, map_smul]
    _ = d1 • B v + d2 • B (g.toLinearMap v) := by rw [h1, h2]
    _ = B (d1 • v + d2 • g.toLinearMap v) := by rw [map_add, map_smul, map_smul]
    _ = B w := by rw [← hd]

private lemma commute_range_eq_pow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (g a : V ≃ₗ[ZMod 2] V) (hg : g ^ 3 = 1)
    (ha : a.toLinearMap * g.toLinearMap = g.toLinearMap * a.toLinearMap)
    (hP2 : Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - 1)) = 2)
    {v : V} (hv : v ∈ LinearMap.range (g.toLinearMap - 1)) (hv0 : v ≠ 0) :
    ∃ i : ℕ, ∀ w ∈ LinearMap.range (g.toLinearMap - 1),
      a.toLinearMap w = ((g ^ i).toLinearMap) w := by
  have hspan := span_pair_range g hg hP2 hv hv0
  have hAv : a.toLinearMap v ∈ LinearMap.range (g.toLinearMap - 1) :=
    comm_preserves_range g a ha hv
  have hAv0 : a.toLinearMap v ≠ 0 := by
    intro h
    exact hv0 (a.injective (by simpa using h))
  have hAG : a.toLinearMap (g.toLinearMap v) = g.toLinearMap (a.toLinearMap v) := by
    rw [← Module.End.mul_apply, ha, Module.End.mul_apply]
  rw [← hspan, Submodule.mem_span_pair] at hAv
  obtain ⟨c1, c2, hc⟩ := hAv
  rcases zmod_two_dichotomy c1 with rfl | rfl <;>
    rcases zmod_two_dichotomy c2 with rfl | rfl
  · exfalso
    exact hAv0 (by simpa using hc.symm)
  · refine ⟨1, ?_⟩
    have h1 : a.toLinearMap v = (g.toLinearMap ^ 1) v := by simpa using hc.symm
    have h2 : a.toLinearMap (g.toLinearMap v) = (g.toLinearMap ^ 1) (g.toLinearMap v) := by
      rw [hAG, h1]
      simp
    intro w hw
    have := eq_on_range_of_eq_on_pair g hspan h1 h2 w hw
    simpa [toLin_pow] using this
  · refine ⟨0, ?_⟩
    have h1 : a.toLinearMap v = (g.toLinearMap ^ 0) v := by simpa using hc.symm
    have h2 : a.toLinearMap (g.toLinearMap v) = (g.toLinearMap ^ 0) (g.toLinearMap v) := by
      rw [hAG, h1]
      simp
    intro w hw
    have := eq_on_range_of_eq_on_pair g hspan h1 h2 w hw
    simpa [toLin_pow] using this
  · refine ⟨2, ?_⟩
    have hG2v : (g.toLinearMap ^ 2) v = v + g.toLinearMap v := g_sq_on_range g hg hv
    have h1 : a.toLinearMap v = (g.toLinearMap ^ 2) v := by
      have hv' : a.toLinearMap v = v + g.toLinearMap v := by simpa using hc.symm
      rw [hv', ← hG2v]
    have h2 : a.toLinearMap (g.toLinearMap v) = (g.toLinearMap ^ 2) (g.toLinearMap v) := by
      rw [hAG, h1]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
    intro w hw
    have := eq_on_range_of_eq_on_pair g hspan h1 h2 w hw
    simpa [toLin_pow] using this

private noncomputable def slEquivGL (n : ℕ) :
    SL(n, ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), ?_⟩, ?_⟩
      · exact congrArg Units.val (Subsingleton.elim
          (Matrix.GeneralLinearGroup.det A) (1 : (ZMod 2)ˣ))
      · exact Units.ext rfl⟩

private noncomputable def glEquivSl {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (m : ℕ) (hW : Module.finrank (ZMod 2) W = m) :
    (W ≃ₗ[ZMod 2] W) ≃* SL(m, ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
    ((Matrix.GeneralLinearGroup.toLin'
        (Module.finBasisOfFinrankEq (ZMod 2) W hW)).symm.trans
      (slEquivGL m).symm)

private lemma zmod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases zmod_two_dichotomy x with h | h
  · exact absurd h hx
  · exact h

private lemma toLin'_surjective (n : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.toLin'
      (n := Fin n) (R := ZMod 2)) := by
  intro e
  let M : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix' e.toLinearMap
  let N : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix' (e⁻¹).toLinearMap
  have htoLinM : Matrix.toLin' M = e.toLinearMap := Matrix.toLin'_toMatrix' e.toLinearMap
  have hcomp : e.toLinearMap * (e⁻¹).toLinearMap = 1 := by
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom e) *
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom e⁻¹) = 1
    rw [← map_mul (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) e e⁻¹,
      mul_inv_cancel, map_one]
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix'_mul, hcomp, LinearMap.toMatrix'_one]
  have hmul : M.det * N.det = 1 := by
    have := congrArg Matrix.det hMN
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have hne : M.det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hdet : M.det = 1 := zmod_two_eq_one_of_ne_zero hne
  refine ⟨⟨M, hdet⟩, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  simpa [htoLinM] using (Matrix.SpecialLinearGroup.toLin'_to_linearMap (R := ZMod 2)
    (⟨M, hdet⟩ : SL(n, ZMod 2)))

private lemma toLin'_bijective (n : ℕ) :
    Function.Bijective (Matrix.SpecialLinearGroup.toLin'
      (n := Fin n) (R := ZMod 2)) :=
  ⟨Matrix.SpecialLinearGroup.toLin'_injective, toLin'_surjective n⟩

private lemma prodCongr_mul {W P : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup P] [Module (ZMod 2) P] (b1 b2 : W ≃ₗ[ZMod 2] W) :
    (b1 * b2).prodCongr (1 : P ≃ₗ[ZMod 2] P)
      = (b1.prodCongr 1) * (b2.prodCongr 1) := by
  ext ⟨w, p⟩
  · simp [LinearEquiv.prodCongr_apply, LinearEquiv.mul_apply]
  · rfl

private noncomputable def blockDiag {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V) :
    (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V) :=
  { toFun := fun b => e.symm.trans ((b.prodCongr (1 : P ≃ₗ[ZMod 2] P)).trans e)
    map_one' := by
      ext v
      simp [LinearEquiv.trans_apply]
    map_mul' := by
      intro b1 b2
      ext v
      simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
        LinearEquiv.prodCongr_apply, LinearEquiv.symm_apply_apply, prodCongr_mul] }

private lemma blockDiag_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (b : W ≃ₗ[ZMod 2] W) (x : V) :
    blockDiag e b x = e ((b.prodCongr (1 : P ≃ₗ[ZMod 2] P)) (e.symm x)) := rfl

private lemma symm_add {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V))
    (a : W) (b : P) : e.symm ((a : V) + (b : V)) = (a, b) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (hadd a b).symm

private lemma blockDiag_fixes_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V))
    (b : W ≃ₗ[ZMod 2] W) (p : P) :
    blockDiag e b (p : V) = (p : V) := by
  have hes : e.symm (p : V) = (0, p) := by
    rw [LinearEquiv.symm_apply_eq]
    simpa using (hadd 0 p).symm
  rw [blockDiag_apply, hes]
  have h1 : (b.prodCongr (1 : P ≃ₗ[ZMod 2] P)) (0, p) = (0, p) := by
    ext <;> simp [LinearEquiv.prodCongr_apply]
  rw [h1]
  simpa using hadd 0 p

private lemma blockDiag_apply_ker {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V))
    (b : W ≃ₗ[ZMod 2] W) (w : W) :
    blockDiag e b (w : V) = ((b w : W) : V) := by
  have hes : e.symm (w : V) = (w, 0) := by
    rw [LinearEquiv.symm_apply_eq]
    simpa using (hadd w 0).symm
  rw [blockDiag_apply, hes]
  have h1 : (b.prodCongr (1 : P ≃ₗ[ZMod 2] P)) (w, 0) = (b w, 0) := by
    ext <;> simp [LinearEquiv.prodCongr_apply]
  rw [h1]
  simpa using hadd (b w) 0

private lemma blockDiag_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V)) :
    Function.Injective (blockDiag e) := by
  intro b1 b2 h
  ext w
  have hw := congrArg (fun f => f (w : V)) h
  rw [blockDiag_apply_ker e hadd b1 w, blockDiag_apply_ker e hadd b2 w] at hw
  exact hw

private lemma blockDiag_commutes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (e : (W × P) ≃ₗ[ZMod 2] V)
    (hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V))
    (g : V ≃ₗ[ZMod 2] V)
    (hgW : ∀ w : W, g (w : V) = (w : V))
    (hgP : ∀ p : P, ∃ q : P, g (p : V) = (q : V))
    (b : W ≃ₗ[ZMod 2] W) :
    ∀ x, blockDiag e b (g x) = g (blockDiag e b x) := by
  intro x
  cases h : e.symm x with
  | mk w p =>
  obtain ⟨q, hq⟩ := hgP p
  have hx : x = (w : V) + (p : V) := by
    conv_lhs => rw [← e.apply_symm_apply x]
    rw [h, hadd]
  have hgx : g x = (w : V) + (q : V) := by
    rw [hx, map_add, hgW, hq]
  have hes : e.symm (g x) = (w, q) := by
    rw [hgx, symm_add e hadd w q]
  rw [blockDiag_apply, hes, blockDiag_apply, h]
  have h1 : (b.prodCongr (1 : P ≃ₗ[ZMod 2] P)) (w, q) = (b w, q) := by
    ext <;> simp [LinearEquiv.prodCongr_apply]
  have h2 : (b.prodCongr (1 : P ≃ₗ[ZMod 2] P)) (w, p) = (b w, p) := by
    ext <;> simp [LinearEquiv.prodCongr_apply]
  rw [h1, h2]
  rw [hadd (b w) q, hadd (b w) p, map_add, hgW (b w), hq]

private def fixesSubmodule {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (P : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ v ∈ P, g v = v}
  mul_mem' := by
    intro a b ha hb v hv
    rw [LinearEquiv.mul_apply, hb v hv]
    exact ha v hv
  one_mem' := by intro v _; rfl
  inv_mem' := by
    intro a ha v hv
    apply a.injective
    change a (a.symm v) = a v
    rw [LinearEquiv.apply_symm_apply]
    exact (ha v hv).symm

private lemma map_ker_eq_of_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (g z : V ≃ₗ[ZMod 2] V)
    (hcomm : g.toLinearMap * z.toLinearMap = z.toLinearMap * g.toLinearMap) :
    (LinearMap.ker (z.toLinearMap - 1)).map (g : V →ₗ[ZMod 2] V)
      = LinearMap.ker (z.toLinearMap - 1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hw' : z.toLinearMap w = w := by
      have h := LinearMap.mem_ker.mp hw
      simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h
    calc z.toLinearMap (g.toLinearMap w) = (z.toLinearMap * g.toLinearMap) w := by
          rw [Module.End.mul_apply]
      _ = (g.toLinearMap * z.toLinearMap) w := by rw [← hcomm]
      _ = g.toLinearMap (z.toLinearMap w) := by rw [Module.End.mul_apply]
      _ = g.toLinearMap w := by rw [hw']
  · rw [LinearEquiv.finrank_map_eq]

private lemma map_centralizer_of_bijective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Bijective f) (s : Set G) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f) ?_
  rintro x hx
  obtain ⟨g, rfl⟩ := hf.2 x
  refine ⟨g, ?_, rfl⟩
  exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    apply hf.1
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hx) (f y) ⟨y, hy, rfl⟩)

private theorem exists_subgroup_centralizer_eq_linear
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (m : ℕ) (zL : V ≃ₗ[ZMod 2] V) (hzL : zL ^ 3 = 1)
    (hV : Module.finrank (ZMod 2) V = m + 2)
    (hW : Module.finrank (ZMod 2) (LinearMap.ker (zL.toLinearMap - 1)) = m) :
    ∃ J : Subgroup (V ≃ₗ[ZMod 2] V),
      J ≤ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) ∧
      Subgroup.zpowers zL ⊓ J = ⊥ ∧
      Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) = Subgroup.zpowers zL ⊔ J ∧
      Nonempty (↥J ≃* SL(m, ZMod 2)) ∧
      ∀ g ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)),
        (g ∈ J ↔ ∀ v ∈ LinearMap.range (zL.toLinearMap - 1), g v = v) := by
  let W : Submodule (ZMod 2) V := LinearMap.ker (zL.toLinearMap - 1)
  let P : Submodule (ZMod 2) V := LinearMap.range (zL.toLinearMap - 1)
  have hW' : Module.finrank (ZMod 2) W = m := hW
  have hcompl : IsCompl W P := isCompl_ker_range zL hzL
  let e : (W × P) ≃ₗ[ZMod 2] V := Submodule.prodEquivOfIsCompl W P hcompl
  have hadd : ∀ (a : W) (b : P), e (a, b) = (a : V) + (b : V) :=
    fun a b => Submodule.coe_prodEquivOfIsCompl' W P hcompl (a, b)
  have hP2 : Module.finrank (ZMod 2) P = 2 := by
    have hdim : Module.finrank (ZMod 2) P + Module.finrank (ZMod 2) W
        = Module.finrank (ZMod 2) V :=
      LinearMap.finrank_range_add_finrank_ker (zL.toLinearMap - 1)
    rw [hW', hV] at hdim
    omega
  have hPne : P ≠ ⊥ := by
    intro hbot
    have : Module.finrank (ZMod 2) P = 0 := by rw [hbot]; simp
    omega
  obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
  have hzL_fix_zero : ∀ w ∈ P, zL w = w → w = 0 := by
    intro w hw hfix
    have hmem : w ∈ W ⊓ P := by
      refine ⟨?_, hw⟩
      show w ∈ LinearMap.ker (zL.toLinearMap - 1)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hfix
    have hle : w ∈ (⊥ : Submodule (ZMod 2) V) := disjoint_iff_inf_le.mp hcompl.disjoint hmem
    simpa using hle
  have hzL2_fix_zero : ∀ w ∈ P, (zL ^ 2) w = w → w = 0 := by
    intro w hw hfix
    have hL : zL ((zL ^ 2) w) = w := by
      have h1 : zL ((zL ^ 2) w) = (zL * zL ^ 2) w :=
        (LinearEquiv.mul_apply zL (zL ^ 2) w).symm
      rw [h1, ← pow_succ' zL 2, hzL]
      rfl
    have hzw : zL w = w := by
      have h2 := congrArg (fun x => zL x) hfix
      rw [hL] at h2
      exact h2.symm
    exact hzL_fix_zero w hw hzw
  have hzL_ne_one : zL ≠ 1 := by
    intro h
    apply hPne
    have : LinearMap.range (zL.toLinearMap - 1) = ⊥ := by
      have hz : zL.toLinearMap - 1 = 0 := by
        rw [h]
        ext v
        simp
      rw [hz]
      simp
    exact this
  let J : Subgroup (V ≃ₗ[ZMod 2] V) :=
    Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) ⊓ fixesSubmodule P
  have hJle : J ≤ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) := inf_le_left
  have hJmem : ∀ g ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)),
      (g ∈ J ↔ ∀ w ∈ P, g w = w) := by
    intro g hg
    constructor
    · intro h w hw
      exact h.2 w hw
    · intro h
      exact ⟨hg, h⟩
  have hbot : Subgroup.zpowers zL ⊓ J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxz, hxJ⟩ := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hfixk : ∀ w ∈ P, (zL ^ k) w = w := by
      have h : zL ^ k ∈ fixesSubmodule P := by
        have hx := hxJ.2
        change x ∈ fixesSubmodule P at hx
        rwa [← hk] at hx
      exact h
    have hzLorder : orderOf zL = 3 := orderOf_eq_prime hzL hzL_ne_one
    have hmod : zL ^ (k % (3 : ℤ)) = zL ^ k := by
      have h := zpow_mod_orderOf zL k
      rwa [hzLorder] at h
    have hcases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
      have h0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
      have h1 : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
      omega
    rw [← hk, ← hmod]
    rcases hcases with h | h | h
    · rw [h, zpow_zero]
    · exfalso
      have hzw : zL v = v := by
        have hw := hfixk v hvP
        rw [← hmod, h] at hw
        simpa using hw
      exact hv0 (hzL_fix_zero v hvP hzw)
    · exfalso
      have hzw : (zL ^ 2) v = v := by
        have hw := hfixk v hvP
        rw [← hmod, h] at hw
        simpa using hw
      exact hv0 (hzL2_fix_zero v hvP hzw)
  have hsup : Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) =
      Subgroup.zpowers zL ⊔ J := by
    apply le_antisymm
    · intro a ha
      have h2 : zL * a = a * zL := by
        have h := ha
        rw [Subgroup.mem_centralizer_iff] at h
        exact h zL (by simp)
      have hcomm : a.toLinearMap * zL.toLinearMap = zL.toLinearMap * a.toLinearMap := by
        have h3 := congrArg (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) h2.symm
        simpa using h3
      obtain ⟨i, hi⟩ := commute_range_eq_pow zL a hzL hcomm hP2 hvP hv0
      let y : V ≃ₗ[ZMod 2] V := (zL ^ (-(i : ℤ))) * a
      have hyJ : y ∈ J := by
        refine ⟨?_, ?_⟩
        · have hzLmem : zL ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) := by
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            rw [Set.mem_singleton_iff] at hh
            subst hh
            rfl
          exact Subgroup.mul_mem (Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)))
            (Subgroup.zpow_mem (Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)))
              hzLmem (-(i : ℤ))) ha
        · intro w hw
          change (zL ^ (-(i : ℤ))) (a w) = w
          rw [show a w = (zL ^ i) w from hi w hw,
            ← LinearEquiv.mul_apply, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero]
          rfl
      have hprod : zL ^ i * y = a := by
        change zL ^ i * ((zL ^ (-(i : ℤ))) * a) = a
        rw [← mul_assoc, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [← hprod]
      exact Subgroup.mul_mem (Subgroup.zpowers zL ⊔ J)
        (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers zL i)) (Subgroup.mem_sup_right hyJ)
    · refine sup_le ?_ hJle
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rfl
  have hzL_fixes_W : ∀ w : W, zL (w : V) = (w : V) := fun w => g_mem_ker zL w.2
  have hzL_maps_P : ∀ p : P, ∃ q : P, zL (p : V) = (q : V) := by
    intro p
    obtain ⟨u, hu⟩ := p.2
    refine ⟨⟨(zL.toLinearMap - 1) (zL u), ⟨zL u, rfl⟩⟩, ?_⟩
    rw [← hu]
    show zL.toLinearMap ((zL.toLinearMap - 1) u)
      = (zL.toLinearMap - 1) (zL.toLinearMap u)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, g_mul_f zL]
  have hblock_mem : ∀ b : W ≃ₗ[ZMod 2] W, blockDiag e b ∈ J := by
    intro b
    refine ⟨?_, ?_⟩
    · change (blockDiag e) b ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V))
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply LinearEquiv.ext
      intro x
      exact blockDiag_commutes e hadd zL hzL_fixes_W hzL_maps_P b x
    · intro w hw
      exact blockDiag_fixes_range e hadd b ⟨w, hw⟩
  let blockDiagJ : (W ≃ₗ[ZMod 2] W) →* J :=
    { toFun := fun b => ⟨blockDiag e b, hblock_mem b⟩
      map_one' := Subtype.ext (map_one (blockDiag e))
      map_mul' := fun b1 b2 => Subtype.ext (map_mul (blockDiag e) b1 b2) }
  have hblock_inj : Function.Injective blockDiagJ := by
    intro b1 b2 h
    exact blockDiag_injective e hadd (Subtype.ext_iff.mp h)
  have hblock_surj : Function.Surjective blockDiagJ := by
    intro g
    have hcomm : g.1.toLinearMap * zL.toLinearMap = zL.toLinearMap * g.1.toLinearMap := by
      have h2 : zL * g.1 = g.1 * zL := by
        have h := g.2.1
        change g.1 ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) at h
        exact (Subgroup.mem_centralizer_iff.mp h) zL (by simp)
      have h3 := congrArg (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) h2.symm
      simpa using h3
    have hmap : W.map (g.1 : V →ₗ[ZMod 2] V) = W := map_ker_eq_of_commute g.1 zL hcomm
    let b : W ≃ₗ[ZMod 2] W := LinearEquiv.ofSubmodules g.1 W W hmap
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    cases hwp : e.symm x with
    | mk w p =>
    have hx : x = (w : V) + (p : V) := by
      conv_lhs => rw [← e.apply_symm_apply x]
      rw [hwp]
      exact hadd w p
    have hbw : (b w : V) = g.1 (w : V) := LinearEquiv.ofSubmodules_apply g.1 hmap w
    have hgp : g.1 (p : V) = (p : V) := g.2.2 (p : V) p.2
    calc blockDiag e b x
        = blockDiag e b ((w : V) + (p : V)) := by rw [hx]
      _ = blockDiag e b (w : V) + blockDiag e b (p : V) := by rw [map_add]
      _ = ((b w : W) : V) + (p : V) := by
            rw [blockDiag_apply_ker e hadd b w, blockDiag_fixes_range e hadd b p]
      _ = g.1 (w : V) + g.1 (p : V) := by rw [hbw, hgp]
      _ = g.1 ((w : V) + (p : V)) := (map_add g.1 _ _).symm
      _ = g.1 x := by rw [hx]
  refine ⟨J, hJle, hbot, hsup, ?_, hJmem⟩
  exact ⟨(MulEquiv.ofBijective blockDiagJ ⟨hblock_inj, hblock_surj⟩).symm.trans
    (glEquivSl m hW')⟩
theorem exists_subgroup_centralizer_eq {m : ℕ} (z : SL(m + 2, ZMod 2)) (hz : orderOf z = 3)
    (hfix : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin'
      (((z : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) - 1))) = m) :
    ∃ J : Subgroup SL(m + 2, ZMod 2),
      J ≤ Subgroup.centralizer ({z} : Set SL(m + 2, ZMod 2)) ∧
      Subgroup.zpowers z ⊓ J = ⊥ ∧
      Subgroup.centralizer ({z} : Set SL(m + 2, ZMod 2)) = Subgroup.zpowers z ⊔ J ∧
      Nonempty (↥J ≃* SL(m, ZMod 2)) ∧
      ∀ g ∈ Subgroup.centralizer ({z} : Set SL(m + 2, ZMod 2)),
        (g ∈ J ↔ ∀ v ∈ LinearMap.range (Matrix.toLin'
          (((z : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) - 1)),
            ((g : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec v
              = v) := by
  let V := Fin (m + 2) → ZMod 2
  let φ : SL(m + 2, ZMod 2) →* (V ≃ₗ[ZMod 2] V) :=
    Matrix.SpecialLinearGroup.toLin' (n := Fin (m + 2)) (R := ZMod 2)
  let zL : V ≃ₗ[ZMod 2] V := φ z
  have hzL : zL ^ 3 = 1 := by
    rw [show zL = φ z from rfl, ← map_pow φ z 3, show z ^ 3 = 1 from by
      have h := pow_orderOf_eq_one z
      rwa [hz] at h, map_one]
  have hφbij : Function.Bijective φ := toLin'_bijective (m + 2)
  have hsub : zL.toLinearMap - 1 = Matrix.toLin'
      (((z : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) - 1) := by
    have hzl : zL.toLinearMap = Matrix.toLin'
        (((z : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))) := by
      simpa [zL, φ] using Matrix.SpecialLinearGroup.toLin'_to_linearMap z
    rw [hzl, map_sub, Matrix.toLin'_one]
    rfl
  have hV : Module.finrank (ZMod 2) V = m + 2 := by
    simp [V]
  have hW : Module.finrank (ZMod 2) (LinearMap.ker (zL.toLinearMap - 1)) = m := by
    rw [hsub]
    exact hfix
  obtain ⟨Jlin, hJle, hJbot, hJsup, hJiso, hJmem⟩ :=
    exists_subgroup_centralizer_eq_linear m zL hzL hV hW
  let J : Subgroup SL(m + 2, ZMod 2) := Jlin.comap φ
  have hcent : (Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V))).comap φ
      = Subgroup.centralizer ({z} : Set SL(m + 2, ZMod 2)) := by
    have h := congrArg (Subgroup.comap φ)
      (map_centralizer_of_bijective φ hφbij ({z} : Set SL(m + 2, ZMod 2)))
    rw [Subgroup.comap_map_eq_self_of_injective (f := φ) hφbij.1, Set.image_singleton] at h
    simpa [zL] using h.symm
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · have hJle' : J ≤ (Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V))).comap φ :=
      Subgroup.comap_mono hJle
    rwa [hcent] at hJle'
  · rw [show J = Jlin.comap φ from rfl, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxz, hxJ⟩ := hx
    rw [Subgroup.mem_comap] at hxJ
    have hφ : φ x ∈ Subgroup.zpowers zL ⊓ Jlin := by
      refine ⟨?_, hxJ⟩
      have hmem : φ x ∈ (Subgroup.zpowers z).map φ := ⟨x, hxz, rfl⟩
      rw [MonoidHom.map_zpowers] at hmem
      simpa [zL] using hmem
    rw [hJbot, Subgroup.mem_bot] at hφ
    apply hφbij.1
    rw [hφ, map_one]
  · apply Subgroup.map_injective hφbij.1
    rw [map_centralizer_of_bijective φ hφbij ({z} : Set SL(m + 2, ZMod 2)),
      Set.image_singleton]
    rw [show J = Jlin.comap φ from rfl, Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_comap_eq_self_of_surjective (f := φ) hφbij.2 Jlin]
    simpa only [zL] using hJsup
  · obtain ⟨e⟩ := hJiso
    have hmapJ : (Jlin.comap φ).map φ = Jlin :=
      Subgroup.map_comap_eq_self_of_surjective (f := φ) hφbij.2 Jlin
    exact ⟨(Subgroup.equivMapOfInjective (Jlin.comap φ) φ hφbij.1).trans
      ((MulEquiv.subgroupCongr hmapJ).trans e)⟩
  · intro g hg
    have hφg : φ g ∈ Subgroup.centralizer ({zL} : Set (V ≃ₗ[ZMod 2] V)) := by
      have hg' := hg
      rw [Subgroup.mem_centralizer_iff] at hg'
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simpa [map_mul, zL] using congrArg φ (hg' z (by simp))
    have hφapp : ∀ v, φ g v = (((g : SL(m + 2, ZMod 2)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))).mulVec v := by
      intro v
      rw [show φ g = Matrix.SpecialLinearGroup.toLin' g from rfl,
        Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
    rw [show J = Jlin.comap φ from rfl, Subgroup.mem_comap, hJmem (φ g) hφg]
    constructor
    · intro h v hv
      have hv' : v ∈ LinearMap.range (zL.toLinearMap - 1) := by rw [hsub]; exact hv
      rw [← hφapp]
      exact h v hv'
    · intro h v hv
      have hv' : v ∈ LinearMap.range (Matrix.toLin'
          (((z : SL(m + 2, ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) - 1)) := by
        rw [← hsub]; exact hv
      rw [hφapp]
      exact h v hv'

end CFSG.SLCentralizerOrderThree

end

