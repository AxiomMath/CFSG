module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenTrans
import CFSG.RankThree.Classical.OddQuadraticFrame

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_plane_Q {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s t : K) :
    Q (s • P.e + t • P.f) = s * t := by
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, P.Q_e, P.Q_f, mul_zero, zero_add,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_plane_B {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s t s' t' : K) :
    polar Q (s • P.e + t • P.f) (s' • P.e + t' • P.f) = s * t' + t * s' := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, P.polar_ee,
    P.polar_ff, P.polar_ef, P.polar_fe, mul_zero, add_zero, zero_add]
  ring


open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_v_facts {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {a : V} (ha : a ∈ P.perp) {α : K}
    (hα0 : α ≠ 0) :
    Q (α • P.e - (Q a / α) • P.f) = -(Q a) ∧
    polar Q a (α • P.e - (Q a / α) • P.f) = 0 ∧
    polar Q P.e (α • P.e - (Q a / α) • P.f) = -Q a / α ∧
    polar Q (α • P.e - (Q a / α) • P.f) P.f = α := by
  have hae' : polar Q a P.e = 0 := by
    rw [polar_comm]; exact (HypPair.mem_perp.mp ha).1
  have haf' : polar Q a P.f = 0 := by
    rw [polar_comm]; exact (HypPair.mem_perp.mp ha).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul]
    exact (ocg_plane_Q P α (-(Q a / α))).trans (by field_simp [hα0])
  · simp only [polar_sub_right, polar_smul_right_eq, hae', haf', mul_zero, sub_zero]
  · simp only [polar_sub_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, mul_zero, mul_one]
    ring
  · rw [polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef, P.polar_ff]
    ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_Q_um_up {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {a v : V}
    (hQv : Q v = -(Q a)) (hav : polar Q a v = 0) :
    Q (a + v) = 0 ∧ Q (a - v) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.map_add Q a v, hQv, hav]; ring
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q a (-v), QuadraticMap.map_neg, hQv,
      polar_neg_right, hav]; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_up {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {a v : V} {α : K} (ha : a ∈ P.perp)
    (hpev : polar Q P.e v = -Q a / α) (hvf : polar Q v P.f = α) :
    polar Q P.e (a + v) = -Q a / α ∧ polar Q P.f (a + v) = α := by
  have hae : polar Q P.e a = 0 := (HypPair.mem_perp.mp ha).1
  have haf : polar Q P.f a = 0 := (HypPair.mem_perp.mp ha).2
  have haf' : polar Q a P.f = 0 := by rw [polar_comm]; exact haf
  refine ⟨?_, ?_⟩
  · rw [polar_add_right, hae, hpev, zero_add]
  · rw [polar_comm, polar_add_left, haf', hvf, zero_add]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_um {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {a v : V} {α : K} (ha : a ∈ P.perp)
    (hpev : polar Q P.e v = -Q a / α) (hvf : polar Q v P.f = α) :
    polar Q P.e (a - v) = Q a / α ∧ polar Q (a - v) P.f = -α := by
  have hae : polar Q P.e a = 0 := (HypPair.mem_perp.mp ha).1
  have haf : polar Q P.f a = 0 := (HypPair.mem_perp.mp ha).2
  have haf' : polar Q a P.f = 0 := by rw [polar_comm]; exact haf
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, polar_add_right, polar_neg_right, hae, hpev]; ring
  · rw [sub_eq_add_neg, polar_add_left, polar_neg_left, haf', hvf]; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_um_up {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {a v : V}
    (hQv : Q v = -(Q a)) (hav : polar Q a v = 0) :
    polar Q (a - v) (a + v) = 4 * Q a := by
  simp only [sub_eq_add_neg, polar_add_left, polar_add_right, polar_neg_left,
    polar_self_eq_two_mul, hav, polar_comm Q v a, hQv, neg_zero, add_zero]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_b'_facts {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {a : V} (ha : a ∈ P.perp) {α : K}
    (hα0 : α ≠ 0) :
    polar Q (α • P.e + (Q a / α) • P.f) a = 0 ∧
    polar Q (α • P.e + (Q a / α) • P.f) (α • P.e - (Q a / α) • P.f) = 0 ∧
    Q (α • P.e + (Q a / α) • P.f) = Q a := by
  have hae : polar Q P.e a = 0 := (HypPair.mem_perp.mp ha).1
  have haf : polar Q P.f a = 0 := (HypPair.mem_perp.mp ha).2
  refine ⟨?_, ?_, ?_⟩
  · simp only [polar_add_left, polar_smul_left_eq, hae, haf, mul_zero, add_zero]
  · rw [sub_eq_add_neg, ← neg_smul, ocg_plane_B P]; ring
  · exact (ocg_plane_Q P α (Q a / α)).trans (by field_simp [hα0])

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_h1 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {X : Subgroup (V ≃ₗ[K] V)}
    (hf : IsRootCenter Q X P.f) {a v : V} {α : K} (hα0 : α ≠ 0)
    (hQup : Q (a + v) = 0) (hpeup : polar Q P.e (a + v) = -Q a / α)
    (hpfup : polar Q P.f (a + v) = α) (hpeum : polar Q P.e (a - v) = Q a / α)
    (hpumf : polar Q (a - v) P.f = -α) (humup : polar Q (a - v) (a + v) = 4 * Q a) :
    ∃ h1 : V ≃ₗ[K] V, h1 ∈ X ∧ h1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      h1 (a + v) = α • P.e ∧ polar Q P.e (h1 (a - v)) = 4 * Q a / α := by
  set w1 : V := α⁻¹ • (α • P.e - (a + v)) with hw1
  set h1 : V ≃ₗ[K] V := eichler Q P.f w1 with hh1
  have hw1f : polar Q P.f w1 = 0 := by
    simp only [hw1, polar_smul_right_eq, polar_sub_right, P.polar_fe, hpfup, mul_one, sub_self,
      mul_zero]
  have hfe' : polar Q P.f (α • P.e) = α := by
    rw [polar_smul_right_eq, P.polar_fe, mul_one]
  have h1up : h1 (a + v) = α • P.e := by
    rw [hh1, hw1]
    exact eichler_apply_eq_of_polar_eq P.Q_f (by rw [hQup, map_smul_eq_sq, P.Q_e, mul_zero])
      hpfup hfe' hα0
  have h1X : h1 ∈ X := by rw [hh1]; exact hf.2.2 w1 hw1f
  have h1O : h1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hh1]; exact eichler_mem_orthogonalGroup Q P.f w1
  have hpew1 : polar Q P.e w1 = Q a / α ^ 2 := by
    simp only [hw1, polar_smul_right_eq, polar_sub_right, P.polar_ee, hpeup, mul_zero]
    field_simp [hα0]; ring
  have hQw1 : Q w1 = Q a / α ^ 2 := by
    rw [hw1, map_smul_eq_sq]
    have hQsub : Q (α • P.e - (a + v)) = Q a := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q (α • P.e) (-(a + v)), QuadraticMap.map_neg,
        map_smul_eq_sq, P.Q_e, hQup, polar_neg_right, polar_smul_left_eq, hpeup]
      field_simp [hα0]; ring
    rw [hQsub]
    field_simp [hα0]
  have hpumw1 : polar Q (a - v) w1 = -3 * Q a / α := by
    simp only [hw1, polar_smul_right_eq, polar_sub_right, polar_comm Q (a - v) P.e, hpeum,
      humup]
    field_simp [hα0]; ring
  refine ⟨h1, h1X, h1O, h1up, ?_⟩
  rw [hh1, eichler_apply P.Q_f hw1f (a - v)]
  simp only [polar_sub_right, polar_add_right, polar_smul_right_eq, hpeum, hpumf, hpew1,
    hpumw1, hQw1, P.polar_ef, mul_one]
  field_simp [hα0]; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_h2 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) (P : HypPair Q) {X : Subgroup (V ≃ₗ[K] V)}
    (he : IsRootCenter Q X P.e) {a v : V} {α : K} (hQa : Q a ≠ 0) (hα0 : α ≠ 0)
    {h1 : V ≃ₗ[K] V} (hQum : Q (a - v) = 0)
    (hpe : polar Q P.e (h1 (a - v)) = 4 * Q a / α) (h1X : h1 ∈ X)
    (h1O : h1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1up : h1 (a + v) = α • P.e) :
    ∃ g : V ≃ₗ[K] V, g ∈ X ∧ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      g (a + v) = α • P.e ∧ g (a - v) = (4 * Q a / α) • P.f := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4a : 4 * Q a / α ≠ 0 := div_ne_zero (mul_ne_zero h4 hQa) hα0
  set w2 : V := (4 * Q a / α)⁻¹ • ((4 * Q a / α) • P.f - h1 (a - v)) with hw2
  set h2' : V ≃ₗ[K] V := eichler Q P.e w2 with hh2
  have hfe2 : polar Q P.e ((4 * Q a / α) • P.f) = 4 * Q a / α := by
    rw [polar_smul_right_eq, P.polar_ef, mul_one]
  have h2h1 : h2' (h1 (a - v)) = (4 * Q a / α) • P.f := by
    rw [hh2, hw2]
    exact eichler_apply_eq_of_polar_eq he.2.1
      (by rw [map_of_mem h1O (a - v), hQum, map_smul_eq_sq, P.Q_f, mul_zero]) hpe hfe2 h4a
  have h2e : h2' P.e = P.e := by rw [hh2]; exact eichler_apply_self P.e w2
  have h2X : h2' ∈ X := by
    rw [hh2]
    exact he.2.2 w2 (by
      rw [hw2, polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, P.polar_ef, hpe,
        mul_one, sub_self, mul_zero])
  have h2O : h2' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hh2]; exact eichler_mem_orthogonalGroup Q P.e w2
  set g : V ≃ₗ[K] V := h2' * h1 with hg
  have hgX : g ∈ X := by rw [hg]; exact X.mul_mem h2X h1X
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hg]; exact Subgroup.mul_mem _ h2O h1O
  have hgup : g (a + v) = α • P.e := by
    rw [hg, LinearEquiv.mul_apply, h1up, map_smul, h2e]
  have hgum : g (a - v) = (4 * Q a / α) • P.f := by
    rw [hg, LinearEquiv.mul_apply, h2h1]
  exact ⟨g, hgX, hgO, hgup, hgum⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_mem_perp_of_orth {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {g : V ≃ₗ[K] V} {b' a v : V} {α β : K}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb'up : polar Q b' (a + v) = 0) (hb'um : polar Q b' (a - v) = 0)
    (hgup : g (a + v) = α • P.e) (hgum : g (a - v) = β • P.f) (hα0 : α ≠ 0)
    (hβ0 : β ≠ 0) : g b' ∈ P.perp := by
  have hbe : polar Q (g b') P.e = 0 := by
    have h := polar_map_of_mem hgO b' (a + v)
    rw [hgup, hb'up, polar_smul_right_eq] at h
    exact (mul_eq_zero.mp h).resolve_left hα0
  have hbf : polar Q (g b') P.f = 0 := by
    have h := polar_map_of_mem hgO b' (a - v)
    rw [hgum, hb'um, polar_smul_right_eq] at h
    exact (mul_eq_zero.mp h).resolve_left hβ0
  exact HypPair.mem_perp.mpr ⟨by rw [polar_comm]; exact hbe, by rw [polar_comm]; exact hbf⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_mem_apply_eq_or_neg_of_perp_le_span {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {X : Subgroup (V ≃ₗ[K] V)}
    (P : HypPair Q) (he : IsRootCenter Q X P.e) (hf : IsRootCenter Q X P.f) {a : V}
    (ha : a ∈ P.perp) (hQa : Q a ≠ 0) (hspan : P.perp ≤ Submodule.span K {a}) {b : V}
    (hb : Q b = Q a) : ∃ g ∈ X, g b = a ∨ g b = -a := by
  have hb0 : Q b ≠ 0 := by rw [hb]; exact hQa
  obtain ⟨g0, hg0X, α, hα0, hg0b⟩ := exists_mem_apply_eq_hypNormal h2 P he hf hb0
  rw [hb] at hg0b
  set v : V := α • P.e - (Q a / α) • P.f with hv
  obtain ⟨hQv, hav, hpev, hvf⟩ := ocg_v_facts P ha hα0
  rw [← hv] at hQv hav hpev hvf
  obtain ⟨hQup, hQum⟩ := ocg_Q_um_up hQv hav
  obtain ⟨hpeup, hpfup⟩ := ocg_polar_up P ha hpev hvf
  obtain ⟨hpeum, hpumf⟩ := ocg_polar_um P ha hpev hvf
  have humup : polar Q (a - v) (a + v) = 4 * Q a := ocg_polar_um_up hQv hav
  obtain ⟨h1, h1X, h1O, h1up, hpe⟩ :=
    ocg_h1 P hf hα0 hQup hpeup hpfup hpeum hpumf humup
  obtain ⟨g, hgX, hgO, hgup, hgum⟩ := ocg_h2 h2 P he hQa hα0 hQum hpe h1X h1O h1up
  set b' : V := α • P.e + (Q a / α) • P.f with hb'
  have hg0b' : g0 b = b' := by rw [hb']; exact hg0b
  obtain ⟨hb'a, hb'v, hQb'⟩ := ocg_b'_facts P ha hα0
  rw [← hb'] at hb'a hb'v hQb'
  have hb'up : polar Q b' (a + v) = 0 := by
    rw [polar_add_right, hb'a, hb'v, add_zero]
  have hb'um : polar Q b' (a - v) = 0 := by
    rw [sub_eq_add_neg, polar_add_right, polar_neg_right, hb'a, hb'v, neg_zero, add_zero]
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4a : 4 * Q a / α ≠ 0 := div_ne_zero (mul_ne_zero h4 hQa) hα0
  have hgb'perp : g b' ∈ P.perp :=
    ocg_mem_perp_of_orth P hgO hb'up hb'um hgup hgum hα0 h4a
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hspan hgb'perp)
  have hQs : s ^ 2 = 1 := by
    have h1' : Q (g b') = Q a := by rw [map_of_mem hgO b', hQb']
    have h2' : s ^ 2 * Q a = Q a := by
      have h3 : Q (s • a) = Q a := by rw [hs]; exact h1'
      rwa [map_smul_eq_sq] at h3
    exact mul_right_cancel₀ hQa (by rw [h2', one_mul])
  rcases sq_eq_one_iff.mp hQs with hs1 | hs1
  · refine ⟨g * g0, X.mul_mem hgX hg0X, Or.inl ?_⟩
    rw [LinearEquiv.mul_apply, hg0b']
    rw [hs1, one_smul] at hs
    exact hs.symm
  · refine ⟨g * g0, X.mul_mem hgX hg0X, Or.inr ?_⟩
    rw [LinearEquiv.mul_apply, hg0b']
    rw [hs1, neg_one_smul] at hs
    exact hs.symm

private lemma ocg_zmod2_isSquare (y : ZMod 2) : IsSquare y := by
  have hy : y = 0 ∨ y = 1 := by
    have h2 : y.val < 2 := ZMod.val_lt y
    rcases (Nat.lt_succ_iff_lt_or_eq.mp h2) with h | h
    · left
      apply ZMod.val_injective 2
      rw [ZMod.val_zero]
      omega
    · right
      apply ZMod.val_injective 2
      rw [ZMod.val_one]
      exact h
  rcases hy with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_Q_add_x {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {x : U}
    (hx : x ∈ P.perp) (r t s : ZMod p) :
    Q (r • P.e + t • P.f + s • x) = r * t + s ^ 2 * Q x := by
  have hxe : polar Q P.e x = 0 := (HypPair.mem_perp.mp hx).1
  have hxf : polar Q P.f x = 0 := (HypPair.mem_perp.mp hx).2
  rw [QuadraticMap.map_add Q (r • P.e + t • P.f) (s • x), ocg_plane_Q P r t, map_smul_eq_sq]
  have hzero : polar Q (r • P.e + t • P.f) (s • x) = 0 := by
    simp only [polar_add_left, polar_smul_left_eq, polar_smul_right_eq, hxe, hxf, mul_zero,
      add_zero]
  rw [hzero, add_zero]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_e_add_x {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {x : U}
    (hx : x ∈ P.perp) (r t s : ZMod p) :
    polar Q P.e (r • P.e + t • P.f + s • x) = t := by
  have hxe : polar Q P.e x = 0 := (HypPair.mem_perp.mp hx).1
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_smul_right_eq, P.polar_ee, P.polar_ef, hxe]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_f_add_x {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {x : U}
    (hx : x ∈ P.perp) (r t s : ZMod p) :
    polar Q P.f (r • P.e + t • P.f + s • x) = r := by
  have hxf : polar Q P.f x = 0 := (HypPair.mem_perp.mp hx).2
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_smul_right_eq, P.polar_fe, P.polar_ff, hxf]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_step_alpha1 {Q : QuadraticForm (ZMod p) U} {x : U} {c : ZMod p}
    (hsq : ¬ IsSquare (c / Q x)) (hc : c ≠ 0) (hQx : Q x ≠ 0)
    {α : ZMod p} (hα0 : α ≠ 0) (s : ZMod p) :
    α * (1 - s ^ 2 * Q x / c) ≠ 0 := by
  refine mul_ne_zero hα0 (fun h => hsq ⟨s, ?_⟩)
  have hc_eq : c = s ^ 2 * Q x := by
    have h1 : s ^ 2 * Q x / c = 1 := (sub_eq_zero.mp h).symm
    field_simp [hc] at h1
    exact h1.symm
  rw [hc_eq]
  field_simp [hQx]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_step_z {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {x : U}
    (hx : x ∈ P.perp) {c : ZMod p} (hc : c ≠ 0)
    {α : ZMod p} (hα0 : α ≠ 0) (s : ZMod p) :
    Q ((α * (1 - s ^ 2 * Q x / c)) • P.e + (c / α) • P.f + s • x) = c ∧
    polar Q P.e ((α * (1 - s ^ 2 * Q x / c)) • P.e + (c / α) • P.f + s • x) = c / α ∧
    polar Q P.f ((α * (1 - s ^ 2 * Q x / c)) • P.e + (c / α) • P.f + s • x) =
      α * (1 - s ^ 2 * Q x / c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ocg_Q_add_x P hx]; field_simp [hc]; ring
  · rw [ocg_polar_e_add_x P hx]
  · rw [ocg_polar_f_add_x P hx]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_step {Q : QuadraticForm (ZMod p) U} (P : HypPair Q)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (he : IsRootCenter Q X P.e) (hf : IsRootCenter Q X P.f)
    {x : U} (hx : x ∈ P.perp) {c : ZMod p} (hsq : ¬ IsSquare (c / Q x))
    (hc : c ≠ 0) (hQx : Q x ≠ 0) (α s : ZMod p) (hα0 : α ≠ 0) :
    ∃ g ∈ X, g (α • P.e + (c / α) • P.f) =
      (α * (1 - s ^ 2 * Q x / c)) • P.e + (c / (α * (1 - s ^ 2 * Q x / c))) • P.f := by
  set α1 : ZMod p := α * (1 - s ^ 2 * Q x / c) with hα1
  have hα10 : α1 ≠ 0 := by rw [hα1]; exact ocg_step_alpha1 hsq hc hQx hα0 s
  set z : U := α1 • P.e + (c / α) • P.f + s • x with hz
  obtain ⟨hQz, hez, hfz⟩ := ocg_step_z P hx hc hα0 s
  rw [← hz] at hQz hez hfz
  rw [← hα1] at hfz
  have hQyα : Q (α • P.e + (c / α) • P.f) = c := by
    rw [ocg_plane_Q P α (c / α)]; field_simp [hα0]
  have heyα : polar Q P.e (α • P.e + (c / α) • P.f) = c / α := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef]; ring
  have hfyα : polar Q P.f (α • P.e + (c / α) • P.f) = α := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]; ring
  have hQyα1 : Q (α1 • P.e + (c / α1) • P.f) = c := by
    rw [ocg_plane_Q P α1 (c / α1)]; field_simp [hα10]
  have hfyα1 : polar Q P.f (α1 • P.e + (c / α1) • P.f) = α1 := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]; ring
  set g1 : U ≃ₗ[ZMod p] U :=
    eichler Q P.e ((c / α)⁻¹ • (z - (α • P.e + (c / α) • P.f))) with hg1
  have hg1X : g1 ∈ X := by
    rw [hg1]
    exact he.2.2 _ (by
      rw [polar_smul_right_eq, polar_sub_right, hez, heyα, sub_self, mul_zero])
  have hg1y : g1 (α • P.e + (c / α) • P.f) = z := by
    rw [hg1]
    exact eichler_apply_eq_of_polar_eq he.2.1 (by rw [hQyα, hQz]) heyα hez
      (div_ne_zero hc hα0)
  set g2 : U ≃ₗ[ZMod p] U :=
    eichler Q P.f (α1⁻¹ • ((α1 • P.e + (c / α1) • P.f) - z)) with hg2
  have hg2X : g2 ∈ X := by
    rw [hg2]
    exact hf.2.2 _ (by
      rw [polar_smul_right_eq, polar_sub_right, hfyα1, hfz, sub_self, mul_zero])
  have hg2z : g2 z = α1 • P.e + (c / α1) • P.f := by
    rw [hg2]
    exact eichler_apply_eq_of_polar_eq hf.2.1 (by rw [hQz, hQyα1]) hfz hfyα1 hα10
  refine ⟨g2 * g1, X.mul_mem hg2X hg1X, ?_⟩
  rw [LinearEquiv.mul_apply, hg1y, hg2z]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_match_alpha {Q : QuadraticForm (ZMod p) U} {x : U} {c : ZMod p}
    {α α' s s' : ZMod p} (hc : c ≠ 0) (hQx : Q x ≠ 0)
    (h : α * s ^ 2 - α' * s' ^ 2 = (α - α') * c / Q x) :
    α * (1 - s ^ 2 * Q x / c) = α' * (1 - s' ^ 2 * Q x / c) := by
  have key : (α * s ^ 2 - α' * s' ^ 2) * Q x = (α - α') * c := by
    have h' := congrArg (· * Q x) h
    rw [div_mul_cancel₀ _ hQx] at h'
    exact h'
  apply mul_right_cancel₀ hc
  have e1 : (α * (1 - s ^ 2 * Q x / c)) * c = α * (c - s ^ 2 * Q x) := by
    field_simp [hc]
  have e2 : (α' * (1 - s' ^ 2 * Q x / c)) * c = α' * (c - s' ^ 2 * Q x) := by
    field_simp [hc]
  rw [e1, e2]
  linear_combination -key

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_mem_apply_eq_of_not_isSquare_div {Q : QuadraticForm (ZMod p) U}
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (P : HypPair Q) (he : IsRootCenter Q X P.e)
    (hf : IsRootCenter Q X P.f) {x : U} (hx : x ∈ P.perp) {c : ZMod p}
    (hsq : ¬ IsSquare (c / Q x)) {a b : U} (ha : Q a = c) (hb : Q b = c) : ∃ g ∈ X, g a = b := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hsq (ocg_zmod2_isSquare _)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hsq ⟨0, by simp⟩
  have hQx : Q x ≠ 0 := by
    rintro h0
    exact hsq (by rw [h0, div_zero]; exact ⟨0, by simp⟩)
  have h2p : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) Nat.prime_two hp2
  have hQa0 : Q a ≠ 0 := by rw [ha]; exact hc
  have hQb0 : Q b ≠ 0 := by rw [hb]; exact hc
  obtain ⟨ga, hgaX, α, hα0, hga⟩ := exists_mem_apply_eq_hypNormal h2p P he hf hQa0
  obtain ⟨gb, hgbX, α', hα'0, hgb⟩ := exists_mem_apply_eq_hypNormal h2p P he hf hQb0
  rw [ha] at hga
  rw [hb] at hgb
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p]
    exact Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨s, s', hs⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq (K := ZMod p)
    hcard hα0 (neg_ne_zero.mpr hα'0) ((α - α') * c / Q x)
  have hs' : α * s ^ 2 - α' * s' ^ 2 = (α - α') * c / Q x := by
    linear_combination hs
  have hα1' := ocg_match_alpha hc hQx hs'
  obtain ⟨g1, hg1X, hg1⟩ := ocg_step P he hf hx hsq hc hQx α s hα0
  obtain ⟨g2, hg2X, hg2⟩ := ocg_step P he hf hx hsq hc hQx α' s' hα'0
  have hg2' : g2 (α' • P.e + (c / α') • P.f) =
      (α * (1 - s ^ 2 * Q x / c)) • P.e +
        (c / (α * (1 - s ^ 2 * Q x / c))) • P.f := by
    rw [hg2, hα1']
  refine ⟨gb⁻¹ * g2⁻¹ * g1 * ga, ?_, ?_⟩
  · exact X.mul_mem (X.mul_mem (X.mul_mem (X.inv_mem hgbX) (X.inv_mem hg2X)) hg1X) hgaX
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hga, hg1]
    rw [← hg2', LinearEquiv.inv_apply_apply', ← hgb, LinearEquiv.inv_apply_apply']

end CFSG.StandardType.ZS
