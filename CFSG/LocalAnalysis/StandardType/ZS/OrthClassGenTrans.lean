module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import Mathlib.Algebra.Field.ZMod
import CFSG.RankThree.Classical.OddQuadraticFrame

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_Q_smul_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s r : K) :
    Q (s • P.e + r • P.f) = s * r := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_Q_add_perp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {w : V} (hw : w ∈ P.perp) (s r : K) :
    Q (s • P.e + r • P.f + w) = s * r + Q w := by
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp hw
  rw [QuadraticMap.map_add Q, ocgT_Q_smul_add_smul P s r, polar_add_left, polar_smul_left_eq,
    polar_smul_left_eq, hew, hfw]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_polar_e_smul_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s r : K) :
    polar Q P.e (s • P.e + r • P.f) = r := by
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_polar_f_smul_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s r : K) :
    polar Q P.f (s • P.e + r • P.f) = s := by
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_fe, P.polar_ff]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_polar_e_add_perp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {w : V} (hw : w ∈ P.perp) (s r : K) :
    polar Q P.e (s • P.e + r • P.f + w) = r := by
  obtain ⟨hew, _⟩ := HypPair.mem_perp.mp hw
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    P.polar_ee, P.polar_ef, hew]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_polar_f_add_perp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {w : V} (hw : w ∈ P.perp) (s r : K) :
    polar Q P.f (s • P.e + r • P.f + w) = s := by
  obtain ⟨_, hfw⟩ := HypPair.mem_perp.mp hw
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    P.polar_fe, P.polar_ff, hfw]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_normal_of_polar_ne_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {X : Subgroup (V ≃ₗ[K] V)} (P : HypPair Q)
    (he : IsRootCenter Q X P.e) {b : V} (hb : Q b ≠ 0) (hβ : polar Q P.e b ≠ 0) :
    ∃ g ∈ X, ∃ α : K, α ≠ 0 ∧ g b = α • P.e + (Q b / α) • P.f := by
  set β : K := polar Q P.e b with hβdef
  have hβ0 : β ≠ 0 := by rw [hβdef]; exact hβ
  set α : K := Q b / β with hαdef
  have hα : α ≠ 0 := by rw [hαdef]; exact div_ne_zero hb hβ0
  set z : V := α • P.e + β • P.f with hzdef
  have hQz : Q z = Q b := by
    rw [hzdef, ocgT_Q_smul_add_smul P α β, hαdef, div_mul_cancel₀ (Q b) hβ0]
  have hzB : polar Q P.e z = β := by
    rw [hzdef, ocgT_polar_e_smul_add_smul P α β]
  have hpol : polar Q P.e (β⁻¹ • (z - b)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hzB, ← hβdef, sub_self, mul_zero]
  have hmap : eichler Q P.e (β⁻¹ • (z - b)) b = z :=
    eichler_apply_eq_of_polar_eq he.2.1 hQz.symm hβdef.symm hzB hβ0
  refine ⟨eichler Q P.e (β⁻¹ • (z - b)), he.2.2 _ hpol, α, hα, ?_⟩
  have hcoef : Q b / α = β := by
    rw [hαdef]
    field_simp [hb, hβ0]
  rw [hmap, hzdef, hcoef]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_normal_of_polar_fe_ne_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {X : Subgroup (V ≃ₗ[K] V)} (P : HypPair Q)
    (hf : IsRootCenter Q X P.f) {b : V} (hγ : polar Q P.f b ≠ 0) :
    ∃ g ∈ X, ∃ α : K, α ≠ 0 ∧ g b = α • P.e + (Q b / α) • P.f := by
  set γ : K := polar Q P.f b with hγdef
  have hγ0 : γ ≠ 0 := by rw [hγdef]; exact hγ
  set z : V := γ • P.e + (Q b / γ) • P.f with hzdef
  have hQz : Q z = Q b := by
    rw [hzdef, ocgT_Q_smul_add_smul P γ (Q b / γ), mul_div_cancel₀ (Q b) hγ0]
  have hzB : polar Q P.f z = γ := by
    rw [hzdef, ocgT_polar_f_smul_add_smul P γ (Q b / γ)]
  have hpol : polar Q P.f (γ⁻¹ • (z - b)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hzB, ← hγdef, sub_self, mul_zero]
  have hmap : eichler Q P.f (γ⁻¹ • (z - b)) b = z :=
    eichler_apply_eq_of_polar_eq hf.2.1 hQz.symm hγdef.symm hzB hγ0
  exact ⟨eichler Q P.f (γ⁻¹ • (z - b)), hf.2.2 _ hpol, γ, hγ0, by rw [hmap, hzdef]⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_hypPair_mem_perp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {a u : V}
    (ha : Q a ≠ 0) (hu0 : u ≠ 0) (hu : Q u = 0) (hau : polar Q a u = 0) :
    ∃ P : HypPair Q, P.e = u ∧ a ∈ P.perp := by
  obtain ⟨y₀, hy₀⟩ := exists_polar_ne_zero hQ hu0
  have haa : polar Q a a ≠ 0 := by
    rw [polar_self_eq_two_mul Q a]
    exact mul_ne_zero h2 ha
  set y : V := y₀ - (polar Q a y₀ / polar Q a a) • a with hydef
  have hay : polar Q a y = 0 := by
    rw [hydef, polar_sub_right, polar_smul_right_eq, div_mul_cancel₀ (polar Q a y₀) haa,
      sub_self]
  have huy : polar Q u y = polar Q u y₀ := by
    rw [hydef, polar_sub_right, polar_smul_right_eq, polar_comm Q u a, hau, mul_zero, sub_zero]
  have huy0 : polar Q u y ≠ 0 := by rw [huy]; exact hy₀
  have h1 : polar Q u ((polar Q u y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ huy0]
  refine ⟨HypPair.ofPolarEqOne hu h1, HypPair.ofPolarEqOne_e hu h1, ?_⟩
  rw [HypPair.mem_perp, HypPair.ofPolarEqOne_e, HypPair.ofPolarEqOne_f]
  refine ⟨?_, ?_⟩
  · rw [polar_comm Q u a]; exact hau
  · rw [polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q u a, hau, mul_zero,
      sub_zero, polar_comm Q y a, hay, mul_zero]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_mem_apply_eq_hypNormal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {X : Subgroup (V ≃ₗ[K] V)} (P : HypPair Q)
    (he : IsRootCenter Q X P.e) (hf : IsRootCenter Q X P.f) {b : V} (hb : Q b ≠ 0) :
    ∃ g ∈ X, ∃ α : K, α ≠ 0 ∧ g b = α • P.e + (Q b / α) • P.f := by
  by_cases hβ : polar Q P.e b = 0
  · by_cases hγ : polar Q P.f b = 0
    · have hb'form : eichler Q P.e b b = b - (2 * Q b) • P.e := by
        rw [eichler_apply he.2.1 hβ, polar_comm Q b P.e, hβ, polar_self_eq_two_mul Q b]
        simp only [zero_smul, mul_zero, add_zero]
      have hb'Q : Q (eichler Q P.e b b) = Q b :=
        map_of_mem (eichler_mem_orthogonalGroup Q P.e b) b
      have hb' : Q (eichler Q P.e b b) ≠ 0 := by rw [hb'Q]; exact hb
      have hγ' : polar Q P.f (eichler Q P.e b b) ≠ 0 := by
        rw [hb'form, polar_sub_right, polar_smul_right_eq, P.polar_fe, mul_one, hγ, zero_sub]
        exact neg_ne_zero.mpr (mul_ne_zero h2 hb)
      obtain ⟨g₁, hg₁X, α, hα, hg₁⟩ :=
        ocgT_normal_of_polar_fe_ne_zero (b := eichler Q P.e b b) P hf hγ'
      refine ⟨g₁ * eichler Q P.e b, X.mul_mem hg₁X (he.2.2 b hβ), α, hα, ?_⟩
      rw [LinearEquiv.mul_apply, hg₁, hb'Q]
    · exact ocgT_normal_of_polar_fe_ne_zero P hf hγ
  · exact ocgT_normal_of_polar_ne_zero P he hb hβ

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocgT_join_normal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {X : Subgroup (V ≃ₗ[K] V)} (P : HypPair Q)
    (he : IsRootCenter Q X P.e) (hf : IsRootCenter Q X P.f) {c : K} (hc : c ≠ 0)
    {α α' : K} (hα : α ≠ 0) (hα' : α' ≠ 0) {w : V} (hwperp : w ∈ P.perp)
    (hwQ : Q w = c * (1 - α' / α)) :
    ∃ h ∈ X, h (α • P.e + (c / α) • P.f) = α' • P.e + (c / α') • P.f := by
  set A : V := α • P.e + (c / α) • P.f with hAdef
  set B : V := α' • P.e + (c / α') • P.f with hBdef
  set z : V := α' • P.e + (c / α) • P.f + w with hzdef
  have hQA : Q A = c := by
    rw [hAdef, ocgT_Q_smul_add_smul P α (c / α), mul_div_cancel₀ c hα]
  have hQB : Q B = c := by
    rw [hBdef, ocgT_Q_smul_add_smul P α' (c / α'), mul_div_cancel₀ c hα']
  have hQz : Q z = c := by
    rw [hzdef, ocgT_Q_add_perp P hwperp α' (c / α), hwQ]
    field_simp [hα]
    ring
  have hApol : polar Q P.e A = c / α := by
    rw [hAdef, ocgT_polar_e_smul_add_smul P α (c / α)]
  have hBpol : polar Q P.f B = α' := by
    rw [hBdef, ocgT_polar_f_smul_add_smul P α' (c / α')]
  have hzpol_e : polar Q P.e z = c / α := by
    rw [hzdef, ocgT_polar_e_add_perp P hwperp α' (c / α)]
  have hzpol_f : polar Q P.f z = α' := by
    rw [hzdef, ocgT_polar_f_add_perp P hwperp α' (c / α)]
  have hE₁mem : eichler Q P.e ((c / α)⁻¹ • (z - A)) ∈ X := by
    apply he.2.2
    rw [polar_smul_right_eq, polar_sub_right, hApol, hzpol_e, sub_self, mul_zero]
  have hE₂mem : eichler Q P.f ((α')⁻¹ • (B - z)) ∈ X := by
    apply hf.2.2
    rw [polar_smul_right_eq, polar_sub_right, hzpol_f, hBpol, sub_self, mul_zero]
  have hE₁ : eichler Q P.e ((c / α)⁻¹ • (z - A)) A = z :=
    eichler_apply_eq_of_polar_eq he.2.1 (by rw [hQA, hQz]) hApol hzpol_e (div_ne_zero hc hα)
  have hE₂ : eichler Q P.f ((α')⁻¹ • (B - z)) z = B :=
    eichler_apply_eq_of_polar_eq hf.2.1 (by rw [hQz, hQB]) hzpol_f hBpol hα'
  refine ⟨eichler Q P.f ((α')⁻¹ • (B - z)) * eichler Q P.e ((c / α)⁻¹ • (z - A)), ?_, ?_⟩
  · exact X.mul_mem hE₂mem hE₁mem
  · rw [LinearEquiv.mul_apply, hE₁, hE₂]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_mem_apply_eq_of_perp_represents {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {X : Subgroup (V ≃ₗ[K] V)}
    (P : HypPair Q) (he : IsRootCenter Q X P.e) (hf : IsRootCenter Q X P.f)
    (huniv : ∀ t : K, ∃ w ∈ P.perp, Q w = t) {a b : V} (ha : Q a ≠ 0) (hab : Q a = Q b) :
    ∃ g ∈ X, g a = b := by
  have hb : Q b ≠ 0 := by rw [← hab]; exact ha
  obtain ⟨ga, hgaX, α, hα, hga⟩ := exists_mem_apply_eq_hypNormal h2 P he hf ha
  obtain ⟨gb, hgbX, α', hα', hgb⟩ := exists_mem_apply_eq_hypNormal h2 P he hf hb
  obtain ⟨w, hwperp, hwQ⟩ := huniv (Q a * (1 - α' / α))
  obtain ⟨h, hhX, hh⟩ := ocgT_join_normal P he hf ha hα hα' hwperp hwQ
  refine ⟨gb⁻¹ * h * ga, X.mul_mem (X.mul_mem (X.inv_mem hgbX) hhX) hgaX, ?_⟩
  simp only [LinearEquiv.mul_apply]
  rw [hga, hh, hab, ← hgb, LinearEquiv.inv_apply_apply']

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_mem_map_eq_of_two_le_finrank (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {W : Submodule (ZMod p) U} (hW : PolarNondegOn Q W) (h2 : 2 ≤ Module.finrank (ZMod p) W)
    (t : ZMod p) : ∃ w ∈ W, Q w = t := by
  by_cases ht : t = 0
  · exact ⟨0, W.zero_mem, by rw [ht, QuadraticMap.map_zero]⟩
  · have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have : Finite (ZMod p) := Finite.of_fintype (ZMod p)
    have : FiniteDimensional (ZMod p) W := FiniteDimensional.of_finrank_pos (by omega)
    have hK : Odd (Nat.card (ZMod p)) := by
      rw [Nat.card_zmod]
      exact (Fact.out : p.Prime).odd_of_ne_two hp
    have hB : LinearMap.BilinForm.Nondegenerate (polarBilin (Q.comp W.subtype)) := by
      refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · apply Subtype.ext
        apply hW x x.2
        intro y hy'
        have h := hx ⟨y, hy'⟩
        rwa [polarBilin_comp, LinearMap.compl₁₂_apply, polarBilin_apply_apply] at h
      · apply Subtype.ext
        apply hW y y.2
        intro x hx'
        have h := hy ⟨x, hx'⟩
        rw [polarBilin_comp, LinearMap.compl₁₂_apply, polarBilin_apply_apply, polar_comm] at h
        exact h
    have : NeZero (Module.finrank (ZMod p) W) := ⟨by omega⟩
    obtain ⟨v, -, hv, -⟩ :=
      CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := W) hK
        (d := Module.finrank (ZMod p) W) rfl h2 (Q.comp W.subtype) hB ht
    refine ⟨(v 0 : W), (v 0).2, ?_⟩
    have hv0 := hv 0 (by simp; omega)
    simpa [QuadraticMap.comp_apply] using hv0

end CFSG.StandardType.ZS
