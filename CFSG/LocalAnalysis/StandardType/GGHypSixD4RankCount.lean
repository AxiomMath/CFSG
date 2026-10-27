module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

namespace D4Rank

open Module
open scoped Pointwise

abbrev fp {R : Type*} [Ring R] (z : R) : R := 1 + z + z ^ 2

section Ring

variable {R : Type*} [CommRing R]

theorem ring_fixProj_sq (h2 : (2 : R) = 0) {g : R} (hg : g ^ 3 = 1) : fp g * fp g = fp g := by
  linear_combination (g + 2) * hg + (g ^ 2 + g + 1) * h2

theorem ring_fixProj_mul_g_gh {g h : R} (hg : g ^ 3 = 1) : fp g * fp (g * h) = fp g * fp h := by
  linear_combination (g * h ^ 2 + h ^ 2 + h) * hg

theorem ring_fixProj_mul_g_gh2 {g h : R} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) :
    fp g * fp (g * h ^ 2) = fp g * fp h := by
  linear_combination (g * h ^ 4 + h ^ 4 + h ^ 2) * hg + (g ^ 2 * h + g * h + h) * hh

theorem ring_fixProj_mul_h_gh {g h : R} (hh : h ^ 3 = 1) : fp h * fp (g * h) = fp g * fp h := by
  linear_combination (g ^ 2 * h + g ^ 2 + g) * hh

theorem ring_fixProj_mul_h_gh2 {g h : R} (hh : h ^ 3 = 1) :
    fp h * fp (g * h ^ 2) = fp g * fp h := by
  linear_combination (g ^ 2 * h ^ 3 + g ^ 2 * h ^ 2 + g ^ 2 * h + g ^ 2 + g * h + g) * hh

theorem ring_fixProj_mul_gh_gh2 {g h : R} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) :
    fp (g * h) * fp (g * h ^ 2) = fp g * fp h := by
  linear_combination (g * h ^ 6 + h ^ 5 + h ^ 4) * hg +
    (g ^ 2 * h + g ^ 2 + g * h ^ 3 + g + h ^ 2 + h) * hh

theorem ring_fixProj_sum (h2 : (2 : R) = 0) {g h : R} (hh : h ^ 3 = 1) :
    fp g + fp h + fp (g * h) + fp (g * h ^ 2) = 1 + fp g * fp h := by
  linear_combination (g ^ 2 * h) * hh + h2

end Ring

section Rank

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable abbrev rk (f : Module.End K V) : ℕ := finrank K (LinearMap.range f)

noncomputable abbrev fixDim (f : Module.End K V) : ℕ := finrank K (LinearMap.ker (f - 1))

variable [FiniteDimensional K V]

theorem rk_add_of_orth {e f : Module.End K V} (he : e * e = e) (hef : e * f = 0)
    (hfe : f * e = 0) (hf : f * f = f) : rk (e + f) = rk e + rk f := by
  have hsup : LinearMap.range (e + f) = LinearMap.range e ⊔ LinearMap.range f := by
    refine le_antisymm (LinearMap.range_add_le e f) (sup_le ?_ ?_)
    · rintro _ ⟨v, rfl⟩
      refine ⟨e v, ?_⟩
      have h1 : (e * e) v = e v := by rw [he]
      have h2 : (f * e) v = 0 := by rw [hfe]; rfl
      simp only [LinearMap.add_apply]
      rw [Module.End.mul_apply] at h1 h2
      rw [h1, h2, add_zero]
    · rintro _ ⟨v, rfl⟩
      refine ⟨f v, ?_⟩
      have h1 : (f * f) v = f v := by rw [hf]
      have h2 : (e * f) v = 0 := by rw [hef]; rfl
      simp only [LinearMap.add_apply]
      rw [Module.End.mul_apply] at h1 h2
      rw [h1, h2, zero_add]
  have hinf : LinearMap.range e ⊓ LinearMap.range f = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, ⟨w, hw⟩⟩
    have h1 : (e * e) u = e u := by rw [he]
    have h2 : (e * f) w = 0 := by rw [hef]; rfl
    rw [Module.End.mul_apply] at h1 h2
    rw [Submodule.mem_bot, ← h1, ← hw, h2]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) (LinearMap.range f)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  exact h

theorem rk_sum_of_orth {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → Module.End K V)
    (he : ∀ i ∈ s, e i * e i = e i) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    rk (∑ i ∈ s, e i) = ∑ i ∈ s, rk (e i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    show finrank K (LinearMap.range (0 : V →ₗ[K] V)) = 0
    rw [LinearMap.range_zero, finrank_bot]
  | insert a s ha ih =>
    have he' : ∀ i ∈ s, e i * e i = e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have horth' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0 := fun i hi j hj hij =>
      horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hne : ∀ i ∈ s, a ≠ i := fun i hi h => ha (h ▸ hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih he' horth']
    refine rk_add_of_orth (he a (Finset.mem_insert_self a s)) ?_ ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => horth a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (hne i hi)
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i hi => horth i (Finset.mem_insert_of_mem hi) a
        (Finset.mem_insert_self a s) (hne i hi).symm
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => horth' i hi j hj hji.symm)
        (fun h => absurd hi h), he' i hi]

theorem rank_formula {A : Type*} [CommRing A] (φ : A →+* Module.End K V) (h2 : (2 : A) = 0)
    {q₁ q₂ q₃ q₄ T P : A} (h₁ : q₁ * q₁ = q₁) (h₂ : q₂ * q₂ = q₂) (h₃ : q₃ * q₃ = q₃)
    (h₄ : q₄ * q₄ = q₄) (h12 : q₁ * q₂ = T) (h13 : q₁ * q₃ = T) (h14 : q₁ * q₄ = T)
    (h23 : q₂ * q₃ = T) (h24 : q₂ * q₄ = T) (h34 : q₃ * q₄ = T)
    (hsum : q₁ + q₂ + q₃ + q₄ = P + T) :
    rk (φ q₁) + rk (φ q₂) + rk (φ q₃) + rk (φ q₄) = rk (φ P) + 3 * rk (φ T) := by
  have hTT : T * T = T := by
    rw [← h12]; linear_combination q₂ ^ 2 * h₁ + q₁ * h₂
  have hT1 : T * q₁ = T := by rw [← h12]; linear_combination q₂ * h₁
  have hT2 : T * q₂ = T := by rw [← h12]; linear_combination q₁ * h₂
  have hT3 : T * q₃ = T := by
    rw [← h12]; linear_combination q₁ * h23 - q₁ * h12 + q₂ * h₁
  have hT4 : T * q₄ = T := by
    rw [← h12]; linear_combination q₁ * h24 - q₁ * h12 + q₂ * h₁
  have hr : ∀ q : A, q * q = q → T * q = T → (q + T) * (q + T) = q + T := by
    intro q hq hTq
    linear_combination hq + 2 * hTq + hTT + T * h2
  have hrT : ∀ q : A, T * q = T → (q + T) * T = 0 := by
    intro q hTq
    linear_combination hTq + hTT + T * h2
  have hTr : ∀ q : A, T * q = T → T * (q + T) = 0 := by
    intro q hTq
    linear_combination hTq + hTT + T * h2
  have hrr : ∀ q q' : A, q * q' = T → T * q = T → T * q' = T → (q + T) * (q' + T) = 0 := by
    intro q q' hqq' hTq hTq'
    linear_combination hqq' + hTq + hTq' + hTT + 2 * T * h2
  have hsplit : ∀ q : A, q * q = q → T * q = T → rk (φ q) = rk (φ (q + T)) + rk (φ T) := by
    intro q hq hTq
    have e : q = (q + T) + T := by linear_combination -T * h2
    conv_lhs => rw [e]
    rw [map_add φ (q + T) T]
    refine rk_add_of_orth ?_ ?_ ?_ ?_
    · rw [← map_mul, hr q hq hTq]
    · rw [← map_mul, hrT q hTq, map_zero]
    · rw [← map_mul, hTr q hTq, map_zero]
    · rw [← map_mul, hTT]
  set e : Fin 5 → A := ![T, q₁ + T, q₂ + T, q₃ + T, q₄ + T] with he
  have eP : φ P = ∑ i, φ (e i) := by
    rw [Fin.sum_univ_five, ← map_add, ← map_add, ← map_add, ← map_add]
    congr 1
    simp only [he, Matrix.cons_val]
    linear_combination -hsum - 3 * T * h2
  have hidem : ∀ i ∈ (Finset.univ : Finset (Fin 5)), φ (e i) * φ (e i) = φ (e i) := by
    intro i _
    rw [← map_mul]
    congr 1
    fin_cases i
    · exact hTT
    · exact hr q₁ h₁ hT1
    · exact hr q₂ h₂ hT2
    · exact hr q₃ h₃ hT3
    · exact hr q₄ h₄ hT4
  have horth : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)),
      i ≠ j → φ (e i) * φ (e j) = 0 := by
    have hs : ∀ x y : A, x * y = 0 → y * x = 0 := fun x y h => by rw [mul_comm, h]
    have o12 := hrr q₁ q₂ h12 hT1 hT2
    have o13 := hrr q₁ q₃ h13 hT1 hT3
    have o14 := hrr q₁ q₄ h14 hT1 hT4
    have o23 := hrr q₂ q₃ h23 hT2 hT3
    have o24 := hrr q₂ q₄ h24 hT2 hT4
    have o34 := hrr q₃ q₄ h34 hT3 hT4
    have t1 := hTr q₁ hT1
    have t2 := hTr q₂ hT2
    have t3 := hTr q₃ hT3
    have t4 := hTr q₄ hT4
    intro i _ j _ hij
    rw [← map_mul, ← map_zero φ]
    congr 1
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | simp only [he]
        first
          | assumption
          | exact hs _ _ (by assumption)
  have hP := rk_sum_of_orth Finset.univ (fun i => φ (e i)) hidem horth
  rw [← eP, Fin.sum_univ_five] at hP
  simp only [he, Matrix.cons_val] at hP
  rw [hsplit q₁ h₁ hT1, hsplit q₂ h₂ hT2, hsplit q₃ h₃ hT3, hsplit q₄ h₄ hT4, hP]
  ring

omit [FiniteDimensional K V] in
theorem two_eq_zero_end (h2 : (2 : K) = 0) : (2 : Module.End K V) = 0 := by
  ext v
  have h : (2 : Module.End K V) v = (2 : K) • v := by
    rw [show (2 : Module.End K V) = 1 + 1 from one_add_one_eq_two.symm, LinearMap.add_apply,
      Module.End.one_apply, ← one_add_one_eq_two, add_smul, one_smul]
  rw [h, h2, zero_smul, LinearMap.zero_apply]

omit [FiniteDimensional K V] in
theorem range_fixProj (h2 : (2 : K) = 0) {g : Module.End K V} (hg : g ^ 3 = 1) :
    LinearMap.range (fp g) = LinearMap.ker (g - 1) := by
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨w, rfl⟩
    have e : (g - 1) * fp g = g ^ 3 - 1 := by noncomm_ring
    rw [← Module.End.mul_apply, e, hg, sub_self, LinearMap.zero_apply]
  · intro hv
    have hgv : g v = v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
    refine ⟨v, ?_⟩
    have hg2 : (g ^ 2) v = v := by rw [pow_two, Module.End.mul_apply, hgv, hgv]
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, hgv, hg2]
    have : v + v = (2 : K) • v := by rw [two_smul]
    rw [this, h2, zero_smul, zero_add]

end Rank

section Abelian

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {E : Type*} [Group E] [IsMulCommutative E]

theorem pairwise_commute_range (ρ : E →* Module.End K V) :
    (Set.range ρ).Pairwise Commute := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
  change ρ x * ρ y = ρ y * ρ x
  rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := E)).comm x y]

@[reducible] noncomputable def adjCommRing (ρ : E →* Module.End K V) :
    CommRing (Algebra.adjoin K (Set.range ρ)) :=
  { (inferInstance : Ring (Algebra.adjoin K (Set.range ρ))) with
    mul_comm := fun a b =>
      (Algebra.isMulCommutative_adjoin K (pairwise_commute_range ρ)).is_comm.comm a b }

theorem exists_commRing_model (ρ : E →* Module.End K V) :
    ∃ (A : Type v) (_ : CommRing A) (φ : A →+* Module.End K V) (ι : E →* A),
      Function.Injective φ ∧ ∀ x, φ (ι x) = ρ x := by
  let _ : CommRing (Algebra.adjoin K (Set.range ρ)) := adjCommRing ρ
  refine ⟨↥(Algebra.adjoin K (Set.range ρ)), adjCommRing ρ,
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl },
    { toFun := fun x => ⟨ρ x, Algebra.subset_adjoin ⟨x, rfl⟩⟩,
      map_one' := Subtype.ext (map_one ρ), map_mul' := fun x y => Subtype.ext (map_mul ρ x y) },
    Subtype.val_injective, fun _ => rfl⟩

end Abelian

section Main

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {E : Type*} [Group E] [IsMulCommutative E]

omit [IsMulCommutative E] in
theorem not_mem_zpowers_facts {m y : E} (hy3 : y ^ 3 = 1) (hy : y ∉ Subgroup.zpowers m) :
    y ≠ 1 ∧ m * y ≠ 1 ∧ m * y ^ 2 ≠ 1 := by
  have hm : m ∈ Subgroup.zpowers m := Subgroup.mem_zpowers m
  refine ⟨fun h => hy (h ▸ one_mem _), fun h => hy ?_, fun h => hy ?_⟩
  · have : y = m⁻¹ * (m * y) := by group
    rw [this, h, mul_one]
    exact inv_mem hm
  · have hy2 : y ^ 2 ∈ Subgroup.zpowers m := by
      have : y ^ 2 = m⁻¹ * (m * y ^ 2) := by group
      rw [this, h, mul_one]
      exact inv_mem hm
    have : y = (y ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hy3, one_mul]
    rw [this]
    exact pow_mem hy2 2

theorem false_of_core (h2K : (2 : K) = 0) (hV : finrank K V = 8) (ρ : E →* Module.End K V)
    (hexp : ∀ x : E, x ^ 3 = 1) {m a b : E} (hm : m ≠ 1) (ha : a ∉ Subgroup.zpowers m)
    (hb : b ∉ Subgroup.zpowers m ⊔ Subgroup.zpowers a)
    (hd : ∀ x : E, x ≠ 1 → fixDim (ρ x) = 2 ∨ fixDim (ρ x) = 4)
    (hm4 : fixDim (ρ m) = 4 ∨ ∀ x : E, x ≠ 1 → fixDim (ρ x) = 2) : False := by
  obtain ⟨A, _, φ, ι, hφinj, hφι⟩ := exists_commRing_model ρ
  have h2 : (2 : A) = 0 := hφinj (by rw [map_ofNat, map_zero, two_eq_zero_end h2K])
  have hι3 : ∀ x : E, ι x ^ 3 = 1 := fun x => by rw [← map_pow, hexp x, map_one]
  have hrk : ∀ x : E, rk (φ (fp (ι x))) = fixDim (ρ x) := by
    intro x
    have e : φ (fp (ι x)) = fp (ρ x) := by simp only [fp, map_add, map_one, map_pow, hφι]
    rw [e, rk, range_fixProj h2K (by rw [← map_pow, hexp x, map_one])]
  have hidem : ∀ x : E, fp (ι x) * fp (ι x) = fp (ι x) := fun x => ring_fixProj_sq h2 (hι3 x)
  set c : E → ℕ := fun y => rk (φ (fp (ι m) * fp (ι y))) with hc
  have R1 : ∀ y : E, fixDim (ρ m) + fixDim (ρ y) + fixDim (ρ (m * y)) +
      fixDim (ρ (m * y ^ 2)) = 8 + 3 * c y := by
    intro y
    have hf := rank_formula φ h2 (hidem m) (hidem y) (hidem (m * y)) (hidem (m * y ^ 2)) rfl
      (by rw [map_mul]; exact ring_fixProj_mul_g_gh (hι3 m))
      (by rw [map_mul, map_pow]; exact ring_fixProj_mul_g_gh2 (hι3 m) (hι3 y))
      (by rw [map_mul]; exact ring_fixProj_mul_h_gh (hι3 y))
      (by rw [map_mul, map_pow]; exact ring_fixProj_mul_h_gh2 (hι3 y))
      (by rw [map_mul, map_mul, map_pow]; exact ring_fixProj_mul_gh_gh2 (hι3 m) (hι3 y))
      (P := 1) (by rw [map_mul, map_mul, map_pow]; exact ring_fixProj_sum h2 (hι3 y))
    rw [hrk, hrk, hrk, hrk, map_one] at hf
    rw [hf, hc]
    congr 1
    rw [rk, LinearMap.range_eq_top.mpr fun v => ⟨v, rfl⟩, finrank_top, hV]
  have hPP : ∀ x y : E, fp (ι x) * fp (ι y) = fp (ι a) * fp (ι b) →
      fp (ι m) * fp (ι x) * (fp (ι m) * fp (ι y)) = fp (ι m) * (fp (ι a) * fp (ι b)) := by
    intro x y hxy
    rw [mul_mul_mul_comm, hidem, hxy]
  have hI : ∀ x : E, fp (ι m) * fp (ι x) * (fp (ι m) * fp (ι x)) = fp (ι m) * fp (ι x) := by
    intro x
    rw [mul_mul_mul_comm, hidem, hidem]
  set t := rk (φ (fp (ι m) * (fp (ι a) * fp (ι b))))
  have R2 : c a + c b + c (a * b) + c (a * b ^ 2) = fixDim (ρ m) + 3 * t := by
    have hf := rank_formula φ h2 (hI a) (hI b) (hI (a * b)) (hI (a * b ^ 2))
      (hPP a b rfl)
      (hPP a (a * b) (by rw [map_mul]; exact ring_fixProj_mul_g_gh (hι3 a)))
      (hPP a (a * b ^ 2) (by rw [map_mul, map_pow]; exact ring_fixProj_mul_g_gh2 (hι3 a) (hι3 b)))
      (hPP b (a * b) (by rw [map_mul]; exact ring_fixProj_mul_h_gh (hι3 b)))
      (hPP b (a * b ^ 2) (by rw [map_mul, map_pow]; exact ring_fixProj_mul_h_gh2 (hι3 b)))
      (hPP (a * b) (a * b ^ 2)
        (by rw [map_mul, map_mul, map_pow]; exact ring_fixProj_mul_gh_gh2 (hι3 a) (hι3 b)))
      (P := fp (ι m)) (by
        rw [← mul_add, ← mul_add, ← mul_add, map_mul, map_mul, map_pow,
          ring_fixProj_sum h2 (hι3 b), mul_add, mul_one])
    rw [hrk] at hf
    exact hf
  have hmS : ∀ {z : E}, z ∈ Subgroup.zpowers m → z ∈ Subgroup.zpowers m ⊔ Subgroup.zpowers a :=
    fun h => Subgroup.mem_sup_left h
  have haS : a ∈ Subgroup.zpowers m ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hyb : b ∉ Subgroup.zpowers m := fun h => hb (hmS h)
  have hyab : a * b ∉ Subgroup.zpowers m := by
    intro h
    apply hb
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact mul_mem (inv_mem haS) (hmS h)
  have hyab2 : a * b ^ 2 ∉ Subgroup.zpowers m := by
    intro h
    apply hb
    have hb2 : b ^ 2 ∈ Subgroup.zpowers m ⊔ Subgroup.zpowers a := by
      have e : b ^ 2 = a⁻¹ * (a * b ^ 2) := by group
      rw [e]
      exact mul_mem (inv_mem haS) (hmS h)
    have e : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hexp b, one_mul]
    rw [e]
    exact pow_mem hb2 2
  rcases hm4 with h4 | hall
  · have key : ∀ y : E, y ∉ Subgroup.zpowers m → c y = 2 := by
      intro y hy
      obtain ⟨h1, h2', h3⟩ := not_mem_zpowers_facts (hexp y) hy
      have r := R1 y
      rcases hd y h1 with e1 | e1 <;> rcases hd _ h2' with e2 | e2 <;>
        rcases hd _ h3 with e3 | e3 <;> omega
    have := key a ha
    have := key b hyb
    have := key (a * b) hyab
    have := key (a * b ^ 2) hyab2
    omega
  · have key : ∀ y : E, y ∉ Subgroup.zpowers m → c y = 0 := by
      intro y hy
      obtain ⟨h1, h2', h3⟩ := not_mem_zpowers_facts (hexp y) hy
      have r := R1 y
      have := hall m hm
      have := hall y h1
      have := hall _ h2'
      have := hall _ h3
      omega
    have := key a ha
    have := key b hyb
    have := key (a * b) hyab
    have := key (a * b ^ 2) hyab2
    have := hall m hm
    omega

theorem false_of_fixDim_two_four [Finite E] (h2K : (2 : K) = 0) (hV : finrank K V = 8)
    (ρ : E →* Module.End K V) (hexp : ∀ x : E, x ^ 3 = 1) (hcard : 27 ≤ Nat.card E)
    (hd : ∀ x : E, x ≠ 1 → fixDim (ρ x) = 2 ∨ fixDim (ρ x) = 4) : False := by
  have hord : ∀ x : E, orderOf x ≤ 3 := fun x => orderOf_le_of_pow_eq_one (by norm_num) (hexp x)
  obtain ⟨m, hm, hm4⟩ : ∃ m : E, m ≠ 1 ∧
      (fixDim (ρ m) = 4 ∨ ∀ x : E, x ≠ 1 → fixDim (ρ x) = 2) := by
    by_cases hex : ∃ z : E, z ≠ 1 ∧ fixDim (ρ z) = 4
    · obtain ⟨z, hz, hz4⟩ := hex
      exact ⟨z, hz, Or.inl hz4⟩
    · have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨m, hm⟩ := exists_ne (1 : E)
      refine ⟨m, hm, Or.inr fun x hx => ?_⟩
      rcases hd x hx with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ hex
  obtain ⟨a, ha⟩ : ∃ a : E, a ∉ Subgroup.zpowers m := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show (⊤ : Subgroup E) ≤ Subgroup.zpowers m from
      fun x _ => h x)
    rw [Subgroup.card_top, Nat.card_zpowers] at hle
    have := hord m
    omega
  obtain ⟨b, hb⟩ : ∃ b : E, b ∉ Subgroup.zpowers m ⊔ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le
      (show (⊤ : Subgroup E) ≤ Subgroup.zpowers m ⊔ Subgroup.zpowers a from fun x _ => h x)
    rw [Subgroup.card_top] at hle
    have hS : Nat.card ↥(Subgroup.zpowers m ⊔ Subgroup.zpowers a) ≤ 9 := by
      have e : Nat.card ↥(Subgroup.zpowers m ⊔ Subgroup.zpowers a) =
          Nat.card ((Subgroup.zpowers m : Set E) * (Subgroup.zpowers a : Set E)) := by
        rw [← Subgroup.mul_normal]
        rfl
      rw [e]
      refine (Set.natCard_mul_le).trans ?_
      have h1 : Nat.card (Subgroup.zpowers m : Set E) = orderOf m := Nat.card_zpowers m
      have h2 : Nat.card (Subgroup.zpowers a : Set E) = orderOf a := Nat.card_zpowers a
      rw [h1, h2]
      have := hord m
      have := hord a
      calc orderOf m * orderOf a ≤ 3 * 3 := Nat.mul_le_mul (hord m) (hord a)
        _ = 9 := rfl
    omega
  exact false_of_core h2K hV ρ hexp hm ha hb hd hm4

end Main

end D4Rank

end CFSG.StandardType
