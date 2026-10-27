module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultDimFiveSpin
public import CFSG.ClassicalInvolution.Asc77.AscSPN11
import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open
open scoped Classical
open CFSG.LieType.Universal.Spin

abbrev V5 : Type := Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5

noncomputable abbrev Q5 : QuadraticForm (ZMod 5) V5 := quadOdd 2 (ZMod 5)

theorem exists_mem_polar_orthogonal_two {a b : V5} (ha : Q5 a ≠ 0) (hb : Q5 b ≠ 0)
    (hab : QuadraticMap.polar Q5 a b = 0) {d : ZMod 5} (hd : d ≠ 0) :
    ∃ c : V5, QuadraticMap.polar Q5 a c = 0 ∧ QuadraticMap.polar Q5 b c = 0 ∧ Q5 c = d := by
  letI : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)
  let U : Submodule (ZMod 5) V5 := Submodule.span (ZMod 5) ({a, b} : Set V5)
  let W : Submodule (ZMod 5) V5 := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q5) U
  have hB : (QuadraticMap.polarBilin Q5).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff (Q := Q5)).mpr
      (CFSG.LieType.Universal.Spin.nondegenerate_quadOdd (n := 2) (K := ZMod 5))
  have hBa : QuadraticMap.polarBilin Q5 a a = 2 * Q5 a := by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  have hBb : QuadraticMap.polarBilin Q5 b b = 2 * Q5 b := by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  have hBab : QuadraticMap.polarBilin Q5 a b = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, hab]
  have hBba : QuadraticMap.polarBilin Q5 b a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, hab]
  have hUne : (Q5.restrict U).Nondegenerate := by
    rw [← QuadraticMap.nondegenerate_polar_iff, QuadraticMap.polarBilin_restrict]
    constructor
    · intro x hx
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp x.2
      have hxa : QuadraticMap.polarBilin Q5 (x : V5) a = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨a, Submodule.subset_span (by simp)⟩
      have hxb : QuadraticMap.polarBilin Q5 (x : V5) b = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨b, Submodule.subset_span (by simp)⟩
      have hα : α = 0 := by
        rw [← hαβ] at hxa
        have h1 : α * (2 * Q5 a) = 0 := by
          simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul, hBa, hBba, mul_zero, add_zero] using hxa
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) ha)
      have hβ : β = 0 := by
        rw [← hαβ] at hxb
        have h1 : β * (2 * Q5 b) = 0 := by
          simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul, hBb, hBab, mul_zero, zero_add] using hxb
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hb)
      apply Subtype.ext
      rw [← hαβ, hα, hβ, zero_smul, zero_smul, add_zero]
      rfl
    · intro x hx
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp x.2
      have hax : QuadraticMap.polarBilin Q5 a (x : V5) = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨a, Submodule.subset_span (by simp)⟩
      have hbx : QuadraticMap.polarBilin Q5 b (x : V5) = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨b, Submodule.subset_span (by simp)⟩
      have hα : α = 0 := by
        rw [← hαβ] at hax
        have h1 : α * (2 * Q5 a) = 0 := by
          simpa only [map_add, map_smul, smul_eq_mul, hBa, hBab, mul_zero, add_zero] using hax
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) ha)
      have hβ : β = 0 := by
        rw [← hαβ] at hbx
        have h1 : β * (2 * Q5 b) = 0 := by
          simpa only [map_add, map_smul, smul_eq_mul, hBb, hBba, mul_zero, zero_add] using hbx
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hb)
      apply Subtype.ext
      rw [← hαβ, hα, hβ, zero_smul, zero_smul, add_zero]
      rfl
  have hWnd := QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal
    (Q := Q5) (CFSG.LieType.Universal.Spin.nondegenerate_quadOdd (n := 2) (K := ZMod 5)) hUne
  have hWpolar : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q5) W).Nondegenerate := by
    rw [show LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q5) W =
        (QuadraticMap.polarBilin Q5).domRestrict₁₂ W W from rfl,
      ← QuadraticMap.polarBilin_restrict]
    exact (QuadraticMap.nondegenerate_polar_iff (Q := Q5.restrict W)).mpr hWnd
  have hW : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q5 W := fun x hxW hxorth =>
    Subtype.ext_iff.mp (hWpolar.1 ⟨x, hxW⟩ (fun y => by
      have h := hxorth y.1 y.2
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        QuadraticMap.polarBilin_apply_apply] using h))
  have hVfin : Module.finrank (ZMod 5) V5 = 5 := by simp
  have hUle : Module.finrank (ZMod 5) U ≤ 2 := by
    have hrange : Set.range (fun i : Fin 2 => if i = 0 then a else b) = ({a, b} : Set V5) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    have h := finrank_range_le_card (R := ZMod 5) (M := V5)
      (fun i : Fin 2 => if i = 0 then a else b)
    rw [Fintype.card_fin] at h
    rw [show U = Submodule.span (ZMod 5)
      (Set.range (fun i : Fin 2 => if i = 0 then a else b)) from by rw [hrange]]
    simpa only [Set.finrank] using h
  have hdim : 2 ≤ Module.finrank (ZMod 5) W := by
    rw [show W = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q5) U from rfl,
      LinearMap.BilinForm.finrank_orthogonal hB U, hVfin]
    omega
  obtain ⟨c, hcW, hcQ⟩ := hW.exists_map_eq (Q := Q5) (by decide) hdim d
  refine ⟨c, ?_, ?_, hcQ⟩
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff (B := QuadraticMap.polarBilin Q5) (N := U)).mp hcW a
      (Submodule.subset_span (by simp))
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff (B := QuadraticMap.polarBilin Q5) (N := U)).mp hcW b
      (Submodule.subset_span (by simp))

theorem exists_mem_polar_orthogonal_three {a b c : V5} (ha : Q5 a ≠ 0) (hb : Q5 b ≠ 0)
    (hc : Q5 c ≠ 0) (hab : QuadraticMap.polar Q5 a b = 0)
    (hac : QuadraticMap.polar Q5 a c = 0) (hbc : QuadraticMap.polar Q5 b c = 0)
    {d : ZMod 5} (hd : d ≠ 0) :
    ∃ e : V5, QuadraticMap.polar Q5 a e = 0 ∧ QuadraticMap.polar Q5 b e = 0 ∧
      QuadraticMap.polar Q5 c e = 0 ∧ Q5 e = d := by
  letI : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)
  let U : Submodule (ZMod 5) V5 := Submodule.span (ZMod 5) ({a, b, c} : Set V5)
  let W : Submodule (ZMod 5) V5 := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q5) U
  have hB : (QuadraticMap.polarBilin Q5).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff (Q := Q5)).mpr
      (CFSG.LieType.Universal.Spin.nondegenerate_quadOdd (n := 2) (K := ZMod 5))
  have hBa : QuadraticMap.polarBilin Q5 a a = 2 * Q5 a := by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  have hBb : QuadraticMap.polarBilin Q5 b b = 2 * Q5 b := by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  have hBc : QuadraticMap.polarBilin Q5 c c = 2 * Q5 c := by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  have hBab : QuadraticMap.polarBilin Q5 a b = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, hab]
  have hBac : QuadraticMap.polarBilin Q5 a c = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, hac]
  have hBba : QuadraticMap.polarBilin Q5 b a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, hab]
  have hBbc : QuadraticMap.polarBilin Q5 b c = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, hbc]
  have hBca : QuadraticMap.polarBilin Q5 c a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, hac]
  have hBcb : QuadraticMap.polarBilin Q5 c b = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, hbc]
  have hUne : (Q5.restrict U).Nondegenerate := by
    rw [← QuadraticMap.nondegenerate_polar_iff, QuadraticMap.polarBilin_restrict]
    constructor
    · intro x hx
      obtain ⟨α, β, γ, hαβγ⟩ := Submodule.mem_span_triple.mp x.2
      have hxa : QuadraticMap.polarBilin Q5 (x : V5) a = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨a, Submodule.subset_span (by simp)⟩
      have hxb : QuadraticMap.polarBilin Q5 (x : V5) b = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨b, Submodule.subset_span (by simp)⟩
      have hxc : QuadraticMap.polarBilin Q5 (x : V5) c = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨c, Submodule.subset_span (by simp)⟩
      have hα : α = 0 := by
        rw [← hαβγ] at hxa
        have h1 : α * (2 * Q5 a) = 0 := by
          simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul, hBa, hBba, hBca, mul_zero, add_zero] using hxa
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) ha)
      have hβ : β = 0 := by
        rw [← hαβγ] at hxb
        have h1 : β * (2 * Q5 b) = 0 := by
          simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul, hBb, hBab, hBcb, mul_zero, zero_add, add_zero] using hxb
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hb)
      have hγ : γ = 0 := by
        rw [← hαβγ] at hxc
        have h1 : γ * (2 * Q5 c) = 0 := by
          simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul, hBc, hBac, hBbc, mul_zero, zero_add, add_zero] using hxc
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hc)
      apply Subtype.ext
      rw [← hαβγ, hα, hβ, hγ, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
      rfl
    · intro x hx
      obtain ⟨α, β, γ, hαβγ⟩ := Submodule.mem_span_triple.mp x.2
      have hax : QuadraticMap.polarBilin Q5 a (x : V5) = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨a, Submodule.subset_span (by simp)⟩
      have hbx : QuadraticMap.polarBilin Q5 b (x : V5) = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨b, Submodule.subset_span (by simp)⟩
      have hcx : QuadraticMap.polarBilin Q5 c (x : V5) = 0 := by
        simpa only [LinearMap.domRestrict₁₂_apply] using
          hx ⟨c, Submodule.subset_span (by simp)⟩
      have hα : α = 0 := by
        rw [← hαβγ] at hax
        have h1 : α * (2 * Q5 a) = 0 := by
          simpa only [map_add, map_smul, smul_eq_mul, hBa, hBab, hBac, mul_zero, add_zero] using hax
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) ha)
      have hβ : β = 0 := by
        rw [← hαβγ] at hbx
        have h1 : β * (2 * Q5 b) = 0 := by
          simpa only [map_add, map_smul, smul_eq_mul, hBb, hBba, hBbc, mul_zero, zero_add,
            add_zero] using hbx
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hb)
      have hγ : γ = 0 := by
        rw [← hαβγ] at hcx
        have h1 : γ * (2 * Q5 c) = 0 := by
          simpa only [map_add, map_smul, smul_eq_mul, hBc, hBca, hBcb, mul_zero, zero_add] using hcx
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero (by decide) hc)
      apply Subtype.ext
      rw [← hαβγ, hα, hβ, hγ, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
      rfl
  have hWnd := QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal
    (Q := Q5) (CFSG.LieType.Universal.Spin.nondegenerate_quadOdd (n := 2) (K := ZMod 5)) hUne
  have hWpolar : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q5) W).Nondegenerate := by
    rw [show LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q5) W =
        (QuadraticMap.polarBilin Q5).domRestrict₁₂ W W from rfl,
      ← QuadraticMap.polarBilin_restrict]
    exact (QuadraticMap.nondegenerate_polar_iff (Q := Q5.restrict W)).mpr hWnd
  have hW : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q5 W := fun x hxW hxorth =>
    Subtype.ext_iff.mp (hWpolar.1 ⟨x, hxW⟩ (fun y => by
      have h := hxorth y.1 y.2
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        QuadraticMap.polarBilin_apply_apply] using h))
  have hVfin : Module.finrank (ZMod 5) V5 = 5 := by simp
  have hUle : Module.finrank (ZMod 5) U ≤ 3 := by
    have hrange : Set.range (fun i : Fin 3 => ![a, b, c] i) = ({a, b, c} : Set V5) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩
    have h := finrank_range_le_card (R := ZMod 5) (M := V5)
      (fun i : Fin 3 => ![a, b, c] i)
    rw [Fintype.card_fin] at h
    rw [show U = Submodule.span (ZMod 5)
      (Set.range (fun i : Fin 3 => ![a, b, c] i)) from by rw [hrange]]
    simpa only [Set.finrank] using h
  have hdim : 2 ≤ Module.finrank (ZMod 5) W := by
    rw [show W = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q5) U from rfl,
      LinearMap.BilinForm.finrank_orthogonal hB U, hVfin]
    omega
  obtain ⟨e, heW, heQ⟩ := hW.exists_map_eq (Q := Q5) (by decide) hdim d
  refine ⟨e, ?_, ?_, ?_, heQ⟩
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff (B := QuadraticMap.polarBilin Q5) (N := U)).mp heW a
      (Submodule.subset_span (by simp))
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff (B := QuadraticMap.polarBilin Q5) (N := U)).mp heW b
      (Submodule.subset_span (by simp))
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff (B := QuadraticMap.polarBilin Q5) (N := U)).mp heW c
      (Submodule.subset_span (by simp))

theorem reflect_smul_ne_zero {μ : ZMod 5} (hμ : μ ≠ 0) (v : V5) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q5 (μ • v) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 v := by
  by_cases hv : Q5 v = 0
  · have : Q5 (μ • v) = 0 := by rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hv, mul_zero]
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero this,
      CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hv]
  · have hμv : Q5 (μ • v) ≠ 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]
      exact mul_ne_zero (pow_ne_zero 2 hμ) hv
    refine LinearEquiv.ext fun x => ?_
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hμv,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply hv, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, smul_smul]
    have e : μ * QuadraticMap.polar Q5 v x / (μ ^ 2 * Q5 v) * μ =
        QuadraticMap.polar Q5 v x / Q5 v := by field_simp
    rw [e]

theorem reflect_sub_swap {x y : V5} (hxy : QuadraticMap.polar Q5 x y = 0)
    (hQ : Q5 x = Q5 y) (hy : Q5 y ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q5 (x - y) x = y ∧
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 (x - y) y = x := by
  have hx : Q5 x ≠ 0 := by rw [hQ]; exact hy
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  refine ⟨?_, ?_⟩
  · have h := CFSG.ComponentClassification.OddClassSelector.reflect_sub_apply
      (Q := Q5) h2 (u := y) (y := x) ((QuadraticMap.polar_comm Q5 y x).trans hxy) hQ.symm hx
    rwa [show y - x = (-1 : ZMod 5) • (x - y) from by module,
      reflect_smul_ne_zero (by decide : (-1 : ZMod 5) ≠ 0)] at h
  · exact CFSG.ComponentClassification.OddClassSelector.reflect_sub_apply
      (Q := Q5) h2 hxy hQ hy

theorem reflect_mul_reflect_mem_orthDerived {p q : V5}
    (hpq : QuadraticMap.polar Q5 p q = 0) (hQ : Q5 p = Q5 q) (hq : Q5 q ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q5 p * CFSG.ClassicalGroups.Orthogonal.reflect Q5 q ∈
      CFSG.RankThree.Classical2.orthDerived Q5 :=
  CFSG.GH74.Filter.reflect_mul_reflect_mem_commutator (Q := Q5)
    (by decide : (2 : ZMod 5) ≠ 0) hpq hQ hq

theorem reflect_mul_reflect_mem_orthDerived_of_isSquare {p q : V5}
    (hp : Q5 p ≠ 0) (hq : Q5 q ≠ 0) (hpq : QuadraticMap.polar Q5 p q = 0)
    (hsq : IsSquare (Q5 p * Q5 q)) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q5 p * CFSG.ClassicalGroups.Orthogonal.reflect Q5 q ∈
      CFSG.RankThree.Classical2.orthDerived Q5 := by
  obtain ⟨m, hm⟩ := hsq
  let μ : ZMod 5 := m / Q5 q
  have hμQ : μ ^ 2 * Q5 q = Q5 p := by
    rw [show μ = m / Q5 q from rfl]
    field_simp
    rw [sq, mul_comm (Q5 q) (Q5 p), ← hm]
  have hμ : μ ≠ 0 := by
    intro h0
    have h := hμQ
    rw [h0] at h
    simp at h
    exact hp h.symm
  have hpol : QuadraticMap.polar Q5 p (μ • q) = 0 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hpq, mul_zero]
  have hmem := reflect_mul_reflect_mem_orthDerived (p := p) (q := μ • q) hpol
    (by rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]; exact hμQ.symm)
    (by rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hμQ]; exact hp)
  simpa only [reflect_smul_ne_zero hμ q] using hmem

theorem reflect_mul_reflect_conj {g : V5 ≃ₗ[ZMod 5] V5}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q5) (p q : V5) :
    g * (CFSG.ClassicalGroups.Orthogonal.reflect Q5 p *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 q) * g⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 (g p) *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 (g q) := by
  calc g * (CFSG.ClassicalGroups.Orthogonal.reflect Q5 p *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 q) * g⁻¹
      = (g * CFSG.ClassicalGroups.Orthogonal.reflect Q5 p * g⁻¹) *
        (g * CFSG.ClassicalGroups.Orthogonal.reflect Q5 q * g⁻¹) := by group
    _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 (g p) *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 (g q) := by
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_conj hg p,
        CFSG.ClassicalGroups.Orthogonal.reflect_conj hg q]

@[expose] noncomputable def statedOmegaEquivOrthDerived :
    ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5))) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Q5) :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).subgroupMap
      (StatedOmega (StatedQuadOdd 2 (ZMod 5)))).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
        (Q := Q5) (Q₀ := StatedQuadOdd 2 (ZMod 5))
        (CFSG.LieType.Universal.Spin.coe_quadOdd (n := 2) (K := ZMod 5))]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).surjective _))

theorem statedOmegaEquivOrthDerived_apply (g : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5)))) :
    (statedOmegaEquivOrthDerived g : V5 ≃ₗ[ZMod 5] V5) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5) g :=
  rfl

theorem reflPairInvariant_intrinsic {x : ↥(CFSG.RankThree.Classical2.orthDerived Q5)} {a b : V5}
    (ha : Q5 a ≠ 0) (hb : Q5 b ≠ 0) (hab : QuadraticMap.polar Q5 a b = 0)
    (hsq : IsSquare (Q5 a * Q5 b))
    (hx : (x : V5 ≃ₗ[ZMod 5] V5) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 b) :
    ReflPairInvariant x := by
  obtain ⟨c, hac, hbc, hcQ⟩ :=
    exists_mem_polar_orthogonal_two ha hb hab (d := Q5 b) hb
  have hc : Q5 c ≠ 0 := by rw [hcQ]; exact hb
  obtain ⟨m, hm⟩ := hsq
  let μ : ZMod 5 := m / Q5 b
  have hμQ : μ ^ 2 * Q5 b = Q5 a := by
    rw [show μ = m / Q5 b from rfl]
    field_simp
    rw [sq, mul_comm (Q5 b) (Q5 a), ← hm]
  have hμ : μ ≠ 0 := by
    intro h0
    have h := hμQ
    rw [h0] at h
    simp at h
    exact ha h.symm
  let c' : V5 := μ • c
  have hc'a : QuadraticMap.polar Q5 a c' = 0 := by
    rw [show c' = μ • c from rfl, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hac,
      mul_zero]
  have hc'b : QuadraticMap.polar Q5 b c' = 0 := by
    rw [show c' = μ • c from rfl, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hbc,
      mul_zero]
  have hc'Q : Q5 c' = Q5 a := by
    rw [show c' = μ • c from rfl, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hcQ, hμQ]
  have hc' : Q5 c' ≠ 0 := by rw [hc'Q]; exact ha
  obtain ⟨d₁, hd₁a, hd₁b, hd₁c, hd₁Q⟩ :=
    exists_mem_polar_orthogonal_three ha hb hc hab hac hbc (d := 2 * Q5 b)
      (hd := mul_ne_zero (by decide) hb)
  obtain ⟨d₂, hd₂a, hd₂b, hd₂c, hd₂Q⟩ :=
    exists_mem_polar_orthogonal_three ha hb hc hab hac hbc (d := 2 * Q5 a)
      (hd := mul_ne_zero (by decide) ha)
  have hQbc : Q5 (b - c) = Q5 d₁ := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q5, QuadraticMap.map_neg Q5,
      QuadraticMap.polar_neg_right, hbc, neg_zero, add_zero, hcQ, hd₁Q]
    ring
  have hQac' : Q5 (a - c') = Q5 d₂ := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q5, QuadraticMap.map_neg Q5,
      QuadraticMap.polar_neg_right, hc'a, neg_zero, add_zero, hc'Q, hd₂Q]
    ring
  have hQbc_ne : Q5 d₁ ≠ 0 := by rw [hd₁Q]; exact mul_ne_zero (by decide) hb
  have hQac'_ne : Q5 d₂ ≠ 0 := by rw [hd₂Q]; exact mul_ne_zero (by decide) ha
  have hc'd₂ : QuadraticMap.polar Q5 c' d₂ = 0 := by
    rw [show c' = μ • c from rfl, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hd₂c,
      mul_zero]
  have hp₁ : QuadraticMap.polar Q5 (b - c) d₁ = 0 := by
    rw [QuadraticMap.polar_sub_left, hd₁b, hd₁c, sub_zero]
  have hp₂ : QuadraticMap.polar Q5 (a - c') d₂ = 0 := by
    rw [QuadraticMap.polar_sub_left, hd₂a, hc'd₂, sub_zero]
  have hy_mem : CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 c ∈
      CFSG.RankThree.Classical2.orthDerived Q5 :=
    reflect_mul_reflect_mem_orthDerived_of_isSquare ha hc hac (by rw [hcQ]; exact ⟨m, hm⟩)
  have hg₁_mem : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁ ∈
      CFSG.RankThree.Classical2.orthDerived Q5 :=
    reflect_mul_reflect_mem_orthDerived hp₁ hQbc hQbc_ne
  have hg₂_mem : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂ ∈
      CFSG.RankThree.Classical2.orthDerived Q5 :=
    reflect_mul_reflect_mem_orthDerived hp₂ hQac' hQac'_ne
  have hd₁a' : CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁ a = a :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      ((QuadraticMap.polar_comm Q5 d₁ a).trans hd₁a)
  have hd₁b' : CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁ b = b :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      ((QuadraticMap.polar_comm Q5 d₁ b).trans hd₁b)
  have hd₂a' : CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂ a = a :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      ((QuadraticMap.polar_comm Q5 d₂ a).trans hd₂a)
  have hd₂b' : CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂ b = b :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      ((QuadraticMap.polar_comm Q5 d₂ b).trans hd₂b)
  have hbca : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) a = a := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    rw [QuadraticMap.polar_sub_left, (QuadraticMap.polar_comm Q5 b a).trans hab,
      (QuadraticMap.polar_comm Q5 c a).trans hac, sub_zero]
  have hbcb : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) b = c :=
    (reflect_sub_swap hbc hcQ.symm hc).1
  have hac'' : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') a = c' :=
    (reflect_sub_swap hc'a hc'Q.symm hc').1
  have hac'b : CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') b = b := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    rw [QuadraticMap.polar_sub_left, hab,
      (QuadraticMap.polar_comm Q5 c' b).trans hc'b, sub_zero]
  let y : ↥(CFSG.RankThree.Classical2.orthDerived Q5) :=
    ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 c, hy_mem⟩
  let g₁ : ↥(CFSG.RankThree.Classical2.orthDerived Q5) :=
    ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁, hg₁_mem⟩
  let g₂ : ↥(CFSG.RankThree.Classical2.orthDerived Q5) :=
    ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂, hg₂_mem⟩
  have hg₁O : (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q5 :=
    mul_mem (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q5 (b - c))
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q5 d₁)
  have hg₂O : (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q5 :=
    mul_mem (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q5 (a - c'))
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q5 d₂)
  have hxy_amb : (↑x : V5 ≃ₗ[ZMod 5] V5) * (↑y : V5 ≃ₗ[ZMod 5] V5) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c := by
    rw [hx]
    change (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 b) *
      (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c
    calc (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 b) *
        (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 c)
        = CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 a) *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 c := by group
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 b) *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 c := by
          rw [show CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
                CFSG.ClassicalGroups.Orthogonal.reflect Q5 a =
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
                CFSG.ClassicalGroups.Orthogonal.reflect Q5 b from
            (CFSG.GH74.Filter.reflect_comm hab).symm]
      _ = (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 a) *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 c) := by group
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 c := by
          rw [CFSG.ClassicalGroups.Orthogonal.reflect_mul_self, one_mul]
  have hy_amb : (↑y : V5 ≃ₗ[ZMod 5] V5) * (↑x : V5 ≃ₗ[ZMod 5] V5) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c := by
    change (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c) * (↑x) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c
    rw [hx]
    calc (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 c) *
        (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 b)
        = CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 c *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 a) *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 b := by group
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 c) *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 b := by
          rw [show CFSG.ClassicalGroups.Orthogonal.reflect Q5 c *
                CFSG.ClassicalGroups.Orthogonal.reflect Q5 a =
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
                CFSG.ClassicalGroups.Orthogonal.reflect Q5 c from
            (CFSG.GH74.Filter.reflect_comm hac).symm]
      _ = (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 a) *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q5 c *
              CFSG.ClassicalGroups.Orthogonal.reflect Q5 b) := by group
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 c *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 b := by
          rw [CFSG.ClassicalGroups.Orthogonal.reflect_mul_self, one_mul]
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q5 b *
            CFSG.ClassicalGroups.Orthogonal.reflect Q5 c :=
          (CFSG.GH74.Filter.reflect_comm hbc).symm
  have hconj₁ : (↑g₁ : V5 ≃ₗ[ZMod 5] V5) * (↑x) * (↑g₁)⁻¹ =
      (↑y : V5 ≃ₗ[ZMod 5] V5) := by
    change (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁) * (↑x) *
        (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁)⁻¹ =
      (CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 c)
    rw [hx, reflect_mul_reflect_conj hg₁O a b]
    rw [show (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁) a = a from by
        rw [LinearEquiv.mul_apply, hd₁a', hbca],
      show (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (b - c) *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₁) b = c from by
        rw [LinearEquiv.mul_apply, hd₁b', hbcb]]
  have hconj₂ : (↑g₂ : V5 ≃ₗ[ZMod 5] V5) * (↑x) * (↑g₂)⁻¹ =
      (↑x) * (↑y) := by
    change (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂) * (↑x) *
        (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂)⁻¹ =
      (↑x) * (↑y)
    rw [hxy_amb]
    rw [hx, reflect_mul_reflect_conj hg₂O a b]
    rw [show (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂) a = c' from by
        rw [LinearEquiv.mul_apply, hd₂a', hac''],
      show (CFSG.ClassicalGroups.Orthogonal.reflect Q5 (a - c') *
          CFSG.ClassicalGroups.Orthogonal.reflect Q5 d₂) b = b from by
        rw [LinearEquiv.mul_apply, hd₂b', hac'b]]
    rw [show c' = μ • c from rfl, reflect_smul_ne_zero hμ c]
    exact (CFSG.GH74.Filter.reflect_comm hbc).symm
  simp only [ReflPairInvariant]
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [isConj_iff]
    refine ⟨g₁⁻¹, ?_⟩
    apply Subtype.ext
    change (↑g₁ : V5 ≃ₗ[ZMod 5] V5)⁻¹ * (↑y) * (↑g₁) = (↑x)
    rw [← hconj₁]
    group
  · rw [commute_iff_eq]
    apply Subtype.ext
    change (↑y : V5 ≃ₗ[ZMod 5] V5) * (↑x) = (↑x) * (↑y)
    rw [hy_amb, hxy_amb]
  · rw [isConj_iff]
    refine ⟨g₂⁻¹, ?_⟩
    apply Subtype.ext
    change (↑g₂ : V5 ≃ₗ[ZMod 5] V5)⁻¹ * ((↑x) * (↑y)) * (↑g₂) = (↑x)
    rw [← hconj₂]
    group

end CFSG.OddTranspositions.PartThree
