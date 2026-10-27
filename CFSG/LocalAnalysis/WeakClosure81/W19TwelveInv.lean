module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_commutator_sup {H E₁ X O V₀ : Subgroup G} (hXH : X ≤ H) (hOH : O ≤ H)
    (hE₁ : H ≤ normalizer (E₁ : Set G)) (hVE : V₀ ≤ E₁)
    (hV₀ : ∀ h ∈ H, ∀ v ∈ V₀, h * v = v * h)
    (hK : H ≤ normalizer ((X ⊔ O : Subgroup G) : Set G))
    (hOE : ∀ o ∈ O, ∀ e ∈ E₁, ⁅e, o⁆ ∈ V₀) :
    H ≤ normalizer ((⁅E₁, X⁆ ⊔ V₀ : Subgroup G) : Set G) := by
  let R : Subgroup G := ⁅E₁, X⁆ ⊔ V₀
  change H ≤ normalizer (R : Set G)
  have hRle : R ≤ E₁ := by
    refine sup_le ?_ hVE
    rw [Subgroup.commutator_le]
    intro e he x hx
    have hxE : x ∈ normalizer (E₁ : Set G) := hE₁ (hXH hx)
    have hx' : x * e⁻¹ * x⁻¹ ∈ E₁ :=
      (Subgroup.mem_normalizer_iff.mp hxE e⁻¹).mp (E₁.inv_mem he)
    rw [commutatorElement_def]
    simpa [mul_assoc] using E₁.mul_mem he hx'
  have hOnorm : O ≤ normalizer (R : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_le]
    intro o ho r hr
    have hro : ⁅o, r⁆ ∈ R := Subgroup.mem_sup_right <| by
      simpa [commutatorElement_inv] using V₀.inv_mem (hOE o ho r (hRle hr))
    have hid : o * r * o⁻¹ = ⁅o, r⁆ * r := by
      rw [← MulAut.conj_apply]
      exact conj_eq_commutatorElement_mul
    have hforward : o * r * o⁻¹ ∈ R := by
      rw [hid]
      exact R.mul_mem hro hr
    rw [commutatorElement_def]
    exact R.mul_mem hforward (R.inv_mem hr)
  have hconjX : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    have hsub : R ≤ R.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro e he y hy
        rw [Subgroup.mem_comap]
        change x * ⁅e, y⁆ * x⁻¹ ∈ R
        rw [conjugate_commutatorElement]
        have hxe : x * e * x⁻¹ ∈ E₁ :=
          (Subgroup.mem_normalizer_iff.mp (hE₁ (hXH hx)) e).mp he
        have hxy : x * y * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
        exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hxe hxy)
      · intro v hv
        rw [Subgroup.mem_comap]
        change x * v * x⁻¹ ∈ R
        have hv' : x * v * x⁻¹ = v := by
          rw [hV₀ x (hXH hx) v hv, mul_assoc, mul_inv_cancel, mul_one]
        rw [hv']
        exact Subgroup.mem_sup_right hv
    exact hsub hr
  have hXnorm : X ≤ normalizer (R : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have hforward : x * r * x⁻¹ ∈ R := hconjX x hx r hr
    rw [commutatorElement_def]
    exact R.mul_mem hforward (R.inv_mem hr)
  have hsupnorm : X ⊔ O ≤ normalizer (R : Set G) := sup_le hXnorm hOnorm
  have hQ : ∀ k ∈ (X ⊔ O : Subgroup G), ∀ e ∈ E₁, ⁅e, k⁆ ∈ R := by
    have hclosure : (X ⊔ O : Subgroup G) = closure ((X : Set G) ∪ (O : Set G)) :=
      Subgroup.sup_eq_closure X O
    intro k hk e he
    rw [hclosure] at hk
    induction hk using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hyX | hyO
        · exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator he hyX)
        · exact Subgroup.mem_sup_right (hOE y hyO e he)
    | one =>
        rw [commutatorElement_one_right]
        exact R.one_mem
    | mul y z hy hz ihy ihz =>
        have hynorm : y ∈ normalizer (R : Set G) := hsupnorm (hclosure.symm ▸ hy)
        have hconj : y * ⁅e, z⁆ * y⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp hynorm (⁅e, z⁆)).mp ihz
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa [mul_assoc] using R.mul_mem ihy hconj
    | inv y hy ihy =>
        have hynorm : y⁻¹ ∈ normalizer (R : Set G) :=
          (normalizer (R : Set G)).inv_mem (hsupnorm (hclosure.symm ▸ hy))
        have hmem : ⁅y, e⁆ ∈ R := by simpa using R.inv_mem ihy
        rw [commutatorElement_inv_right]
        simpa using (Subgroup.mem_normalizer_iff.mp hynorm (⁅y, e⁆)).mp hmem
  have hconjH : ∀ t ∈ H, ∀ r ∈ R, t * r * t⁻¹ ∈ R := by
    intro t ht r hr
    have hsub : R ≤ R.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro e he x hx
        rw [Subgroup.mem_comap]
        change t * ⁅e, x⁆ * t⁻¹ ∈ R
        rw [conjugate_commutatorElement]
        have hte : t * e * t⁻¹ ∈ E₁ :=
          (Subgroup.mem_normalizer_iff.mp (hE₁ ht) e).mp he
        have htx : t * x * t⁻¹ ∈ X ⊔ O :=
          (Subgroup.mem_normalizer_iff.mp (hK ht) x).mp (Subgroup.mem_sup_left hx)
        exact hQ (t * x * t⁻¹) htx (t * e * t⁻¹) hte
      · intro v hv
        rw [Subgroup.mem_comap]
        change t * v * t⁻¹ ∈ R
        have hv' : t * v * t⁻¹ = v := by
          rw [hV₀ t ht v hv, mul_assoc, mul_inv_cancel, mul_one]
        rw [hv']
        exact Subgroup.mem_sup_right hv
    exact hsub hr
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  rw [Subgroup.commutator_le]
  intro t ht r hr
  have hforward : t * r * t⁻¹ ∈ R := hconjH t ht r hr
  rw [commutatorElement_def]
  exact R.mul_mem hforward (R.inv_mem hr)

end CFSG.LocalAnalysis.WeakClosure81

end
