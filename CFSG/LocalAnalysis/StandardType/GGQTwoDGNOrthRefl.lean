module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
public import CFSG.Quasithin.Recognition.CertDerived
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.QTwo

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orthDerived_le_of_reflect (hQ : (polarBilin Q).Nondegenerate) (h6 : 6 ≤ finrank K V)
    {H : Subgroup (V ≃ₗ[K] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {v₀ : V}
    (hv₀ : Q v₀ = 1) (hrH : ∀ h ∈ H, reflect Q v₀ * h * reflect Q v₀ ∈ H)
    (htr : ∀ w, Q w = 1 → ∃ h ∈ H, h v₀ = w) : orthDerived Q ≤ H := by
  classical
  set T : Set (V ≃ₗ[K] V) := {g | ∃ v, Q v = 1 ∧ g = reflect Q v * reflect Q v₀} with hT
  have hpair : ∀ {x y : V}, Q x = 1 → Q y = 1 →
      reflect Q x * reflect Q y ∈ Subgroup.closure T := by
    intro x y hx hy
    have hxT : reflect Q x * reflect Q v₀ ∈ Subgroup.closure T :=
      Subgroup.subset_closure ⟨x, hx, rfl⟩
    have hyT : reflect Q y * reflect Q v₀ ∈ Subgroup.closure T :=
      Subgroup.subset_closure ⟨y, hy, rfl⟩
    have e : reflect Q x * reflect Q y =
        (reflect Q x * reflect Q v₀) * (reflect Q y * reflect Q v₀)⁻¹ := by
      rw [mul_inv_rev, reflect_inv, reflect_inv]
      calc
        reflect Q x * reflect Q y
            = reflect Q x * (reflect Q v₀ * reflect Q v₀) * reflect Q y := by
              rw [reflect_mul_self, mul_one]
        _ = (reflect Q x * reflect Q v₀) * (reflect Q v₀ * reflect Q y) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxT (Subgroup.inv_mem _ hyT)
  have hO := orthogonalGroup_eq_closure_reflect_of_finite hQ h6
  have hcl : Subgroup.closure T ≤ H := by
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨h, hh, hhv⟩ := htr v hv
    have hc := reflect_conj (hHO hh) v₀
    rw [hhv] at hc
    rw [← hc]
    have : h * reflect Q v₀ * h⁻¹ * reflect Q v₀ = h * (reflect Q v₀ * h⁻¹ * reflect Q v₀) := by
      group
    rw [this]
    exact H.mul_mem hh (hrH _ (H.inv_mem hh))
  have hS : ∀ s ∈ reflect Q '' {v | Q v = 1}, s * s = 1 := by
    rintro _ ⟨v, -, rfl⟩
    exact reflect_mul_self Q v
  have hconj : ∀ s ∈ reflect Q '' {v | Q v = 1}, ∀ t ∈ T,
      s * t * s⁻¹ ∈ Subgroup.closure T := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
    have hsO := reflect_mem_orthogonalGroup Q a
    have hsv : Q (reflect Q a v) = 1 := by rw [map_of_mem hsO]; exact hv
    have hsv₀ : Q (reflect Q a v₀) = 1 := by rw [map_of_mem hsO]; exact hv₀
    have e : reflect Q a * (reflect Q v * reflect Q v₀) * (reflect Q a)⁻¹ =
        reflect Q (reflect Q a v) * reflect Q (reflect Q a v₀) := by
      rw [← reflect_conj hsO v, ← reflect_conj hsO v₀]
      group
    rw [e]
    exact hpair hsv hsv₀
  have hcomm : ∀ s ∈ reflect Q '' {v | Q v = 1}, ∀ s' ∈ reflect Q '' {v | Q v = 1},
      ⁅s, s'⁆ ∈ Subgroup.closure T := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hmem := hpair ha hb
    have e : ⁅reflect Q a, reflect Q b⁆ =
        (reflect Q a * reflect Q b) * (reflect Q a * reflect Q b) := by
      simp only [commutatorElement_def]
      rw [reflect_inv, reflect_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ hmem hmem
  have hmain := CFSG.Quasithin.commutator_closure_le_of_involutions hS hconj hcomm
  change ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ H
  rw [hO]
  exact hmain.trans hcl

end CFSG.StandardType.QTwo

end
