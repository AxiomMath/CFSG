module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

theorem exists_mem_normalizer_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R Z : Subgroup G} (hR : IsSylowOf p R ⊤) (hZ : ∀ z ∈ Z, ∀ x ∈ R, x * z = z * x) {g : G}
    (hZg : ∀ z ∈ Z, ∀ x ∈ R, x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x) :
    ∃ n ∈ normalizer (R : Set G), ∀ z ∈ Z, n⁻¹ * z * n = g⁻¹ * z * g := by
  classical
  set C : Subgroup G := centralizer (Z : Set G) with hC
  have hRC : R ≤ C := fun x hx => Subgroup.mem_centralizer_iff.2 fun z hz => (hZ z hz x hx).symm
  set R' : Subgroup G := R.map (MulAut.conj g).toMonoidHom with hR'
  have hR'C : R' ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have h1 := hZg z hz x hx
    have h2 : z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
    have h3 : g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
    show z * (g * x * g⁻¹) = g * x * g⁻¹ * z
    rw [h2, h3, h1]
  have hRsyl : IsSylowOf p R C := hR.of_le hRC le_top
  have hR'syl : IsSylowOf p R' C := by
    apply isSylowOf_of_card hR'C
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hRsyl.card_eq
  obtain ⟨k, hkC, hk⟩ := hRsyl.exists_mem_conj hR'syl
  have hkZ : ∀ z ∈ Z, k * z * k⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.1 hkC z hz
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  refine ⟨k⁻¹ * g, mem_normalizer_of_forward_uc6 fun r hr => ?_, fun z hz => ?_⟩
  · have hmem : g * r * g⁻¹ ∈ R' := ⟨r, hr, by simp [MulAut.conj_apply]⟩
    have := (hk _).1 hmem
    have e : k⁻¹ * g * r * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * r * g⁻¹) * k := by group
    rw [e]
    exact this
  · have e : (k⁻¹ * g)⁻¹ * z * (k⁻¹ * g) = g⁻¹ * (k * z * k⁻¹) * g := by group
    rw [e, hkZ z hz]

end CFSG.LocalAnalysis.UniquenessCase.UC6
