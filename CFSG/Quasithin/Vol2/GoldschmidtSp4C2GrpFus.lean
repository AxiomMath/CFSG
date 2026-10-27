module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpDih

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt minorAut)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

theorem exists_upper_conj {I : Subgroup (antiSp k)} (htr : ∀ x ∈ I, ¬ IsTransvection x)
    (htr' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {g : antiSp k} (hg : IsOppStd g)
    {b₀ c₀ : k} (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hz₀g : g * uElt 0 b₀ c₀ 0 * g⁻¹ ∈ I)
    {b c b' c' : k} (h : uElt 0 b c 0 ∈ I) (h' : uElt 0 b' c' 0 ∈ I) (hne : ¬ (b = 0 ∧ c = 0))
    (hne' : ¬ (b' = 0 ∧ c' = 0)) :
    ∃ y ∈ I, IsUpper y ∧ y * uElt 0 b c 0 * y⁻¹ = uElt 0 b' c' 0 := by
  obtain ⟨hb, hc⟩ := (c2_coords htr htr' h).resolve_left hne
  obtain ⟨hb', hc'⟩ := (c2_coords htr htr' h').resolve_left hne'
  obtain ⟨y₁, hy₁, e₁⟩ := exists_conj_ref hb hc hb₀ hc₀ hg
  obtain ⟨y₂, hy₂, e₂⟩ := exists_conj_ref hb' hc' hb₀ hc₀ hg
  have hcl : ∀ z : antiSp k, z ∈ I → ∀ y ∈ Subgroup.closure
      ({z, g * uElt 0 b₀ c₀ 0 * g⁻¹} : Set (antiSp k)), y ∈ I := fun z hz y hy =>
    (Subgroup.closure_le I).mpr (by
      rintro x (rfl | rfl)
      exacts [hz, hz₀g]) hy
  have e : y₂⁻¹ * y₁ * uElt 0 b c 0 * (y₂⁻¹ * y₁)⁻¹ = uElt 0 b' c' 0 := by
    calc y₂⁻¹ * y₁ * uElt 0 b c 0 * (y₂⁻¹ * y₁)⁻¹
        = y₂⁻¹ * (y₁ * uElt 0 b c 0 * y₁⁻¹) * y₂ := by group
      _ = y₂⁻¹ * (g * uElt 0 b₀ c₀ 0 * g⁻¹) * y₂ := by rw [e₁]
      _ = uElt 0 b' c' 0 := by
        rw [← e₂]
        group
  exact ⟨y₂⁻¹ * y₁, I.mul_mem (I.inv_mem (hcl _ h' _ hy₂)) (hcl _ h _ hy₁),
    P6B.isUpper_of_conj_center hb' hc' hb e, e⟩

end CFSG.Quasithin.Ch3E213M.Sp4C2
