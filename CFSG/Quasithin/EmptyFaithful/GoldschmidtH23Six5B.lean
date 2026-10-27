module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5BHelp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)

theorem m_cases {m : G} (hm : m ∈ M) :
    (m ∈ Subgroup.normalizer (d.V₁ : Set G) ∧ m ∈ Subgroup.normalizer (d.V₂ : Set G)) ∨
      ((∀ v ∈ d.V₁, m * v * m⁻¹ ∈ d.V₂) ∧ ∀ v ∈ d.V₂, m * v * m⁻¹ ∈ d.V₁) := by
  have hmN := d.hMN hm
  have hρ : convI hV ⟨m, hmN⟩ ∈ autI hV M := convI_mem_autI hV hm hmN
  rcases d.S.stab_or_swap (fun w => IntMod.sq_eq_one w) (d.hnorm _ hρ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨mem_normalizer_map hmN h1, mem_normalizer_map hmN h2⟩
  · refine Or.inr ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨w, hw, rfl⟩ := (d.mem_V₁_iff).1 hv
      rw [conj_val hmN w]
      exact d.val_mem_V₂ (h1 w hw)
    · obtain ⟨w, hw, rfl⟩ := (d.mem_V₂_iff).1 hv
      rw [conj_val hmN w]
      exact d.val_mem_V₁ (h2 w hw)

theorem exists_swap :
    ∃ t ∈ T, (∀ v ∈ d.V₁, t * v * t⁻¹ ∈ d.V₂) ∧ ∀ v ∈ d.V₂, t * v * t⁻¹ ∈ d.V₁ := by
  obtain ⟨g, hgT, hgτ⟩ := (mem_autI hV).1 d.hτ
  have hτM : d.S.τ ∈ autI hV M := autI_mono hV d.hTM d.hτ
  have hsw := d.S.swap_of_conj (fun w => IntMod.sq_eq_one w) (d.hnorm _ hτM)
    (fun a ha => d.S.τ₁₂ a ha)
  have hg : convI hV ⟨(g : G), g.2⟩ = d.S.τ := hgτ
  refine ⟨(g : G), hgT, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := (d.mem_V₁_iff).1 hv
    rw [conj_val g.2 w, hg]
    exact d.val_mem_V₂ (hsw.1 w hw)
  · obtain ⟨w, hw, rfl⟩ := (d.mem_V₂_iff).1 hv
    rw [conj_val g.2 w, hg]
    exact d.val_mem_V₁ (hsw.2 w hw)

end Six5Data

end CFSG.Quasithin
