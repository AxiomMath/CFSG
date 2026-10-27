module

public import CFSG.LocalAnalysis.StandardType.GGWitSlpm
public import CFSG.LocalAnalysis.StandardType.GGWitSlpmConj
public import CFSG.LocalAnalysis.StandardType.GGWitSlpmOrder

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem wit_slpm_cr {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (hd : 3 ≤ Module.finrank (ZMod p) U)
    (A : Subgroup (U ≃ₗ[ZMod p] U))
    (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  intro r _ hr
  obtain ⟨a, α, hα, rfl⟩ := slpm_refl_form hp2 hr
  obtain ⟨b, β, hβ, hαb, hβa⟩ := slpm_exists_partner hp2 hd a α hα
  obtain ⟨g, hgdet, hgconj⟩ := slpm_conj hp2 hd a b α β hα hβ
  refine ⟨g, (hA g).mpr (Or.inl hgdet), ?_⟩
  rw [hgconj, slpm_order hp2 a b α β hα hβ hαb hβa]
  have hp3 : 3 ≤ p :=
    ((Fact.out : p.Prime).odd_iff).mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  omega

end CFSG.StandardType.ZS

end
