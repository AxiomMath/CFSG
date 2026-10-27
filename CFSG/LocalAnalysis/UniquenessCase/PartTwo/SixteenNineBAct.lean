module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem s16n9b_card_le_mul_card_inf_centralizer {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    {U E : Subgroup Γ} (hEU : E ≤ Subgroup.normalizer (U : Set Γ)) (hE : IsElemAbelian p E)
    {b : ℕ} (hb : ∀ F : Subgroup (MulAut U), IsElemAbelian p F → Nat.card F ≤ b) :
    Nat.card E ≤ b * Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) := by
  set ρ : E →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hEU) with hρ
  have hcard : Nat.card E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have hEtop : IsElemAbelian p (⊤ : Subgroup E) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext (hE.2 a a.2)⟩
    exact congrArg Subtype.val (hE.1.is_comm.comm (a : E) (b : E))
  have hrange : Nat.card ρ.range ≤ b := by
    rw [MonoidHom.range_eq_map]
    exact hb _ (CFSG.Open.IsElemAbelian.map hEtop ρ)
  have hker : ρ.ker.map E.subtype = E ⊓ Subgroup.centralizer (U : Set Γ) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 := congrArg (fun σ : MulAut U => ((σ ⟨u, hu⟩ : U) : Γ)) (MonoidHom.mem_ker.mp hx)
      simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
      rw [U.normalizerMonoidHom_apply_apply_coe] at h1
      simp only [Subgroup.coe_inclusion] at h1
      calc u * (x : Γ) = (x : Γ) * u * (x : Γ)⁻¹ * (x : Γ) := by rw [h1]
        _ = (x : Γ) * u := by group
    · rintro ⟨hgE, hgC⟩
      refine ⟨⟨g, hgE⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply]
      rw [U.normalizerMonoidHom_apply_apply_coe]
      simp only [Subgroup.coe_inclusion]
      have h1 := Subgroup.mem_centralizer_iff.mp hgC u u.2
      calc g * (u : Γ) * g⁻¹ = (u : Γ) * g * g⁻¹ := by rw [h1]
        _ = u := by group
  have hker' : Nat.card ρ.ker = Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) := by
    rw [← hker, Subgroup.card_map_of_injective E.subtype_injective]
  rw [hcard, hker']
  exact Nat.mul_le_mul_right _ hrange

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
