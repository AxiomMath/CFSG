module

public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c11_big_realizes_equiv {V : Type} [CommGroup V] {D : FFModel} (hA : D.IsActionModel)
    (hF : D.Faithful) {H : Subgroup (MulAut V)} {U : Subgroup V} (h : D.Realizes H U ⊥) :
    ∃ (ρ : D.Gam ≃* ↥H) (β : ↥U ≃* D.Mod), ∀ (γ : D.Gam) (u : ↥U),
      ((β.symm (hA.modAct γ (β u)) : ↥U) : V) = ((ρ γ : ↥H) : MulAut V) (u : V) := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π := FFModel.RealizesVia.injective_of_faithful_on hF hπ
  obtain ⟨hsurj, -, -, hinvU, -, hsec, -, β, hβsurj, hβker, hβeq⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβker u).mp hu))
  let β' : ↥U ≃* D.Mod := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  refine ⟨MulEquiv.ofBijective π ⟨hinj, hsurj⟩, β', fun γ u => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have h1 := hβeq γ u m (hinvU (π γ) u u.2) (hsec γ m m.2) hm.symm
  have h2 : β' ⟨((π γ : ↥H) : MulAut V) (u : V), hinvU (π γ) u u.2⟩ =
      hA.modAct γ (β' u) := by
    change β ⟨((π γ : ↥H) : MulAut V) (u : V), hinvU (π γ) u u.2⟩ = hA.modAct γ (β u)
    rw [← hm, hA.modAct_apply, hA.modEnd_mk, h1]
    congr 1
  have h3 : β'.symm (hA.modAct γ (β' u)) =
      ⟨((π γ : ↥H) : MulAut V) (u : V), hinvU (π γ) u u.2⟩ := by
    rw [← h2]
    exact MulEquiv.symm_apply_apply β' _
  rw [h3]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
