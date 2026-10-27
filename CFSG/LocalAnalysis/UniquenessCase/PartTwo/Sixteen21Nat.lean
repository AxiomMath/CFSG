module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

namespace Sixteen21

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {W : Type} [CommGroup W]

theorem card_eq_of_realizes_nat [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut W)} (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    Nat.card W = Nat.card K ^ Fintype.card ι := by
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥Γ →* ↥H := π₀
  have hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π := hπ₀
  obtain ⟨e, -⟩ := CFSG.Quasithin.H.exists_mulEquiv_of_realizesVia Γ hπ
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Quasithin.H.card_stdMod

theorem exists_fix_of_realizes_nat {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut W)} (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥) {p : ℕ}
    (hfix : ∀ x : ι → K, ∃ g ∈ Γ, orderOf g = p ∧ Matrix.mulVec (g : Matrix ι ι K) x = x)
    (w : W) : ∃ φ ∈ H, orderOf φ = p ∧ φ w = w := by
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥Γ →* ↥H := π₀
  have hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π := hπ₀
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.exists_mulEquiv_of_realizesVia Γ hπ
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hnat : CFSG.Quasithin.H.natAut Γ γ = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [CFSG.Quasithin.H.natAut_apply]
      have h2 := he γ v
      rw [hγ] at h2
      simpa using h2.symm
    apply Subtype.ext
    show (γ : Matrix.GeneralLinearGroup ι K) = 1
    exact CFSG.Quasithin.H.matHom_injective (by
      rw [map_one]
      exact hnat)
  obtain ⟨g, hgΓ, hgord, hgfix⟩ := hfix (Multiplicative.toAdd (e w))
  refine ⟨((π ⟨g, hgΓ⟩ : ↥H) : MulAut W), (π ⟨g, hgΓ⟩).2, ?_, ?_⟩
  · calc orderOf (((π ⟨g, hgΓ⟩ : ↥H) : MulAut W))
        = orderOf (π ⟨g, hgΓ⟩) := Subgroup.orderOf_coe _
      _ = orderOf (⟨g, hgΓ⟩ : ↥Γ) := orderOf_injective π hinj _
      _ = orderOf g := Subgroup.orderOf_mk g hgΓ
      _ = p := hgord
  · apply e.injective
    have hnet : natAct Γ ⟨g, hgΓ⟩ (e w) = e w := by
      have h1 : natAct Γ ⟨g, hgΓ⟩ (e w)
          = Multiplicative.ofAdd (Multiplicative.toAdd (e w)) := by
        simp only [natAct]
        exact congrArg Multiplicative.ofAdd hgfix
      rwa [ofAdd_toAdd] at h1
    rw [he ⟨g, hgΓ⟩ w, hnet]

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
