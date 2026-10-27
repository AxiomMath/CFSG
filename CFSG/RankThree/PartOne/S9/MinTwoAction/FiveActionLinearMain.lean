module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionLinearField

public section

namespace CFSG.RankThree.PartOne.FiveAction

open SemidirectProduct

theorem fixedVector : FixedVector := by
  intro q _ hq2 S A _ _ _ _ φ hφ hsh W _ _ _ ρ hρ hinj
  obtain ⟨s, hs, h2⟩ := Lin.exists_fixed_two hφ hsh (Lin.two_ne_zero_zmod Fact.out hq2) ρ hρ hinj
  exact ⟨s, hs, by omega⟩

theorem scalarBound : ScalarBound := by
  intro q _ hq2 hq5 S A _ _ _ _ φ hφ hsh b hbφ hbc hb5 W _ _ _ ρ hρ hinj hρb
  have : Finite (S ⋊[φ] A) := Finite.of_equiv (S × A) SemidirectProduct.equivProd.symm
  have hbcen : (inr b : S ⋊[φ] A) ∈ Subgroup.center (S ⋊[φ] A) :=
    Subgroup.mem_center_iff.mpr fun x => Lin.inr_central hbφ hbc x
  have hbord : orderOf (inr b : S ⋊[φ] A) = 5 := by
    rw [orderOf_injective (inr : A →* S ⋊[φ] A) inr_injective b, hb5]
  obtain ⟨E, _, _, ρE, hρE, hirrE, hE2, hdim⟩ :=
    Lin.exists_field_rep hq2 hq5 hbcen hbord ρ hρ hρb
  have : Finite W := Module.finite_of_finite (ZMod q)
  have : Module.Finite E W := Module.Finite.of_finite
  have hinjE : Function.Injective (ρE.comp (inl : S →* S ⋊[φ] A)) := by
    intro s t hst
    refine hinj (LinearMap.ext fun w => ?_)
    have h := congrArg (fun f : Module.End E W => f w) hst
    simpa [hρE] using h
  obtain ⟨s, hs, h2⟩ := Lin.exists_fixed_two hφ hsh hE2 ρE hirrE hinjE
  refine ⟨s, hs, ?_⟩
  rw [hdim]
  omega

end CFSG.RankThree.PartOne.FiveAction
