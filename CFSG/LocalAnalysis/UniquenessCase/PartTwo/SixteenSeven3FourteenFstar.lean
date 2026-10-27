module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1614_card_dvd_fstar_mul_aut (H : Type) [Group H] [Finite H] :
    Nat.card H ∣ Nat.card (genFittingFStar H) * Nat.card (MulAut ↥(genFittingFStar H)) := by
  classical
  haveI : (genFittingFStar H).Normal := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal
  have hker : (MulAut.conjNormal : H →* MulAut ↥(genFittingFStar H)).ker ≤ genFittingFStar H := by
    intro x hx
    apply CFSG.Open.Open.generalized_fitting_self_centralizing H
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h2 : x * f * x⁻¹ = f := by
      have h := congrArg (fun e : MulAut ↥(genFittingFStar H) =>
        ((e ⟨f, hf⟩ : ↥(genFittingFStar H)) : H)) (MonoidHom.mem_ker.mp hx)
      simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using h
    calc f * x = x * f * x⁻¹ * x := by rw [h2]
      _ = x * f := by group
  have h1 := Subgroup.card_dvd_of_le hker
  have h2 := Subgroup.card_subgroup_dvd_card
    (MulAut.conjNormal : H →* MulAut ↥(genFittingFStar H)).range
  rw [← Subgroup.card_ker_mul_card_range (MulAut.conjNormal : H →* MulAut ↥(genFittingFStar H))]
  exact Nat.mul_dvd_mul h1 h2

theorem s16c1614_card_dvd_fstar_subgroup {Ω : Type} [Group Ω] [Finite Ω] (H : Subgroup Ω) :
    Nat.card H ∣ Nat.card (Fstar H) * Nat.card (MulAut ↥(Fstar H)) := by
  have hF : ↥(genFittingFStar ↥H) ≃* ↥(Fstar H) :=
    Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective
  rw [← Nat.card_congr hF.toEquiv, ← Nat.card_congr (MulAut.congr hF).toEquiv]
  exact s16c1614_card_dvd_fstar_mul_aut ↥H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
