module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence center_map_equiv)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)

theorem k_3D4TwoAut_holds :
    K_3D4TwoAut := by
  classical
  intro X _ _ hX
  have hX' : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1 :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX).2
  obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hX'
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmod
  have hK3 : Nat.card K = (2 ^ 1) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, hcyc, hcard, -, hZ, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form (f := 1) hf K hK3 σ hσ
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hker' : Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner C := hker
  have hZ' : Subgroup.center C = ⊥ := hZ
  let Φ := QuotientGroup.lift (CFSG.ComponentClassification.OuterAutomorphisms.inner C) Θ hker'.ge
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hker'.ge α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have hΦinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hΦker
  let Ψ : Outer C ≃* (K ≃+* K) := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hcycC : IsCyclic (Outer C) := (MulEquiv.isCyclic Ψ).mpr hcyc
  have hcardOC : Nat.card (Outer C) = 3 := by
    rw [Nat.card_congr Ψ.toEquiv, hcard, Nat.mul_one]
  have hcenterX : Subgroup.center X = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : e x ∈ Subgroup.center C := by
      rw [← center_map_equiv e]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hZ'] at hx'
    have hx1 : e x = 1 := Subgroup.mem_bot.mp hx'
    have hx2 : x = 1 := by
      apply e.injective
      rw [map_one]
      exact hx1
    simpa using hx2
  refine ⟨hcenterX, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (equivalence e)).mpr hcycC
  · rw [Nat.card_congr (equivalence e).toEquiv]
    exact hcardOC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
