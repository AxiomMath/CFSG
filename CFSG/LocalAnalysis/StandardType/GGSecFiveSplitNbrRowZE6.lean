module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZReduce
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZE6Torus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerE6TwoRows
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration TableB

theorem ggTorusDetEltElt_adjoint_E6_two_seven
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (r : ℕ) :
    NbrFrameDet.GGTorusDetEltElt 7 r (adjointGroup .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  obtain ⟨s, m, hs, hm, hZ⟩ := exists_order_seven_frobenius_sl3 hK
  obtain ⟨ρ, hρ, hc, -⟩ := exists_sl3_frame_E6 (K := K)
  exact NbrFrameDet.ggTorusDetEltElt_of_sylowTorus_frame Nat.prime_seven
    (Units.mk0 (2 : ZMod 7) (by decide)) (by decide) s m hs hm hZ
    (sylowTorus_adjoint_E6_two_seven hK) ρ hρ hc r

theorem ggDetAt_E6_two_seven
    {lab : LargeEvenLabel} (h : lab.tag = .E6 ∧ lab.n = 1) : GGDetAt 7 lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK2)
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 0, TypeA.ggTorusLift_zero ?_, ?_⟩
  · show 2 ∣ Nat.card (TableBExc.RecipeGroup .E6 K)
    rw [Nat.card_congr (TableBExc.recipeEquiv .E6 K).toEquiv]
    exact two_dvd_card_adjoint_E6
  · intro L' _ _ ψ A hA
    exact NbrFrameDet.ggTorusDetElt_of_elt Nat.prime_seven
      (TableBExc.E6Three.recipeID_subset_inn_E6_two hK2)
      (TableBExc.center_recipeGroup_eq_bot .E6 K) (ggCenterPrime_recipe_E6_two hK2 Nat.prime_seven)
      (NbrFrameDet.ggTorusDetEltElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
        (ggTorusDetEltElt_adjoint_E6_two_seven hK2 0)) L' ψ A hA

theorem ggRowZE6_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G}
    (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) (hrow : GGInnerDiagOnLabel ggRowP_ZE6 p Bs K) : False := by
  refine ggRowZ_absurd_of_detElt ggLabelRigidInput_holds (S := ggRowP_ZE6) ?_ hcfg hK hrow
  intro p' _ _ lab _ h
  obtain ⟨ht, hn, rfl⟩ := h
  exact ggDetAt_E6_two_seven ⟨ht, hn⟩

end CFSG.StandardType

end
