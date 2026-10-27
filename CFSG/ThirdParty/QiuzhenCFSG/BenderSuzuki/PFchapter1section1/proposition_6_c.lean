module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 6(c)
-/

private theorem proposition_6_c_exists_involution_of_even_card
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK_even : Even (Nat.card K)) :
    ∃ u : G, u ∈ K ∧ IsInvolution u := by
  classical
  have hK_even_card : Even (Nat.card K) := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hK_even
  have htwo_dvd_card : 2 ∣ Nat.card K := even_iff_two_dvd.mp hK_even_card
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 htwo_dvd_card
  refine ⟨u, u.property, ?_⟩
  constructor
  · intro hu_one
    have horder_one : orderOf u = 1 := by
      have : u = 1 := by
        ext
        exact hu_one
      simp [this]
    omega
  · have hpow : u ^ 2 = 1 := by
      simpa [hu_order] using pow_orderOf_eq_one u
    exact congrArg Subtype.val hpow


public theorem proposition_6_c
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hX_le_D : X ≤ D)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    ∃ d : D, rightConjugate X (d : G) ≤ peterfalviV D t := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hCQ_even : Even (Nat.card (α := (((C : Subgroup G) ⊓ Q : Subgroup G)))) := by
    simpa [C] using proposition_6_b H D Q X t hA1 hX_le_D hfixed
  rcases proposition_6_c_exists_involution_of_even_card ((C : Subgroup G) ⊓ Q) hCQ_even with
    ⟨y, hyCQ, hyI⟩
  obtain ⟨p, hp, _hpuniq⟩ := proposition_4_b H D Q t hA1
  let s : G := p.1
  have hyH : y ∈ H := hA1.Q_le_H hyCQ.2
  have hX_le_Cy : X ≤ Subgroup.centralizer ({y} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : x * y = y * x :=
      (Subgroup.mem_centralizer_iff.mp hyCQ.1) x hx
    exact hcomm
  exact
    proposition_5_conjugate_into_V_of_centralized_involution
      H D Q X t s y hA1
      hp.1 hp.2.1 ⟨p.2, hp.2.2.1, hp.2.2.2⟩ hX_le_D hyH hyI hX_le_Cy

end PFchapter1section1
end CFSG.BenderSuzuki

