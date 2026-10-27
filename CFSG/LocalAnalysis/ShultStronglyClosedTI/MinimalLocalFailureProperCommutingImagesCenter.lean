module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem properCommutingImages_center_normal_in_point
    (H S : Subgroup G) (hSH : S ≤ H) (hSN : (S.subgroupOf H).Normal) :
    (((Subgroup.center S).map S.subtype).subgroupOf H).Normal := by
  exact normal_subgroupOf_map_of_characteristic_of_normal S _ H hSH hSN
    (Subgroup.center S) inferInstance rfl ((Subgroup.map_subtype_le _).trans hSH)

theorem properCommutingImages_center_image_commute
    (S : Subgroup G) {a b : G}
    (ha : a ∈ (Subgroup.center S).map S.subtype)
    (hb : b ∈ (Subgroup.center S).map S.subtype) : Commute a b := by
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b₀, _, rfl⟩ := Subgroup.mem_map.mp hb
  change (a₀ : G) * (b₀ : G) = (b₀ : G) * (a₀ : G)
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp ha₀) b₀).symm

variable [Finite G]

theorem properCommutingImages_twoGroup_central_involution
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    ∃ z : G, z ∈ (Subgroup.center S).map S.subtype ∧ orderOf z = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  let : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdiv
  refine ⟨(z : S), Subgroup.mem_map_of_mem S.subtype z.property, ?_⟩
  exact (Subgroup.orderOf_coe (z : S)).trans ((Subgroup.orderOf_coe z).trans hz)

theorem properCommutingImages_involutions_in_normal_root_center
    (H : Subgroup G) (hH : IsStronglyEmbedded H)
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSH : S ≤ H)
    (hSN : (S.subgroupOf H).Normal) (hSne : S ≠ ⊥)
    (a : G) (haH : a ∈ H) (haorder : orderOf a = 2) :
    a ∈ (Subgroup.center S).map S.subtype := by
  let Z := (Subgroup.center S).map S.subtype
  have hZH : Z ≤ H := (Subgroup.map_subtype_le _).trans hSH
  have hZN : (Z.subgroupOf H).Normal :=
    properCommutingImages_center_normal_in_point H S hSH hSN
  have hHnorm : H ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mp hZN
  obtain ⟨z, hzZ, hzorder⟩ := properCommutingImages_twoGroup_central_involution S hS hSne
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hzorder).2, (orderOf_eq_prime_iff.mp hzorder).1⟩
  have ha : IsInvolution a :=
    ⟨(orderOf_eq_prime_iff.mp haorder).2, (orderOf_eq_prime_iff.mp haorder).1⟩
  obtain ⟨g, hgH, hga⟩ := hH.involutions_conjugate_in (hZH hzZ) hz haH ha
  have hZg : rightConjugate Z g = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (Z : Set G)).inv_mem (hHnorm hgH))
  have hzmap : rightConjugateElem z g ∈ rightConjugate Z g :=
    rightConjugateElem_mem_rightConjugate hzZ
  rwa [hga, hZg] at hzmap

end CFSG.ShultStronglyClosedTI
