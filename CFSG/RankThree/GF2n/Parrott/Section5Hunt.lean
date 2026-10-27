module

public import CFSG.RankThree.GF2n.Parrott.HuntM22
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem quasisimple_centralizer_of_quotient_psu_six {z₁ : G} (hord : orderOf z₁ = 2)
    [((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal]
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSU 6 2 1)
    (e : ↥(centralizer ({z₁} : Set G)) ⧸
      (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X)
    (hder : z₁ ∈ ⁅centralizer ({z₁} : Set G), centralizer ({z₁} : Set G)⁆) :
    CFSG.IsQuasisimple (centralizer ({z₁} : Set G)) ∧
      Nat.card (center (centralizer ({z₁} : Set G))) = 2 ∧
      CFSG.Blueprint.LieModel (centralizer ({z₁} : Set G) ⧸
        center (centralizer ({z₁} : Set G))) .PSU 6 2 1 := by
  classical
  let C : Subgroup G := centralizer ({z₁} : Set G)
  let Z₀ : Subgroup C := (Subgroup.zpowers z₁).subgroupOf C
  haveI hZ₀n : Z₀.Normal := inferInstance
  have hzC : z₁ ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hXsimple : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hXcard : Nat.card X = 9196830720 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_six_two
      (hX.statedClassicalModel (by decide))
  have hXnc : ¬ IsMulCommutative X := by
    intro hcomm
    haveI : IsMulCommutative X := hcomm
    have hp : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).mp hXsimple
    rw [hXcard] at hp
    have heven : Even 9196830720 := ⟨4598415360, by norm_num⟩
    exact (by norm_num : (9196830720 : ℕ) ≠ 2) ((Nat.Prime.even_iff hp).mp heven)
  have hQsimple : IsSimpleGroup (C ⧸ Z₀) := MulEquiv.isSimpleGroup e
  have hQnc : ¬ IsMulCommutative (C ⧸ Z₀) := by
    rw [isMulCommutative_iff]
    intro hcomm
    apply hXnc
    rw [isMulCommutative_iff]
    intro a b
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    calc e a' * e b' = e (a' * b') := by rw [map_mul]
      _ = e (b' * a') := by rw [hcomm a' b']
      _ = e b' * e a' := by rw [map_mul]
  haveI : IsSimpleGroup (C ⧸ Z₀) := hQsimple
  have hQperfect : Group.IsPerfect (C ⧸ Z₀) :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hQnc
  have hZ₀eq : Z₀ = Subgroup.zpowers (⟨z₁, hzC⟩ : C) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hZ₀center : Z₀ ≤ center C := by
    rw [hZ₀eq]
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)
  have hcardZ₀ : Nat.card Z₀ = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hzC)).toEquiv,
      Nat.card_zpowers, hord]
  have hderC : (⟨z₁, hzC⟩ : C) ∈ commutator C := by
    have h := hder
    rw [← Subgroup.map_subtype_commutator C] at h
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp h
    have hx' : x = ⟨z₁, hzC⟩ := Subtype.ext hxval
    simpa [hx'] using hx
  have hZ₀comm : Z₀ ≤ commutator C := by
    rw [hZ₀eq]
    exact Subgroup.zpowers_le.mpr hderC
  have hCperfect : commutator C = ⊤ := by
    obtain ⟨hsup, -, -⟩ :=
      CFSG.LocalCores.central_extension_derived Z₀ hZ₀center hQperfect
    rwa [sup_eq_left.mpr hZ₀comm] at hsup
  have hQnc' : ∃ a b : C ⧸ Z₀, a * b ≠ b * a := by
    rw [isMulCommutative_iff] at hQnc
    push Not at hQnc
    exact hQnc
  have hcenter : center C = Z₀ :=
    CFSG.LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient Z₀ hZ₀center
      hQsimple hQnc'
  let eZ : C ⧸ center C ≃* C ⧸ Z₀ := QuotientGroup.quotientMulEquivOfEq hcenter
  have hsimpleC : IsSimpleGroup (C ⧸ center C) := MulEquiv.isSimpleGroup eZ
  have hCqnc : ∃ a b : C ⧸ center C, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQnc'
    refine ⟨eZ.symm a, eZ.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eZ h
  have hLmodel : CFSG.Blueprint.LieModel (C ⧸ center C) .PSU 6 2 1 := by
    have h1 : CFSG.Blueprint.LieModel (C ⧸ Z₀) .PSU 6 2 1 := hX.of_mulEquiv e.symm
    exact h1.of_mulEquiv eZ.symm
  exact ⟨⟨Group.IsPerfect.mk hCperfect, hsimpleC, hCqnc⟩,
    by rw [hcenter, hcardZ₀], hLmodel⟩

theorem fi22_of_centralizer_quotient_psu_six
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z₁ : G} (hord : orderOf z₁ = 2)
    (hU : ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
      (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
        Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
          (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    (hder : z₁ ∈ ⁅centralizer ({z₁} : Set G), centralizer ({z₁} : Set G)⁆) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  obtain ⟨hN, X, hXgrp, hX, ⟨e⟩⟩ := hU
  letI : Group X := hXgrp
  haveI : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal := hN
  have hq := quasisimple_centralizer_of_quotient_psu_six (z₁ := z₁) hord hX e hder
  exact huntM22_of_centralizer hnonab hord hq.1 hq.2.1 hq.2.2

end CFSG.RankThree.GF2n.Parrott
