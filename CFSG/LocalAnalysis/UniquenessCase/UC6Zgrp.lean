module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_regular_zgroup_data {X V Z : Subgroup G}
    (hXV : X ≤ normalizer (V : Set G)) (hV : V ≠ ⊥) (hX1 : X ≠ ⊥)
    (hodd : Odd (Nat.card X))
    (hreg : ∀ x ∈ X, x ≠ 1 → ∀ v ∈ V, x * v * x⁻¹ = v → v = 1)
    (hZX : Z ≤ X) (hZp : (Nat.card Z).Prime) :
    ∃ (q : ℕ) (Q Y : Subgroup G), q.Prime ∧ IsSylowOf q Q X ∧ IsCyclic Q ∧ Y ≤ Q ∧
      Nat.card Y = q ∧ (∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y) ∧
      ¬ Q ≤ (commutator ↥X).map X.subtype := by
  classical
  letI : MulDistribMulAction ↥X ↥V := Subgroup.conjMulDistribMulActionOfLeNormalizer X V hXV
  haveI : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).2 hV
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hX1
  have hregA : CFSG.ActsRegularly ↥X ↥V := by
    intro a ha1
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hay : a • y = y := hy ⟨a, Subgroup.mem_zpowers a⟩
    have hay' : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := congrArg Subtype.val hay
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact Subtype.ext (hreg (a : G) a.2 ha1' (y : G) y.2 hay')
  haveI hZG : IsZGroup ↥X := by
    rw [isZGroup_iff]
    intro p hp P
    haveI : Fact p.Prime := ⟨hp⟩
    exact CFSG.isCyclic_of_odd_regular_pSubgroup (H := ↥V) (R := ↥X) hp hodd hregA P.isPGroup'
  have hcomm_lt : commutator ↥X < ⊤ := IsZGroup.commutator_lt ↥X
  have hidx : (commutator ↥X).index ≠ 1 := by
    intro h
    exact hcomm_lt.ne (Subgroup.index_eq_one.1 h)
  set q : ℕ := Nat.minFac (commutator ↥X).index with hqdef
  have hq : q.Prime := Nat.minFac_prime hidx
  haveI : Fact q.Prime := ⟨hq⟩
  have hqidx : q ∣ (commutator ↥X).index := Nat.minFac_dvd _
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥X) := inferInstance
  have hQnot : ¬ (Q : Subgroup ↥X) ≤ commutator ↥X := by
    intro hle
    have h1 : (commutator ↥X).index ∣ (Q : Subgroup ↥X).index := Subgroup.index_dvd_of_le hle
    exact Q.not_dvd_index (hqidx.trans h1)
  haveI hQcyc : IsCyclic ↥Q := hZG.isZGroup q hq Q
  set QG : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hQG
  have hQGsyl : IsSylowOf q QG X := ⟨Q, rfl⟩
  have hQGcyc : IsCyclic QG := by
    have e : (Q : Subgroup ↥X) ≃* QG :=
      Subgroup.equivMapOfInjective (Q : Subgroup ↥X) X.subtype X.subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hQGnot : ¬ QG ≤ (commutator ↥X).map X.subtype := by
    intro hle
    apply hQnot
    intro x hx
    have : (x : G) ∈ (commutator ↥X).map X.subtype := hle ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hcx⟩ := this
    have : c = x := Subtype.ext hcx
    exact this ▸ hc
  have hQG1 : QG ≠ ⊥ := by
    intro h
    apply hQGnot
    rw [h]
    exact bot_le
  have hqdvd : q ∣ Nat.card QG := by
    have := hQGsyl.isPGroup.card_eq_or_dvd
    exact this.resolve_left fun h => hQG1 (Subgroup.card_eq_one.mp h)
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have hyord : orderOf (y' : G) = q := (Subgroup.orderOf_coe y').trans hy'
  refine ⟨q, QG, Subgroup.zpowers (y' : G), hq, hQGsyl, hQGcyc,
    Subgroup.zpowers_le.2 y'.2, by rw [Nat.card_zpowers, hyord], ?_, hQGnot⟩
  have hsolv : Group.IsSolvable ↥X := inferInstance
  set Y : Subgroup G := Subgroup.zpowers (y' : G) with hY
  have hYX : Y ≤ X := (Subgroup.zpowers_le.2 y'.2).trans hQGsyl.le
  have hYcard : Nat.card Y = q := by rw [hY, Nat.card_zpowers, hyord]
  have hY'card : Nat.card (Y.subgroupOf X) = q := by
    rw [← hYcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
  have hZ'card : Nat.card (Z.subgroupOf X) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv
  have hY'p : Nat.Prime (Nat.card (Y.subgroupOf X)) := by rw [hY'card]; exact hq
  have hZ'p : Nat.Prime (Nat.card (Z.subgroupOf X)) := by rw [hZ'card]; exact hZp
  have hYF := CFSG.prime_order_subgroup_le_centralizer_fitting_of_odd_regular_action
    (H := ↥V) (R := ↥X) hodd hregA hY'p
  have hZF := CFSG.prime_order_subgroup_le_centralizer_fitting_of_odd_regular_action
    (H := ↥V) (R := ↥X) hodd hregA hZ'p
  have hcf := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  intro y hy z hz
  have hy' : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := hy
  have hz' : (⟨z, hZX hz⟩ : ↥X) ∈ Z.subgroupOf X := hz
  have hzF : (⟨z, hZX hz⟩ : ↥X) ∈ CFSG.fittingSubgroup ↥X := hcf (hZF hz')
  have := mem_centralizer_iff.1 (hYF hy') _ hzF
  exact (congrArg Subtype.val this).symm

end CFSG.LocalAnalysis.UniquenessCase.UC6
