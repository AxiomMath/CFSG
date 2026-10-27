module

public import CFSG.RankThree.PartOne.FOCD.CompGood
public import CFSG.RankThree.PartOne.S11d.LieGoodTransfer
public import CFSG.RankThree.PartOne.TCF.Simple
public import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC

theorem compGoodAt_of_simple_layer {G : Type} [Group G] [Finite G] {J : Subgroup G} {d : G}
    (hdJ : d ∈ J) {Q : Subgroup G} (hQs : IsSimpleGroup ↥Q) (hQnc : ∃ x y : ↥Q, x * y ≠ y * x)
    (hQD : Q ≤ J ⊓ Subgroup.centralizer ({d} : Set G))
    (hDQ : ⁅J ⊓ Subgroup.centralizer ({d} : Set G), J ⊓ Subgroup.centralizer ({d} : Set G)⁆ ≤ Q)
    {p : ℕ} (hpQ : p ∣ Nat.card Q) : CompGoodAt p (⟨d, hdJ⟩ : ↥J) := by
  intro E hE
  have hE' : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) (E.map J.subtype) :=
    isComponentOf_map_subtype hdJ hE.2.1 hE.1 hE.2.2
  have hns : ¬ Group.IsSolvable ↥Q := by
    intro h
    obtain ⟨x, y, hxy⟩ := hQnc
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 h x y)
  have hEQ : E.map J.subtype = Q :=
    TCF.component_eq_of_simpleOrBot hQD hDQ (Or.inr ⟨hQs, hns⟩) hE'
  let e : ↥E ≃* ↥Q := (Subgroup.equivMapOfInjective E J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hEQ)
  have hEs : IsSimpleGroup ↥E := by
    have := hQs
    exact e.isSimpleGroup
  have hEnc : ∃ a b : ↥E, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hQnc
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
    have hc : (⟨z, hzE⟩ : ↥E) ∈ Subgroup.center ↥E := Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC y y.2)
    rw [center_eq_bot_of_nonab hEs hEnc, Subgroup.mem_bot] at hc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hc
  · rw [Nat.card_congr e.toEquiv]
    exact hpQ

theorem compGoodAt_of_comm {T : Type} [Group T] {p : ℕ} {b : T}
    (h : ∀ x ∈ Subgroup.centralizer ({b} : Set T), ∀ y ∈ Subgroup.centralizer ({b} : Set T),
      x * y = y * x) : CompGoodAt p b := by
  intro E hE
  exfalso
  have hEsolv : Group.IsSolvable ↥E :=
    Group.isSolvable_of_comm fun u v => Subtype.ext (h u (hE.1 u.2) v (hE.1 v.2))
  have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.2.1
  have : Group.IsPerfect ↥E := hE.2.1.1
  exact Group.IsPerfect.not_isSolvable ↥E hEsolv

end CFSG.RankThree.PartOne.FOCD
