module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankCore

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartOne.FixedRank36

open CFSG

section Conj

variable {G : Type*} [Group G]

@[expose] def conjHom (M X : Subgroup G) (h : M ≤ Subgroup.normalizer (X : Set G)) :
    ↥M →* MulAut ↥X :=
  (Subgroup.normalizerMonoidHom X).comp (Subgroup.inclusion h)

theorem coe_conjHom (M X : Subgroup G) (h : M ≤ Subgroup.normalizer (X : Set G)) (m : M)
    (x : X) : ((conjHom M X h m x : X) : G) = (m : G) * (x : G) * (m : G)⁻¹ := rfl

theorem coe_conjHom_inv (M X : Subgroup G) (h : M ≤ Subgroup.normalizer (X : Set G)) (m : M)
    (x : X) : (((conjHom M X h m)⁻¹ x : X) : G) = (m : G)⁻¹ * (x : G) * (m : G) := by
  rw [← map_inv, coe_conjHom]
  simp

end Conj

section Subtype

variable {G : Type*} [Group G]

theorem map_commutator_subtype (D : Subgroup G) :
    (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_center_subtype (D : Subgroup G) :
    (Subgroup.center ↥D).map D.subtype = D ⊓ Subgroup.centralizer (D : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxD, hx⟩
    refine ⟨⟨x, hxD⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hx g g.2)

theorem commutator_le_center_of_commutator_eq_bot (D : Subgroup G) (h : ⁅⁅D, D⁆, D⁆ = ⊥) :
    commutator ↥D ≤ Subgroup.center ↥D := by
  intro x hx
  have hx' : (x : G) ∈ ⁅D, D⁆ := by
    rw [← map_commutator_subtype]
    exact Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hc := h hx'
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc g g.2)

theorem relIndex_inSubgroup_frattini (D : Subgroup G) :
    (inSubgroup frattini D).relIndex D = Nat.card (↥D ⧸ frattini ↥D) := by
  have h : (Subgroup.map D.subtype (frattini ↥D)).subgroupOf D = frattini ↥D :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  rw [Subgroup.relIndex, inSubgroup, h]
  rfl

end Subtype

section Rank

theorem pRank_le_of_injective {q : ℕ} [Fact q.Prime] {H K : Type*} [Group H] [Group K]
    [Finite K] (f : H →* K) (hf : Function.Injective f) : CFSG.pRank q H ≤ CFSG.pRank q K := by
  refine csSup_le ⟨0, ⊥, ?_, by simp⟩ ?_
  · exact { toIsMulCommutative := inferInstance
            exponent_dvd_p := by simp }
  · rintro r ⟨E, hE, hr⟩
    have : IsElementaryAbelian q (E.map f) := IsElementaryAbelian.map f
    have hcard : Nat.card (E.map f) = q ^ r := by
      rw [Subgroup.card_map_of_injective hf, hr]
    exact le_pRank_of_elem (Fact.out : q.Prime).one_lt this hcard

variable {G : Type*} [Group G] [Finite G]

theorem pRank_fixedSub_conjHom_le {q : ℕ} [Fact q.Prime] (M X : Subgroup G)
    (h : M ≤ Subgroup.normalizer (X : Set G)) (m : M) :
    CFSG.pRank q ↥(fixedSub (conjHom M X h m)) ≤
      CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({(m : G)} : Set G)) := by
  let f : ↥(fixedSub (conjHom M X h m)) →* ↥(X ⊓ Subgroup.centralizer ({(m : G)} : Set G)) :=
    { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.2 ⟨x.1.2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx : conjHom M X h m x.1 = x.1 := x.2
        have := congrArg Subtype.val hx
        rw [coe_conjHom] at this
        exact (mul_inv_eq_iff_eq_mul.1 this).symm⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine pRank_le_of_injective f fun x y hxy => ?_
  have hxy' := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext hxy')

end Rank

end CFSG.RankThree.PartOne.FixedRank36
