module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Quasithin.EmptyFaithfulMultiple (wreathSThreeTwo)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem pCore_two_Hbar_eq_bot (S : Setting z E F) :
    CFSG.pCore 2 (Hbar z) = ⊥ := by
  let N : Subgroup ↥(H z) := (Q z).subgroupOf (H z)
  haveI : N.Normal := instNormalQH z
  let q : ↥(H z) →* Hbar z := QuotientGroup.mk' N
  have hQp : IsPGroup 2 N := (Q_isPGroup S).comap_subtype
  have hmap : (CFSG.pCore 2 ↥(H z)).map q = CFSG.pCore 2 (Hbar z) :=
    CFSG.pCore_map_mk'_eq_of_normal_isPGroup (G := ↥(H z)) (p := 2) N hQp
  rw [← hmap]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.pCore 2 ↥(H z) ≤ N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxfit : x ∈ CFSG.fittingSubgroup (↥(H z)) :=
      CFSG.pCore_le_fitting (↥(H z)) 2 hx
    have hxgen : x ∈ CFSG.generalizedFitting (↥(H z)) := by
      rw [CFSG.generalizedFitting.eq_sup]
      exact Subgroup.mem_sup_left hxfit
    change (x : G) ∈ CFSG.LargeExtraspecial.Timmesfeld.fStar (H z)
    exact Subgroup.mem_map.mpr ⟨x, hxgen, rfl⟩
  apply (Subgroup.map_eq_bot_iff (f := q) (H := CFSG.pCore 2 ↥(H z))).mpr
  rw [show q.ker = N from QuotientGroup.ker_mk' N]
  exact hle

end CFSG.RankThree.GF2n.Stroth78
