module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitRho

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

theorem rhoE_mk_of_comm (S : AbelSub G) (W A : Subgroup G)
    (hAS : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (a : A) (v : S.carrier)
    (hc : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W) :
    rhoE S W A hAS hAW a (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk v) := by
  rw [rhoE_mk]
  refine congrArg Additive.ofMul ?_
  set u : S.carrier := conjSub S (hAS a.2) v with hudef
  have hcoe : ((u * v⁻¹ : S.carrier) : G) = (a : G) * v * (a : G)⁻¹ * v⁻¹ := by
    simp [hudef, conjSub, mul_assoc]
  have hmem : u * v⁻¹ ∈ W.subgroupOf S.carrier := by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hc
  have hu : u = (u * v⁻¹) * v := by group
  rw [hu, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hmem, one_mul]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
