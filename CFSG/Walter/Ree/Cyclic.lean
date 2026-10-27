module

public import CFSG.Walter.Ree.Cyclic.SmallModule
public import CFSG.LieType.Ree.FixedSubgroupData

public noncomputable section

namespace CFSG.Walter.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem shortRestrictHom_injective
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime] :
    Function.Injective
      (ReeTag.shortRestrictHom ReeTag.G2 K (CharP.cast_eq_zero K ReeTag.G2.prime)) := by
  intro g h hgh
  apply ReeTag.shortRep_injective
  ext v
  rw [ReeTag.coe_shortRep_apply, ReeTag.coe_shortRep_apply,
    ← ReeTag.coe_shortRestrictHom_apply (CharP.cast_eq_zero K ReeTag.G2.prime), hgh,
    ReeTag.coe_shortRestrictHom_apply]

theorem reeGamma_isCyclic_sylow
    (a : ℕ) (_ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Nat.card K ^ 2 - Nat.card K + 1)
    (P : Sylow p (ReeTag.G2.reeGamma K a)) :
    IsCyclic (P : Subgroup (ReeTag.G2.reeGamma K a)) := by
  have hle : ReeTag.G2.reeGamma K a ≤ adjointGroup ReeTag.G2.tag K := Subgroup.map_subtype_le _
  let ρ : (P : Subgroup (ReeTag.G2.reeGamma K a)) →* Module.End K (ReeTag.G2.shortModule K) :=
    (ReeTag.shortRestrictHom ReeTag.G2 K (CharP.cast_eq_zero K ReeTag.G2.prime)).comp
      ((Subgroup.inclusion hle).comp (P : Subgroup (ReeTag.G2.reeGamma K a)).subtype)
  have hρ : Function.Injective ρ :=
    (shortRestrictHom_injective K).comp
      ((Subgroup.inclusion_injective hle).comp (Subgroup.subtype_injective _))
  have he : orderOf (Nat.card K : ZMod p) = 6 :=
    Cyclic.orderOf_eq_six Fact.out (hK ▸ dvd_pow_self 3 (by omega)) hp
  refine Cyclic.isCyclic_of_isPGroup_of_finrank_lt (K := K) (W := ReeTag.G2.shortModule K)
    P.isPGroup' ρ hρ ?_
  rw [he, ReeTag.finrank_shortModule]
  decide

end CFSG.Walter.Ree
