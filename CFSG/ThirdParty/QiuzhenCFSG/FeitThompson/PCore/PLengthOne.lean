module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG
open Subgroup

section PLengthOne

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- If `p` is coprime to `|G|`, then `G` has p-length 1. -/
public theorem CFSG.hasPLengthOne_of_coprime_card {p : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime p (Nat.card G)) :
    HasPLengthOne (p := p) G := by
  have hquot_dvd : Nat.card (G ⧸ Op_p'p p G) ∣ Nat.card G := by
    simpa [Subgroup.index_eq_card] using (Subgroup.index_dvd_card (H := Op_p'p p G))
  have hcopQ : Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) :=
    Nat.Coprime.of_dvd_right hquot_dvd hcop
  have htop_le_core :
      (⊤ : Subgroup (G ⧸ Op_p'p p G)) ≤ pPrimeCore p (G ⧸ Op_p'p p G) := by
    exact le_sSup ⟨(inferInstance : (⊤ : Subgroup (G ⧸ Op_p'p p G)).Normal), by simpa using hcopQ⟩
  have hcore_top : pPrimeCore p (G ⧸ Op_p'p p G) = ⊤ := top_unique htop_le_core
  simp [HasPLengthOne, Op_p'pp', hcore_top]

/-- `p`-length 1 is invariant under group isomorphism. -/
public theorem CFSG.hasPLengthOne_of_equiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {p : ℕ} [Fact p.Prime] (e : G ≃* G') :
    HasPLengthOne (p := p) G → HasPLengthOne (p := p) G' := by
  intro hplen
  have hcomp :
      HasNormalPComplement p (↥(pElementsSubgroup p G)) :=
    (hasPLengthOne_iff_hasNormalPComplement_pElements (G := G) (p := p)).1 hplen
  let eP :
      ↥(pElementsSubgroup p G) ≃* ↥((pElementsSubgroup p G).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective (f := e.toMonoidHom) (pElementsSubgroup p G) e.injective
  have hcompMap :
      HasNormalPComplement p (↥((pElementsSubgroup p G).map e.toMonoidHom)) :=
    hasNormalPComplement_of_equiv (G := ↥(pElementsSubgroup p G)) (p := p) eP hcomp
  let P' : Subgroup G' := (pElementsSubgroup p G).map e.toMonoidHom
  have hmap_eq : P' = pElementsSubgroup p G' :=
    pElementsSubgroup_map_equiv (G := G) (G' := G') (p := p) e
  have hcompMap' : HasNormalPComplement p (↥P') := hcompMap
  have hcomp' : HasNormalPComplement p (↥(pElementsSubgroup p G')) := by
    rw [← hmap_eq]
    exact hcompMap'
  exact (hasPLengthOne_iff_hasNormalPComplement_pElements (G := G') (p := p)).2 hcomp'

/-- `p`-length 1 transfers through the `commutator_subgroupOf_map` relation. -/
public theorem CFSG.hasPLengthOne_commutator_subgroupOf_map {p : ℕ} [Fact p.Prime]
    (S H R : Subgroup G) (hH_le : H ≤ S) (hR_le : R ≤ S) :
    HasPLengthOne p ↥⁅H.subgroupOf S, R.subgroupOf S⁆ →
      HasPLengthOne p ↥⁅H, R⁆ := by
  intro hsub
  let ecomm :
      ↥⁅H.subgroupOf S, R.subgroupOf S⁆ ≃*
        ↥((⁅H.subgroupOf S, R.subgroupOf S⁆).map S.subtype) :=
    Subgroup.equivMapOfInjective (f := S.subtype) (⁅H.subgroupOf S, R.subgroupOf S⁆)
      S.subtype_injective
  have hmap :
      HasPLengthOne p ↥((⁅H.subgroupOf S, R.subgroupOf S⁆).map S.subtype) :=
    hasPLengthOne_of_equiv (p := p) ecomm hsub
  have hEq :
      (⁅H.subgroupOf S, R.subgroupOf S⁆).map S.subtype = ⁅H, R⁆ :=
    commutator_subgroupOf_map_eq S R H hR_le hH_le
  rw [hEq] at hmap
  exact hmap

end PLengthOne
