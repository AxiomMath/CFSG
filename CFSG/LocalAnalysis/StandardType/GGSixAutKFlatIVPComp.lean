module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.ComponentClassification.CatalogueBAlternating

section PComponent

variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

theorem ggPComponent_iff_data {A B : Subgroup G} (hAB : A ≤ B) :
    CFSG.IsPComponent p (A.subgroupOf B) ↔
      IsSubnormal A B ∧ primeResidual p A = ⊤ ∧ CFSG.IsQuasisimple (A ⧸ pPrimeCore p A) := by
  rw [pComponent_subgroupOf_iff p A B hAB, IsSubnormal.iff_subgroupOf hAB]

theorem ggLargeEvenPComponent_iff (X L : Subgroup G) :
    LargeEvenPComponent p X L ↔ L ≤ X ∧ CFSG.IsPComponent p (L.subgroupOf X) := by
  have key : LargeEvenPComponent p X L ↔ L ≤ X ∧ CFSG.Open.lBalanceIsPComponent p X L := by
    constructor
    · rintro ⟨hLX, hs, hc, hmin⟩
      refine ⟨hLX, (LBalance.pComponent_iff_minimal_image p X L hLX).2
        ⟨isSubnormal_iff_open.1 hs, ⟨hc.1, isSubnormal_iff_open.1 hc.2.1, hc.2.2⟩, ?_⟩⟩
      intro J hJL hJ heq
      by_contra hne
      exact hmin J (lt_of_le_of_ne hJL hne) (isSubnormal_iff_open.2 hJ) heq
    · rintro ⟨hLX, hL⟩
      obtain ⟨hs, hc, hmin⟩ := (LBalance.pComponent_iff_minimal_image p X L hLX).1 hL
      refine ⟨hLX, isSubnormal_iff_open.2 hs,
        ⟨hc.1, isSubnormal_iff_open.2 hc.2.1, hc.2.2⟩, ?_⟩
      intro J hJL hJ heq
      exact hJL.ne (hmin J hJL.le (isSubnormal_iff_open.1 hJ) heq)
  rw [key]
  exact and_congr_right fun hLX => (pComponent_subgroupOf_iff_lBalance p X L hLX).symm

theorem ggPComponent_subgroupOf_of_le {A Y Z : Subgroup G} (hAZ : A ≤ Z) (hZY : Z ≤ Y)
    (h : CFSG.IsPComponent p (A.subgroupOf Y)) : CFSG.IsPComponent p (A.subgroupOf Z) := by
  rw [ggPComponent_iff_data p hAZ]
  have hdata := (ggPComponent_iff_data p (hAZ.trans hZY)).1 h
  refine ⟨?_, hdata.2⟩
  have hsub := hdata.1.inf_of_le hZY
  rwa [inf_eq_left.mpr hAZ] at hsub

theorem ggPComponent_subgroupOf_of_subnormal {A Y Z : Subgroup G} (hAY : A ≤ Y)
    (hYZ : IsSubnormal Y Z) (h : CFSG.IsPComponent p (A.subgroupOf Y)) :
    CFSG.IsPComponent p (A.subgroupOf Z) := by
  rw [ggPComponent_iff_data p (hAY.trans hYZ.le)]
  have hdata := (ggPComponent_iff_data p hAY).1 h
  exact ⟨hdata.1.trans hYZ, hdata.2⟩

theorem ggPComponent_commutator_eq {A B : Subgroup G} (hAB : A ≤ B)
    (h : CFSG.IsPComponent p (A.subgroupOf B)) : ⁅A, A⁆ = A := by
  haveI : Group.IsPerfect (A.subgroupOf B) := pComponent_perfect h
  have hperfA : Group.IsPerfect (A : Subgroup G) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hAB).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAB).surjective
  exact Subgroup.isPerfect_iff.mp hperfA

theorem ggPComponent_map_subtype {W : Subgroup G} {A B : Subgroup ↥W} (hAB : A ≤ B)
    (h : CFSG.IsPComponent p (A.subgroupOf B)) :
    CFSG.IsPComponent p ((A.map W.subtype).subgroupOf (B.map W.subtype)) := by
  have hdata := (ggPComponent_iff_data p hAB).1 h
  let e := A.equivMapOfInjective W.subtype W.subtype_injective
  refine (ggPComponent_iff_data p (Subgroup.map_mono hAB)).2 ?_
  exact ⟨hdata.1.map W.subtype, primeResidual_eq_top_of_equiv p e hdata.2.1,
    quasisimple_primeCore_quotient_of_equiv p e hdata.2.2⟩

end PComponent

end CFSG.StandardType
