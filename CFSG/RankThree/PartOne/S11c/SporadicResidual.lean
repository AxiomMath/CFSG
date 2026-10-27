module

public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.S11.CatalogLeaves

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic)

@[expose] def SporadicPlanesCentralize (A : Type) [Group A] : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* A) → ∀ (p : ℕ) (E : Subgroup (MulAut T)) (U : Subgroup T), PlaneOn p E U →
      PlaneCentralizes E U

structure SporadicResidualInputs : Prop where
  m11 : SporadicPlanesCentralize (Carrier .M11)
  m12 : SporadicPlanesCentralize (Carrier .M12)
  m22 : SporadicPlanesCentralize (Carrier .M22)
  m23 : SporadicPlanesCentralize (Carrier .M23)
  m24 : SporadicPlanesCentralize (Carrier .M24)
  j1 : SporadicPlanesCentralize (Carrier .J1)
  j2 : SporadicPlanesCentralize (Carrier .J2)
  j3 : SporadicPlanesCentralize (Carrier .J3)
  hs : SporadicPlanesCentralize (Carrier .HS)
  mcl : SporadicPlanesCentralize (Carrier .McL)
  he : SporadicPlanesCentralize (Carrier .He)
  ru : SporadicPlanesCentralize (Carrier .Ru)
  on : SporadicPlanesCentralize (Carrier .ONan)
  co2 : SporadicPlanesCentralize (Carrier .Co2)
  co3 : SporadicPlanesCentralize (Carrier .Co3)
  th : SporadicPlanesCentralize (Carrier .Th)
  fi22 : SectionsForceEvenRankFour (Carrier .Fi22)
  fi23 : SectionsForceEvenRankFour (Carrier .Fi23)
  fi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime)
  b : SectionsForceEvenRankFour (Carrier .B)
  m : SimplePresentationMSectionsForceEvenRankFour

theorem sporadicResidual_of_inputs (h : SporadicResidualInputs) :
    ActualCoverSporadicMovingPlaneFiveModelResidual := by
  intro H _ _ hH X hX hspor p E U hpl hnc
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have hnab := hX.2.2
  have hrank : evenRank H ≤ 3 := by
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact hH
  have byPlane : SporadicPlanesCentralize (Carrier s) → False := fun hs =>
    hnc (hs _ hsimple hnab ⟨e⟩ p E U hpl)
  have bySection : SectionsForceEvenRankFour (Carrier s) → False := fun hsec => by
    have h4 := hsec H X (Subgroup.center X) ⟨e⟩
    omega
  cases s
  · exact (byPlane h.m11).elim
  · exact (byPlane h.m12).elim
  · exact (byPlane h.m22).elim
  · exact (byPlane h.m23).elim
  · exact (byPlane h.m24).elim
  · exact (byPlane h.j1).elim
  · exact (byPlane h.j2).elim
  · exact (byPlane h.j3).elim
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact (byPlane h.hs).elim
  · exact (byPlane h.mcl).elim
  · exact (byPlane h.he).elim
  · exact (byPlane h.ru).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  · exact (byPlane h.on).elim
  · exact Or.inl ⟨e⟩
  · exact (byPlane h.co2).elim
  · exact (byPlane h.co3).elim
  · exact (bySection h.fi22).elim
  · exact (bySection h.fi23).elim
  · exact (bySection h.fi24).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact (byPlane h.th).elim
  · exact (bySection h.b).elim
  · have h4 := h.m H X (Subgroup.center X) (X ⧸ Subgroup.center X) hnab ⟨MulEquiv.refl _⟩ ⟨e⟩
    omega

end CFSG.RankThree.PartOne
