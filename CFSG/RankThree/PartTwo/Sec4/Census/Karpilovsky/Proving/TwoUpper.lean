module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open Subgroup

theorem center_eq_bot_of_simple_nonabelian (X : Type) [Group X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ center X := by rw [h]; exact Subgroup.mem_top a
    exact hab ((mem_center_iff.mp ha) b).symm

theorem twoUpper_of_rowBound (s : TauCeti.SporadicName)
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier s)]
    [IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s)]
    (hnc : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier s, a * b ≠ b * a)
    (h : CFSG.EvenSporadicStandard.RowBound s)
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* CFSG.Blueprint.NativeSporadic.Carrier s)
    (hsurj : Function.Surjective π) (hcen : π.ker ≤ center E) (h2 : IsPGroup 2 π.ker) :
    Nat.card π.ker ∣ CFSG.EvenSporadicStandard.twoPartBound s := by
  have hZ : center E = π.ker := by
    refine le_antisymm ?_ hcen
    intro z hz
    have hcentral : π z ∈ center (CFSG.Blueprint.NativeSporadic.Carrier s) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hsurj g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz x)]
    rw [center_eq_bot_of_simple_nonabelian _ hnc, mem_bot] at hcentral
    exact hcentral
  have hcard : Nat.card π.ker = Nat.card (center E) := by rw [hZ]
  let e : (E ⧸ center E) ≃* CFSG.Blueprint.NativeSporadic.Carrier s :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hsurj)
  have hq : CFSG.Open.IsQuasisimple E := by
    refine ⟨Group.isPerfect_def.mp inferInstance, ?_⟩
    exact e.isSimpleGroup
  have hsp : CFSG.Blueprint.NativeSporadic.IsSporadic (E ⧸ center E) s := ⟨e⟩
  have h2' : IsPGroup 2 (center E) := by rw [hZ]; exact h2
  rw [hcard]
  exact (h E hq h2' hsp).1

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
