module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
public import CFSG.LocalAnalysis.WeakClosure81.CentralInSylowIndexReverse

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

@[expose] def Orth6MinusOddTranspFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsOrth6MinusMod Y → ∀ d : Y, d * d = 1 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTranspClass {y : Y | IsConj d y} →
      Even (Subgroup.centralizer ({d} : Set Y)).index

theorem w3Lem85TwoGap6_of_fact (h : Orth6MinusOddTranspFact) : W3Lem85TwoGap6 := by
  intro X _ _ S hS h2 hX hc
  obtain ⟨Y, _, φ, hφ, hk3, -, hY⟩ := hX
  haveI : Finite Y := Finite.of_surjective φ hφ
  have hodd : Odd (Nat.card φ.ker) := by rw [hk3]; exact ⟨1, rfl⟩
  obtain ⟨d, hdd, -, hSd, hcl⟩ := barSituation_map_two hS h2 φ hφ hodd
  have hcs := centralInSylow_map φ hφ S hc
  rw [hSd] at hcs
  have hindex := (centralInSylow_zpowers_iff_odd_index d hdd).1 hcs
  exact (Nat.not_even_iff_odd.2 hindex) (h Y hY d hdd hcl)

end CFSG.LocalAnalysis.WeakClosure81

end
