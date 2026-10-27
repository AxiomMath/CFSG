module

import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hy : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [h, Subgroup.mem_bot] at hy
  exact e.injective (by rw [hy, map_one])

theorem center_eq_bot_of_isLThreePi {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (h : IsLThreePi X) : Subgroup.center X = ⊥ := by
  obtain ⟨p, e, _, he, h⟩ := h
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv' φ (Sec13.isPerfect_center_projSL p e he hq).2
  · by_cases hq2 : 2 < p ^ e
    · exact center_eq_bot_of_mulEquiv' φ (Sec13.isPerfect_center_projSU p e he hq hq2).2
    · exfalso
      have hp : p.Prime := Fact.out
      have h1 : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
      have h2 : p ^ e = 2 := by omega
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp h2
      have hs := Sec13.isSolvable_projSU_two
      have hsolv : IsSolvable X :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have : Group.IsPerfect X := hX.1
      have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
      exact Group.IsPerfect.not_isSolvable X hsolv

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
