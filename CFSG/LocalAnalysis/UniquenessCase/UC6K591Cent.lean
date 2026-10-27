module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open scoped MatrixGroups

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have ha : a ∈ center X := by rw [h]; exact mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem exists_noncomm_of_simple_of_even {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (h3 : 2 < Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra! hcomm
  letI : CommGroup X := { ‹Group X› with mul_comm := fun a b => hcomm a b }
  have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card (α := X)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  omega

theorem centreless_of_isAlt_ten {X : Type} [Group X] (h : IsAlt X 10) : center X = ⊥ := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card X = 1814400 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  refine center_eq_bot_of_simple (exists_noncomm_of_simple_of_even ?_ ?_) <;> rw [hcard] <;> norm_num

end CFSG.LocalAnalysis.UniquenessCase.UC6
