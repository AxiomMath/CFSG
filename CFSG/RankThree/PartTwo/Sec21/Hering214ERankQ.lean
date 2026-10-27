module

public import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.RankThree.PartTwo.Sec21.HeringFFLRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_elemAbelian_nine_le_centralizer (h3 : localRank 3 G ≤ 3) {L Q P : Subgroup G}
    (heven : Even (Nat.card (aschbacherSolvableCore 3 L)))
    (hQL : Q ≤ L) (hQ : IsElemAbelian 3 Q) (hQ9 : Nat.card Q = 9)
    (hPC : P ≤ Subgroup.centralizer (L : Set G)) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (hPL : P ⊓ L = ⊥) : False := by
  obtain ⟨-, hTch, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hX3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact hT3
  have hNL : Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) : Set G) :=
    SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L
      (aschbacherSolvableCore 3 ↥L)
  have hPN : P ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) :
      Set G) :=
    (hPC.trans (Subgroup.centralizer_le_normalizer _)).trans hNL
  have hQN : Q ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) :
      Set G) :=
    (hQL.trans Subgroup.le_normalizer).trans hNL
  have hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hPC hx) y (hQL hy)).symm
  have hdisj : ∀ x ∈ P, x ∈ Q → x = 1 := by
    intro x hx hxQ
    have hxb : x ∈ P ⊓ L := Subgroup.mem_inf.mpr ⟨hx, hQL hxQ⟩
    rw [hPL] at hxb
    exact Subgroup.mem_bot.mp hxb
  obtain ⟨K, hKN, hK, hKcard⟩ :=
    CFSG.RankThree.PartTwo.Sec21.exists_elemAbelian_card_mul hP hQ hPN hQN hcomm hdisj
  have hK81 : Nat.card K = 81 := by simp [hKcard, hP9, hQ9]
  have hodd := Sec8.odd_card_of_le_normalizer h3 hK hK81 hX3 hKN
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
