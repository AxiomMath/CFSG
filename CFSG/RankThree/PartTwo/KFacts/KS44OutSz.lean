module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def KPSz : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    CFSG.Assembly.InCatalog S → ¬ 3 ∣ Nat.card S → ∃ f : ℕ, SuzukiModel S 2 f

theorem commutator_le_inner_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : SuzukiModel S p f) :
    commutator (MulAut S) ≤ (MulAut.conj : S →* MulAut S).range := by
  have hcyc := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S p f h).1.1
  have hcomm : IsMulCommutative (Outer S) := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    exact zpow_mul_comm g m n
  have : (MulAut.conj : S →* MulAut S).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hcomm

theorem two_dvd_card_of_suzukiModel {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : SuzukiModel S 2 f) : 2 ∣ Nat.card S := by
  obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := h
  set w := e.symm (CFSG.LieType.Ree.suzukiWElt a K)
  have hw2 : w ^ 2 = 1 := by
    rw [← map_pow, sq]
    have : CFSG.LieType.Ree.suzukiWElt a K * CFSG.LieType.Ree.suzukiWElt a K = 1 :=
      Subtype.ext (Units.ext (suzukiW_mul_self K))
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro hw
    have h1 : CFSG.LieType.Ree.suzukiWElt a K = 1 := by
      rw [← e.apply_symm_apply (CFSG.LieType.Ree.suzukiWElt a K)]
      change e w = 1
      rw [hw, map_one]
    have h2 := congrArg (fun g : suzukiGroup a K =>
      ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h1
    simp [CFSG.LieType.Ree.coe_suzukiWElt, suzukiW] at h2
  rw [← orderOf_eq_prime hw2 hw1]
  exact orderOf_dvd_natCard w

theorem commutator_le_inner_of_not_three_dvd (hSz : KPSz) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Assembly.InCatalog S)
    (h3 : ¬ 3 ∣ Nat.card S) : commutator (MulAut S) ≤ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨f, hf⟩ := hSz S hnab hcat h3
  exact commutator_le_inner_of_suzukiModel hf

theorem two_dvd_card_of_not_three_dvd (hSz : KPSz) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Assembly.InCatalog S)
    (h3 : ¬ 3 ∣ Nat.card S) : 2 ∣ Nat.card S := by
  obtain ⟨f, hf⟩ := hSz S hnab hcat h3
  exact two_dvd_card_of_suzukiModel hf

end CFSG.RankThree.PartTwo.KFacts
