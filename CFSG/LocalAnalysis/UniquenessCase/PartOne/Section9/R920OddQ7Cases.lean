module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyTwoSub
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenSE
import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Gen
import CFSG.Walter.AStar.Basic
import CFSG.Walter.J1Props.Factor
import CFSG.Walter.Models
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem shape92_cases_seven {Q : Type} [Group Q] [Finite Q] (hQ : F09.Shape92 Q)
    {X : Subgroup Q} (hX : IsL2Odd (Bar2 X) 7)
    (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) :
    (∃ p f : ℕ, p ≠ 3 ∧ LieModel Q .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel Q .PSL 3 p f) ∨
      (∃ p f : ℕ, p ≠ 2 ∧ p ^ f % 3 = 1 ∧ LieModel Q .PSU 3 p f) := by
  have hY := isLThreeTwo_of_isL2Odd_seven hX
  rcases hQ with ⟨hc, -⟩ | hJ | ⟨p, f, hL⟩ | ⟨p, f, hpf, hL⟩ | ⟨p, f, hpf, hU⟩
  ·
    exfalso
    have : IsMulCommutative Q := @IsCyclic.isMulCommutative Q _ hc
    exact not_isSolvable_of_isL2Odd_seven hX (le_top : X ≤ ⊤) inferInstance
  ·
    exfalso
    obtain ⟨e⟩ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ
    have hA : CFSG.Walter.HasAbelianSylowTwo Q :=
      CFSG.Walter.J1Props.hasAbelianSylowTwo.of_surjective
        (f := (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨R, -, hR, a, ha, b, hb, hab⟩ :=
      CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.exists_noncomm_two_subgroup_of_isLThreeTwo hY
    obtain ⟨P, hRP⟩ := hR.exists_le_sylow
    exact hab (congrArg Subtype.val ((hA P).is_comm.comm ⟨a, hRP ha⟩ ⟨b, hRP hb⟩))
  · by_cases hp3 : p = 3
    ·
      exfalso
      subst hp3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨-, hf1, -, -, hne⟩ := hL.admissible
      have hf : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        exact hne (by norm_num)
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by norm_num)
        (hL.statedClassicalModel (by decide))
      have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
        rcases hr with ⟨-, ⟨-, h⟩ | ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
        all_goals first | omega | cases h
      obtain ⟨T⟩ : Nonempty (Sylow 3 Q) := inferInstance
      have h1 := CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_three T
        (hcyc T T.isPGroup')
      omega
    · exact Or.inl ⟨p, f, hp3, hL⟩
  · exact Or.inr (Or.inl ⟨p, f, hpf, hL⟩)
  · by_cases hp2 : p = 2
    ·
      exfalso
      subst hp2
      obtain ⟨-, hf1, -, hne⟩ := hU.admissible
      have hf : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        exact hne (by norm_num)
      obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hf
        (hU.statedClassicalModel (by decide))
      have : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv Q e.toEquiv
      have hB := (CFSG.Open.bender_psu3_borel_full f hf).map_mulEquiv e.symm
      exact CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.not_isLThreeTwo_of_stronglyEmbedded
        (fun S => (hB S).1) X hY
    · exact Or.inr (Or.inr ⟨p, f, hp2, hpf, hU⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
