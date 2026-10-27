module

public import CFSG.RankThree.PartTwo.Sec16.Item165Proof
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Res165R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → IsL3TwoPow L →
      ∀ X ∈ scriptY3Star A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
        ¬ Group.IsSolvable ↥X → oPrimeResidualOf 3 X ≤ Y₀

@[expose] noncomputable def Red165R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → IsL3TwoPow L →
      ∀ X ∈ scriptY3Star A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
        ¬ Group.IsSolvable ↥X → oPrimeResidualOf 3 X ≤ Y₀ →
          ∀ T ∈ scriptQPiStar A (lB A) X (piOf 2),
            ∃ X' ∈ scriptY3 A (lB A), ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧
              ¬ 3 ∣ Nat.card X' ∧ T ≤ X'

namespace Steps165

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_of_isSolvable {A : Subgroup G} (hAF : A ∈ partTwoF G) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hXs : Group.IsSolvable ↥X) : ¬ 3 ∣ Nat.card X := by
  have hΔ : delta A (lB A) X ≤ pPrimeCoreOf 3 X := by
    refine sSup_le fun Q hQ => ?_
    have hQ3 : ¬ 3 ∣ Nat.card Q :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    refine le_pPrimeCoreOf_of_isSolvable hAF.1 (fun y hy hy3 => ?_) hX.1.1.2 hXs hQ.2 hQ3
      hQ.1.1.2.2
    exact Sec15.mem_of_mem_partTwoF hAF hy3 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy a ha)
  have hle : X ≤ pPrimeCoreOf 3 X := by
    calc X = delta A (lB A) X := hX.2
      _ ≤ pPrimeCoreOf 3 X := hΔ
  have heq : pPrimeCoreOf 3 X = X := le_antisymm (pPrimeCoreOf_le 3 X) hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop := coprime_card_pPrimeCoreOf 3 X
  rw [heq] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop

theorem exists_star {A : Subgroup G} (hAF : A ∈ partTwoF G) {Y₀ X T : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G))
    (h3 : 3 ∣ Nat.card X) (hT : T ∈ scriptQPiStar A (lB A) X (piOf 2)) :
    ∃ X' ∈ scriptY3Star A (lB A), ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      ¬ Group.IsSolvable ↥X' ∧ ∃ T' ∈ scriptQPiStar A (lB A) X' (piOf 2), T ≤ T' := by
  obtain ⟨X', hXX', hX'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hX
  have hX'M : ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) := fun h => hXM (hXX'.trans h)
  have hX's : ¬ Group.IsSolvable ↥X' := fun hs =>
    not_three_dvd_of_isSolvable hAF hX'.prop hs (h3.trans (Subgroup.card_dvd_of_le hXX'))
  have hT' : T ∈ scriptQPi A (lB A) X' (piOf 2) :=
    ⟨⟨hT.prop.1.1, hT.prop.1.2.trans hXX'⟩, hT.prop.2⟩
  obtain ⟨T', hTT', hT'max⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) X' (piOf 2))) hT'
  exact ⟨X', hX', hX'M, hX's, T', hT'max, hTT'⟩

end Steps165

theorem step165Three_of (hRes : Res165R) (hRed : Red165R) : Step165Three := by
  intro G _ _ A c L Y₀ h hL3 X hX hXM h3 T hT
  obtain ⟨X', hX', hX'M, hX's, T', hT', hTT'⟩ :=
    Steps165.exists_star h.mem_partTwoF hX hXM h3 hT
  obtain ⟨X'', hX'', hX''M, hX''3, hT'X''⟩ := hRed G A c L Y₀ h hL3 X' hX' hX'M hX's
    (hRes G A c L Y₀ h hL3 X' hX' hX'M hX's) T' hT'
  exact ⟨X'', hX'', hX''M, hX''3, hTT'.trans hT'X''⟩

end CFSG.RankThree.PartTwo.Sec16
