module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

theorem item1418R_of_uniq (h1417 : Item1417_2R) (hU : Step1418UniqR) : Item1418R := by
  intro G _ _ A c L hR hfail S hS B hB hSB
  have hA : IsE27 A := hR.toSec14Std.isE27
  have hpt : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ¬ IsConjIn (xA A) S T →
      ∀ b ∈ B, b ≠ 1 → T ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ →
        Subgroup.zpowers b ∈ gammaA A (lB A) := by
    intro T hT hST b hb hb1 hTb
    have hSb : S ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
      intro h
      apply hSB
      rw [eq_bot_iff, ← h]
      exact inf_le_inf_left S (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    exact h1417 G A c L hR hfail S hS T hT hST b (hB.1 hb) hb1 hSb hTb
  have hT3 : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ¬ 3 ∣ Nat.card T := fun T hT =>
    (isPiSubgroup_piCompl_iff Nat.prime_three T).mp hT.prop.1.1.1.2.1
  obtain ⟨T, hT, hST⟩ := Proof1413Res2.exists_not_isConjIn hfail.1 S
  obtain ⟨b, hb, hb1, hTb⟩ :=
    Proof1413Res2.exists_mem_hyperplane_inf_centralizer_ne_bot hA hB hT.prop.1.1.1.2.2
      (hT3 T hT) (Proof1413Res2.ne_bot_of_not_isConjIn hS hT hST)
  have hbΓ := hpt T hT hST b hb hb1 hTb
  by_contra hno
  have huniq : ∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b := by
    intro F hF hFB
    by_contra hne
    exact hno ⟨F, hF, _, hbΓ, hne, hFB, Subgroup.zpowers_le.mpr hb⟩
  apply hU G A c L hR hfail S hS B hB hSB b hb hbΓ huniq
  intro T' hT' hST'
  refine Proof1413Res2.le_of_forall_centralizer hA hB hT'.prop.1.1.1.2.2 (hT3 T' hT')
    fun b' hb' hb'1 hTb' => ?_
  rw [centralizer_singleton_eq_of_zpowers_eq (huniq _ (hpt T' hT' hST' b' hb' hb'1 hTb')
    (Subgroup.zpowers_le.mpr hb'))]
  exact inf_le_right

end CFSG.RankThree.PartTwo.Sec14
