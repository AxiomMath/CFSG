module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Model
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Reduce

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Asch6 CFSG.Open

theorem asch6_4Odd_holds : Asch6_4Odd := by
  intro Q _ _ V _ _ hV ρ hρ L A _ hAL hA4 hA2 hquad hAC p e hp hp2 hq9 hL2
  unfold IsElemAbelian at hA2
  have hA2' : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h := hA2.2 a ha
    rwa [pow_two] at h
  unfold CFSG.Quasithin.F6.IsL2 at hL2
  unfold StatedClassicalModel at hL2
  obtain ⟨-, K, _, _, hKcard, ⟨e₂⟩⟩ := hL2
  let eL : ↥L ≃* CFSG.GorensteinWalter.PSL2 K :=
    e₂.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    omega
  letI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hL : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hZ : Subgroup.center ↥L = ⊥ := by
    have hmap := Subgroup.map_center_eq eL
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot K] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.injective).mp hmap
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h11 : 11 ≤ p ^ e := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have h7 : 7 ≤ p ^ e := by omega
  have hne9 : p ^ e ≠ 9 := by omega
  have hX : L2AutFacts ↥L :=
    (l2AutFacts_psl2 hp hp2 hKcard h7 hne9).of_mulEquiv eL.symm
  have hI : L2InnerFacts ↥L :=
    (l2InnerFacts_psl2 hp hp2 hKcard h11).of_mulEquiv eL.symm
  exact false_of_l2Facts_of_rep hV ρ hρ hL hZ hX hI hAL hA4 hA2' hquad hAC

theorem asch6_4Seven_holds : Asch6_4Seven := by
  intro Q _ _ V _ _ hV ρ hρ L A _ hAL hA4 hA2 hquad hAC hL2 a ha
  unfold IsElemAbelian at hA2
  have hA2' : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h := hA2.2 a ha
    rwa [pow_two] at h
  unfold CFSG.Quasithin.F6.IsL2 at hL2
  unfold StatedClassicalModel at hL2
  obtain ⟨-, K, _, _, hKcard, ⟨e₂⟩⟩ := hL2
  let eL : ↥L ≃* CFSG.GorensteinWalter.PSL2 K :=
    e₂.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    norm_num
  letI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hL : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hZ : Subgroup.center ↥L = ⊥ := by
    have hmap := Subgroup.map_center_eq eL
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot K] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.injective).mp hmap
  have hX : L2AutFacts ↥L :=
    (l2AutFacts_psl2 (p := 7) (f := 1) (by norm_num) (by norm_num) hKcard
      (by norm_num) (by norm_num)).of_mulEquiv eL.symm
  exact inner_of_l2AutFacts_of_rep hV ρ hρ hL hZ hX hAL hA4 hA2' hquad hAC a ha

end CFSG.LocalAnalysis.WeakClosure81

end
