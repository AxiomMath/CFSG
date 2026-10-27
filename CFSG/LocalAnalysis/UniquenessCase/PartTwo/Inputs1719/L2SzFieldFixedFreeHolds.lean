module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzFieldKFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.RankThree.PartOne.S11c.Sec66Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint (LieModel)

theorem k_L2SzFieldFixedFree_holds : K_L2SzFieldFixedFree := by
  intro Y _ _ p r α hshape hord hαinn y hy
  rcases hshape with ⟨rfl, rfl, hL2⟩ | ⟨rfl, rfl, hSz⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
    obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (K := Y)
      (F := GaloisField 2 3) 2 2 3 (by norm_num) hF hL2
    have hαinn' : α ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut Y := by
      simpa only [CFSG.HardMathSupport.Solomon.LocalBalance.innerAut,
        CFSG.ComponentClassification.OuterAutomorphisms.inner] using hαinn
    have hfix := (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196.l2Eight_outer_fixSubgroup
      (F := GaloisField 2 3) hF e hord hαinn').1
    intro hαy
    have hmem : y ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := hαy
    have hdvd : 7 ∣ 6 := by
      have h1 := orderOf_dvd_natCard
        (⟨y, hmem⟩ : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α)
      rwa [Subgroup.orderOf_mk, hy, hfix] at h1
    norm_num at hdvd
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hSuz⟩ := CFSG.Blueprint.LieModel.suzukiModel hSz
    obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hSuz
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
    have hαinn' : α ∉ CFSG.RankThree.PartOne.Sec66T.innerAut Y := by
      simpa only [CFSG.RankThree.PartOne.Sec66T.innerAut,
        CFSG.ComponentClassification.OuterAutomorphisms.inner] using hαinn
    have hfix := CFSG.RankThree.PartOne.Sec66T.sz_card_fixSub_twenty
      (a := a) (K := K) ha hK e Nat.prime_five (by norm_num) hfa hord hαinn'
    intro hαy
    have hmem : y ∈ CFSG.RankThree.PartOne.Sec66T.fixSub α := hαy
    have hdvd : 31 ∣ 20 := by
      have h1 := orderOf_dvd_natCard
        (⟨y, hmem⟩ : CFSG.RankThree.PartOne.Sec66T.fixSub α)
      rwa [Subgroup.orderOf_mk, hy, hfix] at h1
    norm_num at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
