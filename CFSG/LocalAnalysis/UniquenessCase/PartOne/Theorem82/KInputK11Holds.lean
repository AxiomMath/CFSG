module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupL2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.BenderSuzuki.MatrixGroups

theorem k11_holds :
    K11 := by
  intro X _ _ _ hcyc hX A W hA hNW hW
  rcases hX with ⟨p, f, hL⟩ | hJ
  · have hmodel : CFSG.Open.StatedClassicalModel X .PSL 2 p f := by
      rcases hL with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h
      all_goals omega
    obtain ⟨hadm, K, instK, instFinK, hKcard, ⟨eX⟩⟩ := hmodel
    haveI : Fact p.Prime := ⟨hadm.1⟩
    letI : Field K := instK
    letI : Finite K := instFinK
    have eK : X ≃* PSL2MatrixGroup K :=
      eX.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have hp3 : p ≠ 3 := by
      rintro rfl
      obtain ⟨-, hf, -, -, hne⟩ := hadm
      have hf2 : 2 ≤ f := by
        by_contra h
        have hf1 : f = 1 := by omega
        exact hne (by rw [hf1]; norm_num)
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨H, hHcard, hHel⟩ :=
        CFSG.Glauberman.Dickson.exists_elementaryAbelian_subgroup (F := K) (p := 3) (f := f)
          hKcard (m := 2) (by omega)
      let HX : Subgroup X := H.map eK.symm.toMonoidHom
      haveI : IsElementaryAbelian 3 H := hHel
      have hHXel : IsElementaryAbelian 3 HX :=
        IsElementaryAbelian.map (A := H) eK.symm.toMonoidHom
      have hHXcard : Nat.card HX = 3 ^ 2 := by
        change Nat.card (H.map eK.symm.toMonoidHom) = 3 ^ 2
        rw [Subgroup.card_map_of_injective eK.symm.injective, hHcard]
      haveI : IsElementaryAbelian 3 HX := hHXel
      have hHXp : IsPGroup 3 HX := IsElementaryAbelian.isPGroup 3 ↥HX
      exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (A := ↥HX) (p := 3)
        hHXcard) (hcyc HX hHXp)
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv eK
      (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 hKcard hp3)
      hcyc A W hA hNW hW
  · obtain ⟨eX⟩ := hJ
    have eJ : X ≃* CFSG.Sporadic.J1.J := eX.trans CFSG.Sporadic.J1.nativeEquiv
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv eJ
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.overgroupEqTop_J hcyc A W hA hNW hW

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
