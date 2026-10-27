module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeEven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeLin
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem kf7_reeType_one_recognition :
    KF7ReeTypeOneRecognition := by
  intro X _ _ hO L N hLN hKL hshape hN
  obtain ⟨hKs, hKnab, hKn, hKC, -⟩ :=
    kf7_setup (p := 3) (by norm_num) (by norm_num) hO hLN hKL hN
  haveI : IsSimpleGroup ↥(genFittingFStar X) := hKs
  haveI : (genFittingFStar X).Normal := hKn
  have hL8 : ∀ S : Sylow 2 ↥L, Nat.card (S : Subgroup ↥L) = 8 :=
    fun S => card_sylow_two_of_isReeType_one hshape S
  have hLab : ∀ S : Sylow 2 ↥L, IsMulCommutative (S : Subgroup ↥L) := hshape.2.1
  let S : Sylow 2 ↥(genFittingFStar X) := Sylow.nonempty.some
  have hScomm : IsMulCommutative (S : Subgroup ↥(genFittingFStar X)) :=
    isMulCommutative_sylow_two_of_le hKL hLab S
  obtain ⟨t, ht, F, hField, hFintype, hFcard, ⟨eC⟩⟩ := hshape.2.2
  letI : Field F := hField
  letI : Fintype F := hFintype
  have hF : Fintype.card F = 3 := by simpa using hFcard
  have hC24 : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥L)) = 24 :=
    card_centralizer_of_isReeType_one hshape ht F hF eC
  rcases CFSG.Quasithin.H13.S3320.walter_split ↥(genFittingFStar X) hKnab S hScomm with
    ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hfpos, h5, h8, ⟨e⟩⟩ |
      ⟨f, hfodd, hf3, hRee⟩ | ⟨eJ⟩
  · exact reeEven_case hKL hKn hKnab hKC hLab hL8 hf e
  · have hp2 : p ≠ 2 := by
      rcases hpodd with ⟨k, hk⟩
      omega
    exact (centralizer_reeLin_false hKL hKn hKC hL8 hLab ht hC24 hp2 hfpos h5 h8 e).elim
  · obtain ⟨a, rfl⟩ := hfodd
    have ha1 : 1 ≤ a := by omega
    exact (ree_case_false (a := a) (ha := ha1) hKL hKn hKC ht hC24 hRee).elim
  · obtain ⟨eJ'⟩ := eJ
    exact (j1_case_false hKL hKn hKC ht hC24 eJ').elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
