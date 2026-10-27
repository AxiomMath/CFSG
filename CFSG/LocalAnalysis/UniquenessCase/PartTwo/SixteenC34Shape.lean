module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c34_conc4_136W_odd {W : Type} [CommGroup W] {A : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (h : Conc4_136W A t L) (hodd : Odd (Nat.card ↥L))
    (hdvd : Nat.card ↥L ∣ 168) (hrk : rk ↥(commSub ⊤ L) ≤ 3) :
    (IsCyclicOrd ↥L 3 ∧ rk ↥(commSub ⊤ L) = 2) ∨
      (IsCyclicOrd ↥L 7 ∧ rk ↥(commSub ⊤ L) = 3) := by
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at hdvd
    exact absurd (zero_dvd_iff.1 hdvd) (by norm_num))
  obtain ⟨-, -, h3⟩ := h
  rcases h3 with h133 | ⟨K, hK, g, -, -, hKL, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p, -, -, -, -, hshape⟩ := h133
    rcases hshape with ⟨hc, hr⟩ | ⟨hc, hr⟩ | ⟨hP, hr⟩ | ⟨hE, hr, -⟩ | ⟨hc, hr⟩ |
      ⟨r, m, hpm, hr2, hE, hrk', -⟩ | ⟨hE, hr, -⟩
    · exact Or.inl ⟨hc, by omega⟩
    · omega
    · omega
    · omega
    · exact Or.inr ⟨hc, by omega⟩
    · rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    · omega
  · have hKle : K ≤ L := hKL ▸ le_sup_left
    have hdK : Nat.card ↥K ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hKle
    haveI : Finite ↥K :=
      Finite.of_injective (Subgroup.inclusion hKle) (Subgroup.inclusion_injective hKle)
    exact (s16c34_not_quasisimple_of_odd_card_dvd_168 hK.2.2 (hdK.trans hdvd)
      (Odd.of_dvd_nat hodd hdK)).elim
  · exact (s16c34_not_quasisimple_of_odd_card_dvd_168 hcomp.2.2 hdvd hodd).elim
  · exact (s16c34_not_quasisimple_of_odd_card_dvd_168 hcomp.2.2 hdvd hodd).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
