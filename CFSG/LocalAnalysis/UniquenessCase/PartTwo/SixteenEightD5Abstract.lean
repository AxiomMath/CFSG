module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Conc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Extract
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5NonComm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16e_d5_abstract {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hconc : Conc4_136W A t L) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hind : IsIndivisible A)
    (hsyl : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 ≤ CFSG.Open.pRank p A) :
    ∃ K : Subgroup (MulAut W), Conc4_136W A t K ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} =
        4 := by
  have hrk6 := s16e_d5_extract hL hrk hconc
  have hrk8 : rk ↥(⊤ : Subgroup W) = 8 := by rwa [hWL] at hrk
  obtain ⟨K, Z, hfr⟩ := s16e_d5_blocks hW hL hWL hrk8 hrk6
  have hLA : L ≤ A := hconc.le
  have htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j := fun i j => hfr.trans hLn hind i j
  obtain ⟨p, hp, hp2, h3⟩ := hsyl
  obtain ⟨-, h27⟩ := s16e_d5_sylow hfr hLA hLn hp hp2 h3
  obtain ⟨a, hfam⟩ := s16e_d5_family hfr hLA hLn htr h27
  obtain ⟨i, hi⟩ := s16e_d5_noncomm hfr hfam ht2 ht1
  exact ⟨Subgroup.zpowers (a i), s16e_d5_conc hfr hLn htr hfam i hi,
    s16e_d5_conj_card hfr hLn htr hfam i⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
