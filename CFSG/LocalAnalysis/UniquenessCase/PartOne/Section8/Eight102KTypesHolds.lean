module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU5
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec21.U4Lines (nonempty_projSU_mulEquiv_SU card_galoisField_two_mul
  card_rootsOfUnity_three unitaryInvolution_rootsOfUnity)

theorem kU45Types_holds : KU45Types := by
  intro X _ _ n hX p hp hpn S hS hSi
  suffices h : KTypes.KTypesAt X ⊤ p n by
    obtain ⟨ha, hb, hc, hd, he⟩ := h S le_top hS (by rwa [relIndex_top_right])
    exact ⟨ha, hb, hc, hd, fun B₁ B₂ h₁ h₂ => (he B₁ B₂ h₁ h₂).imp fun _ hx => hx.2⟩
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hU5 (by decide))
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        (CFSG.Blueprint.LieModel.admissible hU5) (MulEquiv.refl _))
    obtain rfl : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (by simpa using hpn)
    have hK := card_galoisField_two_mul 2 (by norm_num)
    have : Nontrivial (rootsOfUnity 3 (GaloisField 2 (2 * 2))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [card_rootsOfUnity_three even_two hK]; norm_num)
    obtain ⟨u, hu⟩ := exists_ne (1 : rootsOfUnity 3 (GaloisField 2 (2 * 2)))
    exact (KTypes.u5_kTypesAt hK (unitaryInvolution_rootsOfUnity even_two u)
      (fun h => hu (Subtype.ext h)) ((mem_rootsOfUnity 3 _).mp u.2)).of_mapL
      (topEquiv.trans ((e.trans (CFSG.PGLModel.projSUEquivStatedProj 5 2 2)).trans topEquiv.symm))
  · have hn0 : 0 < n := (CFSG.Blueprint.LieModel.admissible hU4).2.1
    obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hU4 (by decide))
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        (CFSG.Blueprint.LieModel.admissible hU4) (MulEquiv.refl _))
    obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU n hn0
    have hF := card_galoisField_two_mul n hn0
    have : Nontrivial (rootsOfUnity 3 (GaloisField 2 (2 * n))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [card_rootsOfUnity_three hn hF]; norm_num)
    obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 (GaloisField 2 (2 * n)))
    exact (KTypes.u4_kTypesAt hn0 hn hF hω hp hpn).of_mapL (topEquiv.trans (e.trans e₀))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
