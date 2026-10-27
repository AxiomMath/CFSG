module

public import CFSG.RankThree.PartOne.KEXC.OddCenterCover
public import CFSG.RankThree.PartOne.S11d.FieldFFTwo
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticOrthogonalCoverOddKernel
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCover
public import CFSG.LieType.Chevalley.TwistedE6EvenCover
public import CFSG.RankThree.SteinbergR3EExceptionalCoverKernelOdd

public section

namespace CFSG.RankThree.PartOne.KEXC

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.FieldFix


theorem oddCenterLie_holds : OddCenterLie := by
  intro J _ _ hq t n m hm5 hmodel
  have : Group.IsPerfect J := hq.1
  have hadm : StatedLieAdmissible t n 2 m := statedLieAdmissible_of_lieModel hmodel
  let η : J →* J ⧸ center J := QuotientGroup.mk' (center J)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hker : η.ker = center J := QuotientGroup.ker_mk' _
  suffices hodd : Odd (Nat.card η.ker) by
    rw [hker] at hodd
    exact fun h2 => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rcases hmodel with ⟨htc, hcm⟩ | ⟨hn0, htc, hM⟩ | ⟨hn0, htc, hM⟩ | ⟨hn0, htc, hM⟩
  ·
    have htags : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
        t = .POmegaMinus := by simpa [classicalTags] using htc
    have hL : LieModel (J ⧸ center J) t n 2 m := Or.inl ⟨htc, hcm⟩
    rcases htags with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      rcases (show n = 2 ∨ 3 ≤ n by have := hadm.2.2.1; omega) with rfl | hn3
      · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
        exact (even_linear_unitary_rank_one_catalog_central_two_cover_trivial θ hθ h2 hθC
          (Or.inl ⟨m, by omega, hL⟩)).1
      · exact even_higher_linear_unitary_perfect_central_kernel_odd_off_five_boundaries η hη
          hker.le (Or.inl rfl) hn3 (by omega) hcm (by simp; omega)
    ·
      rcases (show n = 3 ∨ 4 ≤ n by have := hadm.2.2.1; omega) with rfl | hn4
      · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
        exact (even_linear_unitary_rank_one_catalog_central_two_cover_trivial θ hθ h2 hθC
          (Or.inr ⟨m, by omega, hL⟩)).1
      · exact even_higher_linear_unitary_perfect_central_kernel_odd_off_five_boundaries η hη
          hker.le (Or.inr rfl) (by omega) (by omega) hcm (by simp; omega)
    · exact even_symplectic_orthogonal_perfect_central_kernel_odd_off_two_boundaries η hη hker.le
        (Or.inl rfl) hcm (by simp; omega)
    · exact absurd rfl hadm.2.2.2
    · exact even_symplectic_orthogonal_perfect_central_kernel_odd_off_two_boundaries η hη hker.le
        (Or.inr (Or.inl rfl)) hcm (by simp; omega)
    · exact even_symplectic_orthogonal_perfect_central_kernel_odd_off_two_boundaries η hη hker.le
        (Or.inr (Or.inr rfl)) hcm (by intro h; simp at h)
  ·
    subst hn0
    have hL : LieModel (J ⧸ center J) t 0 2 m := Or.inr (Or.inl ⟨rfl, htc, hM⟩)
    have htags : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
        t = .trialityD4 := by simpa [chevalleyExceptionalTags] using htc
    rcases htags with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact CFSG.RankThree.even_G2_large_field_perfect_central_kernel_odd η hη hker.le
        (by omega) hM
    · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
      exact (CFSG.LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
        θ hθ hθC h2 (by omega) (Or.inl rfl) hL).1
    · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
      exact (CFSG.LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
        θ hθ hθC h2 (by omega) (Or.inr (Or.inl rfl)) hL).1
    · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
      exact (CFSG.LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
        θ hθ hθC h2 (by omega) (Or.inr (Or.inr (Or.inl rfl))) hL).1
    · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
      exact (CFSG.LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
        θ hθ hθC h2 (by omega) (Or.inr (Or.inr (Or.inr rfl))) hL).1
    · refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
      exact (CFSG.LieType.Chevalley.twisted_E6_nonprime_even_field_central_two_cover_trivial
        θ hθ hθC h2 (by omega) hL).1
    · exact CFSG.RankThree.nonprime_even_triality_perfect_central_kernel_odd η hη hker.le
        (by omega) hM
  ·
    subst hn0
    have hL : LieModel (J ⧸ center J) t 0 2 m := Or.inr (Or.inr (Or.inl ⟨rfl, htc, hM⟩))
    have htags : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      simpa [reeTitsTags] using htc
    rcases htags with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · have h := odd_center_of_suzuki_ree_model hm5 (Or.inr rfl) hL
      rwa [← hker] at h
    · have := hadm.2.2.2.2
      omega
  ·
    subst hn0 htc
    have h := odd_center_of_suzuki_ree_model hm5 (Or.inl rfl)
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hM⟩)))
    rwa [← hker] at h

end CFSG.RankThree.PartOne.KEXC
