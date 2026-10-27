module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem not_isSolvable_M (S : SliceCore D L D₃ Y H) : ¬ Group.IsSolvable ↥D.M :=
  UC6S846.not_solvable_of_mem_calC S.L_mem

theorem isStronglyPEmbedded_of_mem_sig (hSg : UC6S846.SigmaStd D) (S : SliceCore D L D₃ Y H) {p : ℕ}
    (hp : p ∈ D.sig) : IsStronglyPEmbedded p D.M :=
  UC6S846.sp_of_mem_sig hSg S.not_isSolvable_M hp

theorem three_not_mem_sig (hSg : UC6S846.SigmaStd D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) : 3 ∉ D.sig :=
  fun h => hnsp (S.isStronglyPEmbedded_of_mem_sig hSg h)

theorem sig_prime_ne_three (hSg : UC6S846.SigmaStd D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {p : ℕ} (hp : p ∈ D.sig) :
    p.Prime ∧ p ≠ 2 ∧ p ≠ 3 :=
  ⟨(D.sig_prime p hp).1, (D.sig_prime p hp).2, fun h => S.three_not_mem_sig hSg hnsp (h ▸ hp)⟩

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
