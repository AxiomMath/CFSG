module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ClassicalE2Sp

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open CFSG.RankThree.PartTwo.Sec13.KF135Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Fam7Classical (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (X ≃* projSL 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 4 2 n))

theorem kF135At_fam7Classical : KF135At Fam7Classical := by
  intro S _ _ p P x u V hF h
  exfalso
  obtain ⟨n, hn, hF⟩ := hF
  rcases hF with hF | hF | hF | hF | hF <;> obtain ⟨e⟩ := hF
  · exact false_of_kF135Hyp_projSL_two hn e h
  · exact false_of_kF135Hyp_projSL_three hn e h
  · exact false_of_kF135Hyp_projSU_three hn e h
  · exact false_of_kF135Hyp_projSp_two hn e h
  · exact false_of_kF135Hyp_projSU_four hn e h

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
