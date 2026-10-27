module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Psl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem inspL2_holds : InspL2 := by
  intro G _ _ p f hp2 hL _ D hD
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hKc : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    have h2 : (2 : K) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : K) = 0 := by simpa using h
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
    let e' : G ≃* PSL(2, K) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    exact inspL2Core_of_mulEquiv e' (fun D' hD' => psl_exists_klein h2 D' hD') D hD
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK
