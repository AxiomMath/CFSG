module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup TauCeti
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

section K34oddNonLie


theorem k34odd_nonLie
    (X : Type) [Group X] [Finite X] (i : CFSGIndex) (e : X ≃* i.Group)
    (hi : ∀ d, i ≠ CFSGIndex.lie d) (hnab : ∃ a b : X, a * b ≠ b * a)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) :
    (IsAlt X 9 ∨ IsAlt X 10 ∨ IsAlt X 11) ∨ IsSpor X .J3 := by
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
    exact absurd (e.injective (by rw [map_mul, map_mul]; exact hc (e a) (e b))) hab
  | lie d => exact absurd rfl (hi d)
  | alternating n hn =>
    by_cases hn8 : n ≤ 8
    · have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) ≤ 2 :=
        CFSG.SectionRank.pRank_alternating_le_two hn8 Nat.prime_three (by norm_num)
      have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) =
          CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
      omega
    · by_cases hn12 : 12 ≤ n
      · have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
          CFSG.AGLEmbedding.le_pRank_of_mulEquiv_alternatingGroup (k := 4) e (by omega)
        omega
      · have hn9 : 9 ≤ n := by omega
        have hn11 : n ≤ 11 := by omega
        interval_cases n
        · exact Or.inl (Or.inl ⟨e⟩)
        · exact Or.inl (Or.inr (Or.inl ⟨e⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨e⟩))
  | sporadic s =>
    by_cases hs : s = .J3
    · subst hs
      obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      exact Or.inr ⟨e.trans φ.symm⟩
    · exact absurd hrk
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.sporadic_three_rank_ne_three s hs e)

end K34oddNonLie

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
