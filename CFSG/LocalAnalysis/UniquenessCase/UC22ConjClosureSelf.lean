module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_conjClosure_eq {N A : Subgroup G} {r : ℕ} (hr : r.Prime) (hAN : A ≤ N)
    (hA : Nat.card A = r) (hrk : CFSG.Open.pRank r N ≤ 1) :
    conjClosure (conjClosure N A) A = conjClosure N A := by
  have : Fact r.Prime := ⟨hr⟩
  refine le_antisymm ?_ ?_
  · have hHH : conjClosure N A ≤ normalizer (conjClosure N A : Set G) :=
      Subgroup.le_normalizer
    exact uc22p22v_conjClosure_le hHH (uc22p22v_le_conjClosure N A)
  · have hNN : N ≤ normalizer (N : Set G) := Subgroup.le_normalizer
    have hHN : conjClosure N A ≤ N := uc22p22v_conjClosure_le hNN hAN
    have hrkH : CFSG.Open.pRank r (conjClosure N A) ≤ 1 :=
      (CFSG.RankThreeEvenClassification.Helpers.pRank_mono r hr hHN).trans hrk
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    have hAH : A ≤ conjClosure N A := uc22p22v_le_conjClosure N A
    have hBH : A.map (MulAut.conj g).toMonoidHom ≤ conjClosure N A := by
      have hgN : (conjClosure N A).map (MulAut.conj g).toMonoidHom = conjClosure N A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (uc22p22v_le_normalizer_conjClosure N A hg)
      calc A.map (MulAut.conj g).toMonoidHom
          ≤ (conjClosure N A).map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAH
        _ = conjClosure N A := hgN
    have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = r := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
    obtain ⟨h, hhH, hEq⟩ :=
      CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime hrkH hAH hBH hA hcard
    rw [← hEq]
    exact le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf (conjClosure N A) A) => K) _
      ⟨h, hhH, rfl⟩ le_rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
