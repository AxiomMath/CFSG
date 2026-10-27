module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSevenThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isStronglyPEmbedded_three_of_mem_sigma (hU : uniqueFourUnique G) (S : Setup4 G)
    (h3 : 3 ∈ uniqueFourSigma S.M) : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M := by
  obtain ⟨-, hM0, -, P, -, -, hcl⟩ := (hU S.M S.maxLocal ⟨3, h3⟩).1 3 h3
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, -⟩
  · exact UC6.isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
  · omega

@[expose] def UC2_14_7BR (D : Data G) : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X B R : Subgroup G),
    Hyp8100 D L n r p A X → Case8100ThreeR D L p X →
      CFSG.ABGLocalTools.IsSylowOf r R X → B ≤ D.M → Nat.card B = p → ⁅R, B⁆ = R →
        UniqueMax D.M (B ⊔ R)

theorem uc2_14_7Three_of_BR {D : Data G} (h : UC2_14_7BR D) : UC2_14_7Three D := by
  intro L n r p A X B R hH hc3 hR _ hB hBp hRB _
  obtain ⟨hcal, -, -, -, -, -, -, -, hXset, -⟩ := id hH
  have hXM : X ≤ D.M := by
    intro x hx
    have hx' : x ∈ (L 0 : Set G) * (L 1 : Set G) := by rw [← hXset]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
    exact D.M.mul_mem ((hcal 0).1.le ha) ((hcal 1).1.le hb)
  have hRM : R ≤ D.M := hR.le.trans hXM
  have hBR := h L n r p A X B R hH hc3 hR hB hBp hRB
  refine ⟨uc22p22u_uniqueMax_mono D le_sup_left (sup_le (sup_le hB hRM) D.sylowM.le) hBR, ?_⟩
  intro S hST _ _
  exact uc22p22u_uniqueMax_mono D le_sup_left (sup_le (sup_le hB hRM) (hST.trans D.sylowM.le))
    hBR

theorem le_and_normalizer_le_of_isPGroup {M E Y : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : rankThreeIsMaxTwoLocal M) (hE : E ∈ uniqueSet M) (hEY : E ≤ Y) (hY : IsPGroup q Y) :
    Y ≤ M ∧ normalizer (Y : Set G) ≤ M := by
  have hYM := PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup hM hE hEY hY
  exact ⟨hYM, normalizer_le_of_mem_uniqueSet hM (mem_uniqueSet_of_le hE hEY hYM)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
