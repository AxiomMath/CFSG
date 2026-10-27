module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmEntry
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LocalAnalysis.StandardType.SpTwoLocalRankLower
public import CFSG.LocalAnalysis.StandardType.SpRangeEightCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.Open (StatedSp)

section Holds


theorem ggSixLSixSevenConjA3At_PSp : GGSixLSixSevenConjA3At .PSp := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  exfalso
  obtain ⟨hp3, hm⟩ := hctx.twoLocalRank_eq_four_of_a3 ggLNoncyclicInput_holds hA
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  obtain ⟨-, hf, hn2, -⟩ := hctx.2.2.2.1.1
  have hkerSp : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker
  have hZ : Subgroup.center (StatedSp n (GaloisField 2 f)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hkerSp.trans hZ.le
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  subst hp3
  have hn : n ≤ 4 ∨ (n = 5 ∧ 3 ∣ Nat.card (GaloisField 2 f) + 1) := by
    rcases three_dvd_two_pow_pred_or_succ f with h | h
    · left
      have h1 := SpRank.le_largeEvenTwoLocalRank_statedSp (F := GaloisField 2 f) hp hp2
        (by rw [hF]; exact h) (by omega) ψ hψinj
      rw [hm] at h1
      exact h1
    · by_cases h4 : n ≤ 4
      · exact Or.inl h4
      · right
        have h1 := SpRank.pred_le_largeEvenTwoLocalRank_three_statedSp (F := GaloisField 2 f)
          (by omega) ψ hψinj
        rw [hm] at h1
        exact ⟨by omega, by rw [hF]; exact h⟩
  have hcen : ¬ 3 ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G)) := by
    rw [hrange]
    exact not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub
  have hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G) :=
    fun b hb => PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hn2 ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
  have hBs := hctx.bstar
  have hBsr : Bs ≤ ψ.range := fun b hb =>
    mem_of_exists_mem_centralizer_of_not_dvd hp hcen (hBs.2.1.2 b hb) (hdiag b hb)
  have hD : D ≤ ψ.range := hctx.d_le_bstar.trans hBsr
  have hJc : IsComponentOf J (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    hctx.j_isComponentOf_inf
  have hA' : IsAlternatingEightCover ↥J := hctx.alternating_eight_quotient hA
  exact SpFixed.false_of_isSubnormal_range_inf_centralizer_eightCover hn ψ hψinj hD
    (by rw [hctx.card_d]; norm_num)
    (fun a ha b hb => TableB.IsElemAbelian.comm hBs.2.1 (hctx.d_le_bstar ha) (hctx.d_le_bstar hb))
    (fun a ha => hBs.2.1.2 a (hctx.d_le_bstar ha))
    (by
      have h := hJc.2.1
      rw [← hrange] at h
      exact h) hA'

end Holds

end CFSG.StandardType
