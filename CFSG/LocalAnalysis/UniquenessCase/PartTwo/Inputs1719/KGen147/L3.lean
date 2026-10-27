module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Pair
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.L3Gen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.L3Normal
import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.LieType.SeitzGeneration CFSG.Open
open scoped MatrixGroups

theorem kGenSpans_of_sl3 {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2)
    (h7F : ¬ 7 ∣ Nat.card F) {B R : Subgroup SL(3, F)} (hBR : IsKGenPair B R) :
    KGenSpans B R := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases h7 : 7 ∣ Nat.card F - 1
  · obtain ⟨g, hBg, hRg⟩ := exists_conj_eq_zpowers_shiftSL hq h7 hBR
    refine KGenSpans.of_map (MulAut.conj g) ?_
    intro H hBH hYH
    have hq5 : 5 ≤ Nat.card F := by
      have h1 := Finite.one_lt_card (α := F)
      omega
    have hR7 : IsPGroup 7 (R.map (MulAut.conj g).toMonoidHom) :=
      (hBR.map (MulAut.conj g)).2.1.isPGroup
    refine eq_top_of_diagSL_mem_of_centralizer_le hq hq5 (fun a b d h => ?_) ?_
    · exact hYH _ le_rfl hR7 (Subgroup.centralizer_le_normalizer _ (hRg a b d h))
    · have hcz : centralizer ({shiftSL} : Set SL(3, F)) ≤
          normalizer ((zpowers shiftSL : Subgroup SL(3, F)) : Set SL(3, F)) := by
        rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer _
      rw [← hBg] at hcz
      exact hcz.trans hBH
  · exfalso
    have hcyc : IsCyclic (R.map (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F)) :=
      CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_GL_three h7F h7
        (hBR.2.1.isPGroup.map _)
    let eR := R.equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective
    have hRc : IsCyclic R := isCyclic_of_surjective eR.symm.toMonoidHom eR.symm.surjective
    exact CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hBR.2.1
      (by rw [hBR.2.2.1]; norm_num) hRc

theorem kGenSpans_of_lieModel_psl3 {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hq : p ^ f % 3 = 2) (h : CFSG.Blueprint.LieModel K .PSL 3 p f) {B R : Subgroup K}
    (hBR : IsKGenPair B R) : KGenSpans B R := by
  obtain ⟨hp, hf, -⟩ := h.admissible
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 3 p f
    (h.statedClassicalModel_of_ne_zero three_ne_zero)
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hqF : Nat.card (GaloisField p f) % 3 = 2 := hF ▸ hq
  let e' := e.trans (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.pslEquivSL3 hqF)
  refine KGenSpans.of_map e' (kGenSpans_of_sl3 hqF ?_ (hBR.map e'))
  rw [hF]
  intro h7
  have hp7 : p = 7 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7)).symm
  subst hp7
  have h71 : 7 ^ f % 3 = 1 := by simp [Nat.pow_mod]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
