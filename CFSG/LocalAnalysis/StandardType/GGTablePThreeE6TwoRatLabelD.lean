module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
import CFSG.RankThree.PartOne.KD4T.Emb
import CFSG.RankThree.PartOne.KD4T.Inj
import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
import CFSG.RankThree.PartOne.KE6.E6LAct
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LieType.Chevalley.StandardParabolic
import CFSG.LieType.Chevalley.StandardParabolicCells
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDLeafPerm
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDStrictBase
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDStrict

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6TwoRatLabelD

open CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.RankThree.E6 CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.Yardstones.Md0ec50421ce4

private theorem e6TwoRatLabelD_pOmegaMinus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hsq : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      CFSG.Blueprint.LieModel
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        .POmegaMinus 4 (ringChar L) f := by
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (ringChar_ne_of_pow_eq_one hp hap h1)
  have hTp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  exact e6TwoRatLabelD_strict_of_rank_four S hp hpL hT hTp h1 i hshape.1 hshape.2 hout hsq

private theorem e6TwoRatLabelD_tag_eq_twD_of_markTag {lab : LargeEvenLabel}
    (h : markTag lab = .POmegaMinus) : lab.tag = .twD := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [markTag] at h <;>
    first
      | rfl
      | (split_ifs at h <;> simp_all)
      | simp_all

private theorem e6TwoRatLabelD_rank_ne_of_markTag {lab : LargeEvenLabel}
    (h : markTag lab = .POmegaMinus) : lab.rank ≠ 2 ∧ lab.rank ≠ 3 := by
  have htag := e6TwoRatLabelD_tag_eq_twD_of_markTag h
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  simp only [markTag] at h
  have h2 : ¬ rank = 2 := by
    intro hr
    rw [if_pos hr] at h
    exact absurd h (by decide)
  have h3 : ¬ rank = 3 := by
    rw [if_neg h2] at h
    intro hr
    rw [if_pos hr] at h
    exact absurd h (by decide)
  exact ⟨h2, h3⟩

private theorem e6TwoRatLabelD_markRank_eq_self_of_markTag {lab : LargeEvenLabel}
    (htag : lab.tag = .twD) (hm : markTag lab = .POmegaMinus) : markRank lab = lab.rank := by
  obtain ⟨h2, h3⟩ := e6TwoRatLabelD_rank_ne_of_markTag hm
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  simp only [markRank]
  rw [if_neg h2, if_neg h3]

private theorem e6TwoRatLabelD_markDeg_eq_n_of_markTag {lab : LargeEvenLabel}
    (htag : lab.tag = .twD) (h2 : lab.rank ≠ 2) : markDeg lab = lab.n := by
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  simp only [markDeg]
  rw [if_neg h2]

private theorem e6TwoRatLabelD_label
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) {f : ℕ}
    (hm : CFSG.Blueprint.LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaMinus 4 2 f) :
    ∃ lab : LargeEvenLabel, lab.n = f ∧ lab.tag = .twD ∧ lab.rank = 4 ∧
      RationalLabelIs S i lab := by
  have hQS' : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open hQS
  have hZ := CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot hQS'
  obtain ⟨lab, hlab, htag, hrank, hchar, hdeg, hraw⟩ :=
    CFSG.StandardType.exists_label_rawDatum_of_lieModel hZ hm
  have htag' : lab.tag = .twD := e6TwoRatLabelD_tag_eq_twD_of_markTag htag
  obtain ⟨h2, -⟩ := e6TwoRatLabelD_rank_ne_of_markTag htag
  have hrank' : lab.rank = 4 := by
    rw [← e6TwoRatLabelD_markRank_eq_self_of_markTag htag' htag, hrank]
  have hn' : lab.n = f := by
    rw [← e6TwoRatLabelD_markDeg_eq_n_of_markTag htag' h2, hdeg]
  exact ⟨lab, hn', htag', hrank', hlab, hraw⟩

end E6TwoRatLabelD

theorem rationalLabel_outerD_four_sq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧ (componentRoots (rootCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hsq : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      lab.tag = .twD ∧ lab.rank = 4 ∧ RationalLabelIs S i lab := by
  obtain ⟨f, hf, hm⟩ := e6TwoRatLabelD_pOmegaMinus S hp hT hap h1 i hshape hout hsq
  have hm2 : CFSG.Blueprint.LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaMinus 4 2 f := by
    rw [← ringChar.eq L 2]
    exact hm
  obtain ⟨lab, hn, htag, hrank, hrat⟩ := e6TwoRatLabelD_label S i hQS hm2
  refine ⟨lab, ?_, htag, hrank, hrat⟩
  rw [hn]
  rw [← ringChar.eq L 2]
  exact hf

end CFSG.StandardType.TablePThreeKG

end
