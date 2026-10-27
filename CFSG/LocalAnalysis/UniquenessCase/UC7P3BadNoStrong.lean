module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadMembers
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open scoped commutatorElement
open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus gammaCore)

theorem four_le_pRank_of_coverHasLargeTwoLocal {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a) (h : CoverHasLargeTwoLocal L) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have hperf : Group.IsPerfect L := by
    refine Group.isPerfect_def.2 ?_
    rcases hs.eq_bot_or_eq_top_of_normal (commutator L) with h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator L :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    · exact h1
  obtain ⟨U, -, -, hU⟩ := h L hperf (MonoidHom.id L) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [MonoidHom.ker_id]; simp)
  exact hU.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

@[expose] def BadIdentOutput (p : ℕ) (L : Type) [Group L] : Prop :=
  IsSmallStrongP p L ∨
    (∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
        (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨ IsReeGTwoIndex p d) ∧
      Nonempty (L ≃* CatGroup d)) ∨
    (p = 5 ∧ IsoLie L (.suzuki 2))

@[expose] def BadIdentification : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        BadIdentOutput p ↥(CFSG.generalizedFitting X)

theorem badNoStrongThree_of_kfacts (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hUO : KFactUnitaryOrder) (hRO : KFactReeOrder) (hOrd : BadListOrders)
    (hAdapt : BadIdentification) : BadNoStrongThree := by
  intro p hp hp5 X _ _ hX hO hrk N hN hKD R
  by_contra hne
  have hlt := lt_top_iff_ne_top.2 hne
  obtain ⟨hs, hnab, -, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  have h4 := four_le_pRank_of_coverHasLargeTwoLocal hs hnab hKD
  have hH := threeHeavy_of_gls3 hG3 hUO hRO (hX.subgroup _) hs hnab R h4 hlt
  rcases hAdapt p hp hp5 X hX hO hrk N hN with h | h | ⟨-, hsz⟩
  · exact false_of_isSmallStrongP hOrd hUO hp hp5 hs hnab R hlt h4 hH h
  · exact false_of_oneLieIdent hUO hp hp5 h4 hH h
  · exact false_of_suzuki hOrd hsz hH

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
