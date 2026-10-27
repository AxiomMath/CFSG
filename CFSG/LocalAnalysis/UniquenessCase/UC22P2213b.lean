module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
import CFSG.LocalAnalysis.UniquenessCase.UC22P22u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213b_hyp2120_134 (D : Data G) (Ch : Choice2011 G) (h12 : S22_12 D Ch)
    (h1930 : H1930 D) (hsig : D.sig.Nonempty) (c : Ctx22b D Ch) :
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M ∧
    (∀ p ∈ D.sig, ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) ∧
        P ≤ normalizer (c.B : Set G)) ∧
    (∀ p ∈ D.sig, 1 < CFSG.Open.pRank p (barPreimage D.M (centE D.M)) →
      ¬ InvertedIn D.M c.B) := by
  haveI : (CFSG.layer (Bar2 D.M)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hEn : (centE D.M).Normal := uc22p21c_normal_centralizer (CFSG.layer (Bar2 D.M))
  refine ⟨?_, fun p hp => ?_, fun p hp hrk => ?_⟩
  ·
    obtain ⟨p, hp⟩ := hsig
    haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
    have hPL := (h12 h1930 c p hp P hP).1.2.1
    rw [uc22p21c_commutator_bar_eq_bot_iff, hPL, Subgroup.commutator_comm]
    exact CFSG.LocalCores.fitting_layer_commute
  ·
    haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
    obtain ⟨g, hg, hcomm⟩ := (h12 h1930 c p hp P hP).2
    have hgX : (barPreimage D.M (centE D.M)).map (MulAut.conj g).toMonoidHom =
        barPreimage D.M (centE D.M) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (uc22p22u_barPreimage_normalizes hg)
    refine ⟨P.map (MulAut.conj g).toMonoidHom,
      CFSG.ABGLocalTools.isSylowOf_of_card ((Subgroup.map_mono hP.le).trans hgX.le) ?_,
      fun x hx => ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun b hb => ?_)
      exact hcomm b hb x hx
  ·
    exfalso
    have hpp : p.Prime := (D.sig_prime p hp).1
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
    have hcyc := (h12 h1930 c p hp P hP).1.2.2.2.2
    have := (uc22p22q_pRank_le_sylow hP).trans (CFSG.SectionRank.pRank_le_one_of_isCyclic hpp hcyc)
    omega

theorem uc22p2213b_hyp2120_iff (D : Data G) (Ch : Choice2011 G) (h12 : S22_12 D Ch)
    (h1930 : H1930 D) (hsig : D.sig.Nonempty) (c : Ctx22b D Ch) :
    Hyp2120 D c.toCtx21 ↔ ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) := by
  obtain ⟨h1, h3, h4⟩ := uc22p2213b_hyp2120_134 D Ch h12 h1930 hsig c
  exact ⟨fun h => h.2.1, fun h2 => ⟨h1, h2, h3, h4⟩⟩

theorem uc22p2213b_hyp2120_B0_iff (D : Data G) (Ch : Choice2011 G) (h12 : S22_12 D Ch)
    (h1930 : H1930 D) (hsig : D.sig.Nonempty) (c : Ctx22b D Ch) :
    Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } ↔
      ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
        ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) :=
  uc22p2213b_hyp2120_iff D Ch h12 h1930 hsig { c with B := c.B0, hB := c.hB0, hle := le_rfl }

end CFSG.LocalAnalysis.UniquenessCase.UC22
