module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCNAFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16h_hyp154_of_component_nonthin
    (D : Data G) (S : s16h_Std D)
    (h880 : F08.R880 D) (h163 : R16_3FComp D) (hSchur : RSchur153)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L)) : Hyp154 D V₀ V L := by
  obtain ⟨q, hqprime, hq2, hr⟩ := hnt
  have hV := h.hyp151.isElemAbelian
  have hσ₁ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := by
    obtain ⟨p, hp⟩ := S.hx.sig_nonempty
    exact ⟨p, hp, S.hSig.three_le p hp⟩
  by_cases hqσ : q ∈ D.sig
  · have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup q P → ¬ IsCyclic ↥P →
        P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
      intro w hwV hw0 P hPp hPc hPC
      exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 hqσ hPp hPc hwV hw0 hPC
    have hU : s16h_CondU D V₀ V L hV := s16h_condU_of_noncyclic D h hqprime hgood hr
    exact s16h_hyp154_of_condU D S.h61 h hσ₁ hU hs hδ
  · obtain ⟨hq3, hsp3⟩ :=
      s16h_nonthin_dichotomy_free D S.h127 S.h119 h880 h163 hSchur h hs ht ht2 ht1 htr hW hcomp
        hqprime hq2 hr
    subst q
    have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup 3 P → ¬ IsCyclic ↥P →
        P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
      intro w hwV hw0 P hPp hPc hPC
      exact s16h_uniqueMax_cent_of_cElt_three D S.h61 S.h63 S.h127 hsp3 h.hyp16 hPp hPc
        hwV hw0 hPC
    have hU : s16h_CondU D V₀ V L hV := s16h_condU_of_noncyclic D h hqprime hgood hr
    exact s16h_hyp154_of_condU D S.h61 h hσ₁ hU hs hδ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
