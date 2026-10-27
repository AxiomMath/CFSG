module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3C2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_hyp154_of_component_e3
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    (h880 : F08.R880 D) (h163c : R16_3FComp D) (hSchur : RSchur153) (hJP : K_JonesParshallH1)
    (h1217 : R1217 D) (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian)) : Hyp154 D V₀ V L := by
  by_cases hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L)
  · exact s16h_hyp154_of_component_nonthin D S h880 h163c hSchur h hs hnot hδ ht ht2 ht1 htr hW
      hcomp hnt
  · have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
        CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1 := fun q hq hq2 =>
      not_lt.1 fun hlt => hnt ⟨q, hq, hq2, hlt⟩
    rcases Nat.lt_or_ge (s15 D.M V₀ V h.hyp151.isElemAbelian L) 3 with h2 | h3
    · exact s16h_hyp154_of_component_two_e3 D S hr3 hσ h880 hJP h1217 hU2 h920L28 h hs hnot
        hδ ht ht2 ht1 htr hW hcomp hthin (by omega)
    · exact s16h_hyp154_of_component_three D S hσ h880 h163c hSchur h hs hnot hδ ht ht2 ht1 htr
        hW hcomp h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
