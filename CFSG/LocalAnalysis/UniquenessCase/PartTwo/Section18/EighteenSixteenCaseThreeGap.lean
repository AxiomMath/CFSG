module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeenK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem dvd_card_cTilde_of_case3 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (hs : P18_13_3 D V₀ V p L h) (hSg : UC6S846.SigmaStd D)
    (hKp : K_OmegaFourPlusNormalizer_pRank) (h638 : UC6.R6_38 D) :
    p ∣ Nat.card (F11.CTilde D.M V₀ V) := by
  classical
  by_contra hnd
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  obtain ⟨f, hO, hNat⟩ := hs
  obtain ⟨-, -, hf2, hcong⟩ := isOmegaPlus_barSub_cong h h1742 hO
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := barSub V₀ V hV (UC22.conjClosure D.M L)
  let Y : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  have hO' : IsOmegaPlus ↥H 4 f := hO
  have hNat' : NatOmegaPlus H ⊤ ⊥ 4 f := hNat
  have hHY : H ≤ Y := barSub_mono V₀ V hV h.X_le_M
  have hnormY : Y ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
    mbar_le_normalizer_conjClosure h
  have hOp : UC22.F10.OpRes p Y = Y := opRes_mbar_eq D h h638
  have h1 : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p Y :=
    pRank_le_pRank_mbar_of_not_dvd hV hP h.p_prime hnd
  have h2 : CFSG.Open.pRank p Y ≤ 2 :=
    hKp H Y p f hf2 hO' hNat' h.p_prime h.p_ne_two hcong hHY hnormY hOp
  have h3 := hSg.three_le p h.hp
  omega

theorem eighteen_sixteen_three_weak (D : Data G) (h61 : UC6.R6_1 D)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h143 : R18_14_3At D V₀ V p L h)
    (hK : K_Omega4Plus_nonsingPoint) (hSg : UC6S846.SigmaStd D)
    (hKp : K_OmegaFourPlusNormalizer_pRank) (h638 : UC6.R6_38 D) :
    R18_16_3wAt D V₀ V p L h := by
  intro hs
  exact eighteen_sixteen_three_weak_of_pCV D h61 V₀ V p L h h1742 h143 hK
    (dvd_card_cTilde_of_case3 D h h1742 hs hSg hKp h638) hs

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
