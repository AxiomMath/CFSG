module

public import CFSG.Quasithin.EmptyFaithful.S153LXfer

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.S1549C
  CFSG.Quasithin.S1549D CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153L

theorem input49I_holds (h113 : StageLemma14113) (h56 : AsB56) : S1549C.Input49I := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := Y0_le_H hb
  have hWH : W ≤ H := od.W_le.trans ((pCoreOf_le 2 _).trans (sup_le hY0H hTH))
  have hHs : StarOf T M V₁ H H = starOfSub h H := starOf_eq_starOfSub cx hb le_rfl
  have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
    have := od.off
    rwa [hHs] at this
  have hBW : B ≤ starOfSub h W := by
    have := od.B_le
    rwa [starOf_eq_starOfSub cx hb hWH] at this
  have hJ : Jgrp hb B = preStar h (conjClosure B (starOfSub h H)) := by
    unfold Jgrp
    rw [hHs]
  set A : Subgroup (MulAut (UTil T M V₁ H)) := conjClosure B (starOfSub h H) with hAdef
  have hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut (UTil T M V₁ H))) :=
    le_normalizer_conjClosure B _
  have hAH : A ≤ starOfSub h H := conjClosure_le fun g hg b hb' =>
    (starOfSub h H).mul_mem ((starOfSub h H).mul_mem hg (hoff.1 hb')) ((starOfSub h H).inv_mem hg)
  have hSQ : SQTKGroup ↥A := by
    have := sqtkGroup_starOfSub cx hb (K := preStar h A) (preStar_le h A)
    rwa [starOfSub_preStar h hAH] at this
  have hBR : B ≤ pCoreOf 2 (starOfSub h (Y0 T Mc M) ⊔ starOfSub h T) := by
    rw [← starOfSub_sup h hY0H hTH]
    exact hBW.trans ((starOfSub_mono h od.W_le).trans (starOfSub_pCoreOf_le h (sup_le hY0H hTH)))
  have hmain := ns_main (V := UTil T M V₁ H) h56 hV (starOfSub h H) A (starOfSub h (M ⊓ H))
    (starOfSub h (Y0 T Mc M)) (starOfSub h T) B hAH
    (fun g hg j hj => (Subgroup.mem_normalizer_iff.mp (hAn hg) j).mp hj)
    (pCoreOf_starOfSub_H h) hSQ (starOfSub_mono h (Y0_le_inf hb))
    (starOfSub_mono h inf_le_right) hoff (le_conjClosure B _) hBR rfl
    (fun x hx hx3 => theta_star hb hx3 hx) (Ystar_gen hb) (fun X hXH hXY => hKL_star h113 hb X hXH hXY)
    (fun E hE hE3 => hY3_star hb hE hE3)
  rw [hJ]
  refine ⟨exists_cComp_of_not_solvable (not_isSolvable_preStar h hAH hmain.1), fun L hL => ?_⟩
  obtain ⟨hn, hc⟩ := hmain.2 _ (starOfSub_mem_cComp h hAH hL)
  exact eq_commutator_of_star h hAH hAn hL hY0H hn hc

end S153L

end CFSG.Quasithin
