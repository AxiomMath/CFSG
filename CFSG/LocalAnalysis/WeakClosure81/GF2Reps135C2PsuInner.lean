module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCover
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuCover
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabel
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuArith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuNatural
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuFour
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psu_inner
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htL : t ∈ L) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) : W4Lem13_5Concl W Y L t := by
  classical
  have htY : t ∈ Y := hctx.2.2.1 htL
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  have hQ : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hIrr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨hn3, hf1, hq, K, _, _, _, hKcard, φ, hφs, hker, hodd⟩ :=
    w135c2_psu_cover hW hQ hIrr hlie
  by_cases hn4 : n = 4
  · subst hn4
    exact w135c2_psu_four_inner hW hctx htL ht2 hm hlie
  have hirr := w135c2_psl_rep_irreducible hIrr φ hφs
  have hne := w135c2_psl_rep_ne_one hQ φ hφs
  have htLord : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨y, hy2, hy1, hyt⟩ := w135c2_exists_involution_lift φ hodd htLord
    (MonoidHom.mem_range.mpr (hφs _))
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (pslRep φ y - 1)) ≤ 3 := by
    rw [w135c2_psl_finrank_range, hyt]
    exact hm
  obtain ⟨s, ε, hs1, h0, hact, hper, hns, hrk, ⟨k, _, _, hcard⟩, hdesc⟩ :=
    w135c2_psu_label hn3 hKcard (pslRep φ) hirr hne
  have hmv : s * movedTop (by omega : 2 ≤ n) ε ≤ 6 := by
    have := hrk y hy2 hy1
    omega
  have hnf : ¬ (n = 3 ∧ f = 1) := by
    rintro ⟨h3, h1⟩
    exact hq (by rw [h3, h1]; rfl)
  rcases w135c2_psu_classify_three hn3 hnf hs1 ε h0 hact hper hns hmv with
    ⟨r₀, j, hone, hεj, hj, hf1'⟩ | ⟨hn4', -⟩
  · obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj hj
    subst hf1'
    exact w135c2_natural hctx htY ht2 hW (w135c2_psu_natural_chev2 hKcard φ hφs β hβ)
  · exact absurd hn4' hn4

end CFSG.LocalAnalysis.WeakClosure81
