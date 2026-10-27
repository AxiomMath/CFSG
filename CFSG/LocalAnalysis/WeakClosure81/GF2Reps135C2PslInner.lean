module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCover
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLabel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslArith
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslNatural
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslFive
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslAdjoint
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOrthSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslTwoSmall
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimAdjoint
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimSingle
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2MainA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psl_inner
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htL : t ∈ L)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) : W4Lem13_5Concl W Y L t := by
  classical
  have htY : t ∈ Y := hctx.2.2.1 htL
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  have hQ : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hIrr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨hn2, K, _, _, _, hKcard, φ, hφs, hker, hodd⟩ := w135c2_psl_cover hW hQ hIrr hlie
  have hirr := w135c2_psl_rep_irreducible hIrr φ hφs
  have hne := w135c2_psl_rep_ne_one hQ φ hφs
  have htLord : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨y, hy2, hy1, hyt⟩ := w135c2_exists_involution_lift φ hodd htLord
    (MonoidHom.mem_range.mpr (hφs _))
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (pslRep φ y - 1)) ≤ 3 := by
    rw [w135c2_psl_finrank_range, hyt]
    exact hm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, ε, hs1, h0, hact, hper, hrk, ⟨k, _, _, hcard⟩, hdesc⟩ :=
    w135c2_psl_label (m := m) (f := f) (by omega) hKcard (pslRep φ) hirr hne
  have hmv : s * movedTop (by omega : 2 ≤ m + 1) ε ≤ 6 := by
    have := hrk y hy2 hy1
    omega
  have hcardW : Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
  rcases w135c2_psl_classify_three (by omega : 2 ≤ m + 1) hs1 ε h0 hact hper hmv with
    ⟨r₀, j, hone, hεj, hj⟩ | ⟨hn4, hf1, hs1', j, hj, hεall⟩ | ⟨hn5, hf1, hs1', j, hj, hεall⟩ |
    ⟨hn3, hf1, hs1', a, b, ha, hb, hεall⟩ | ⟨hn2', hf2, hs1', j, hj, hεall⟩
  · obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj
    exact w135c2_natural hctx htY ht2 hW
      (w135c2_psl_natural hn2 hKcard φ hφs hker hj β hβ)
  · have hm3 : m = 3 := by omega
    subst hm3
    subst hf1
    obtain ⟨β, hβ⟩ := hdesc 0 j (fun r hr => absurd (Subsingleton.elim r 0) hr) (hεall 0)
    exact w135c2_natural hctx htY ht2 hW (w135c2_psl_orth_six hKcard φ hφs hker hj β hβ)
  · have hm4 : m = 4 := by omega
    subst hm4
    subst hf1
    obtain ⟨β, hβ⟩ := hdesc 0 j (fun r hr => absurd (Subsingleton.elim r 0) hr) (hεall 0)
    exact w135c2_concl_of_item3
      (w135c2_psl_five (by simpa using hKcard) φ hφs hker hj β hβ)
  · have hm2 : m = 2 := by omega
    subst hm2
    subst hf1
    have hdim := w135c2_finrank_bModel_adjoint_three (k := k) ε a b ha hb hεall
    rw [hdim, hs1', one_mul] at hcard
    exact w135c2_concl_of_item3
      (w135c2_psl_adjoint (by simpa using hKcard) φ hφs hker (hcardW.trans hcard))
  · have hm1 : m = 1 := by omega
    subst hm1
    subst hf2
    have hdim := w135c2_finrank_bModel_of_card_le_one (k := k) ε
      (fun r => by rw [hεall r]; simp)
    have hprod : ∏ r : Fin 2, ∏ i ∈ ε r, (1 + 1).choose (i : ℕ) = 2 ^ 2 := by
      simp only [hεall, Finset.prod_singleton]
      have hj1 : (j : ℕ) = 1 := hj
      rw [hj1]
      simp
    rw [hdim, hprod, hs1'] at hcard
    have hlt : Nat.card W < 2 ^ (4 * 2) := by
      rw [hcardW, hcard]
      norm_num
    rcases w135c2_psl_two_small (by norm_num) hKcard φ hφs hker hirr hne hlt with
      hnat | ⟨l, hl, -⟩
    · exact w135c2_natural hctx htY ht2 hW hnat
    · omega

end CFSG.LocalAnalysis.WeakClosure81
