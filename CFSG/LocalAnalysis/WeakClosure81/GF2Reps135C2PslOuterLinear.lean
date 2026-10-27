module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterRange
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterPeriod
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterEight
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterFinish
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_psl_outer_linear
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hRows : Chev135Rows)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (htL : t ∉ L)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hn41 : ¬ (n = 4 ∧ f = 1)) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f)
    {k d r : ℕ} (hk : Nat.card (LEnd L) = 2 ^ k) (hrk : rk W = k * d)
    (hr : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = k * r) (hr1 : 1 ≤ r) :
    W4Lem13_5Concl W Y L t := by
  classical
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
  obtain ⟨y, hyL, hy1, hy2, hyd⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  have hyord : orderOf (⟨y, hyL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨yy, hyy2, hyy1, hphiyy⟩ := w135c2_exists_involution_lift φ hodd hyord
    (MonoidHom.mem_range.mpr (hφs ⟨y, hyL⟩))
  have hfinr : Module.finrank (ZMod 2) (LinearMap.range (pslRep φ yy - 1)) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) := by
    simpa [hphiyy] using w135c2_psl_finrank_range φ yy
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, ε, hs1, hE, h0, hact, hper, hrank, ⟨k', _, _, hcardW⟩, hdesc, hrot, hmin⟩ :=
    w135c2_psl_label_ext (m := m) (f := f) (by omega) hKcard (pslRep φ) hirr hne
  have hks : k = s := by
    have h : 2 ^ k = 2 ^ s := by rw [← hk, w135c2_psl_lend_card φ hφs, hE]
    exact Nat.pow_right_injective (le_refl 2) h
  rw [hks] at hk hrk hr
  have hsu : s * r ≤ 3 := by rw [← hr]; exact hm
  have hmv : movedTop (by omega : 2 ≤ m + 1) ε ≤ 4 * r := by
    have h1 : s * movedTop (by omega : 2 ≤ m + 1) ε ≤ s * (4 * r) := by
      calc s * movedTop (by omega : 2 ≤ m + 1) ε
          ≤ 2 * Module.finrank (ZMod 2) (LinearMap.range (pslRep φ yy - 1)) :=
            hrank yy hyy2 hyy1
        _ = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) := by rw [hfinr]
        _ ≤ 2 * (2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t))) :=
            Nat.mul_le_mul_left 2 hyd
        _ = s * (4 * r) := by rw [hr]; ring
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hdvd : s ∣ f := w135c2_psl_period_dvd hs1 ε hrot hmin
  have hd : d = Module.finrank k' (BModel k' ε) := by
    have hcardA : Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
    have h : 2 ^ (s * d) = 2 ^ (s * Module.finrank k' (BModel k' ε)) := by
      rw [← hrk, ← w135_card_eq_two_pow_rk hW, hcardA, hcardW]
    exact Nat.eq_of_mul_eq_mul_left hs1 (Nat.pow_right_injective le_rfl h)
  rcases w135c2_psl_outer_range (n := m + 1) (by omega) hs1 hr1 hsu ε h0 hact hper hdvd hmv hd with
    ⟨r₀, j, hone, hεj, hj⟩ | ⟨_, hf3, _⟩ | ⟨hn6, hf1, hs1', hd20⟩ |
      ⟨hn8, hf1, hs1', hd28⟩ | ⟨hn4, hf1⟩ | hrange
  · obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj
    exact w135c2_natural hctx htY ht2 hW
      (w135c2_psl_natural (by omega : 2 ≤ m + 1) hKcard φ hφs hker hj β hβ)
  · exfalso
    obtain rfl : m = 1 := by omega
    subst hf3
    have hlie' : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3 := by simpa using hlie
    exact htL (finL28_involution_mem hctx hlie' htY ht2)
  · exfalso
    obtain rfl : m = 5 := by omega
    subst hf1
    have hlie' : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 6 2 1 := by simpa using hlie
    have hcard20 : Nat.card W = 2 ^ 20 := by
      rw [w135_card_eq_two_pow_rk hW, hrk, hs1', hd20]
    have h4 := finRowStmt_psl_six_twenty W hW Y L t hctx htY ht2 hlie' hcard20
    omega
  · exfalso
    obtain rfl : m = 7 := by omega
    subst hf1
    have hlie' : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 8 2 1 := by simpa using hlie
    have hcard28 : Nat.card W = 2 ^ 28 := by
      rw [w135_card_eq_two_pow_rk hW, hrk, hs1', hd28]
    have h4 := finRowStmt_psl_eight_twentyeight W hW Y L t hctx htY ht2 hlie' hcard28
    omega
  · exact absurd ⟨hn4, hf1⟩ hn41
  · exact w135c2_psl_outer_finish hRows hW hctx htY ht2 hm hn41 hlie hk hrk hrange

end CFSG.LocalAnalysis.WeakClosure81
