module

public import Certificates.Kernel.BabyMonster.Facts3101
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check10
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check11
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check12
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check13
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check20
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check21
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check22
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check23
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Open.LocalVocabulary
public import Certificates.Kernel.BabyMonster.Chain2

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.KC.BM.NativePair24 CFSG.KC.BM.Fix

set_option maxRecDepth 100000

theorem foldl_mul_eq {M : Type*} [Monoid M] (a : M) (l : List M) :
    l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => rw [List.foldl_nil, List.prod_nil, mul_one]
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem sq_step {M : Type*} [Monoid M] {a b c : M} {n m : ℕ} (h : a ^ n = b) (hb : b * b = c)
    (hm : n * 2 = m) : a ^ m = c := by
  rw [← hm, pow_mul, h, sq, hb]

theorem wf1 {W : List Nat} (h : wfMat W = true) : ∀ X ∈ [W], wfMat X = true := by
  intro X hX
  rw [List.mem_singleton] at hX
  rw [hX]
  exact h

theorem wf2 {W V : List Nat} (hW : wfMat W = true) (hV : wfMat V = true) :
    ∀ X ∈ [W, V], wfMat X = true := by
  intro X hX
  rcases List.mem_pair.1 hX with rfl | rfl
  · exact hW
  · exact hV

theorem sm1 {A W C : List Nat} (hW : wfMat W = true) (hA : wfMat A = true)
    (h : AllStrips [W] A C) : stripMat A * stripMat W = stripMat C := by
  have e := stripMat_mul_of_allStrips (wf1 hW) hA h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e

theorem sm1one {A W : List Nat} (hW : wfMat W = true) (hA : wfMat A = true)
    (h : AllStrips [W] A idStrips) : stripMat A * stripMat W = 1 := by
  have e := stripMat_mul_eq_one (wf1 hW) hA h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e

theorem sm2one {A W V : List Nat} (hW : wfMat W = true) (hV : wfMat V = true)
    (hA : wfMat A = true) (h : AllStrips [W, V] A idStrips) :
    stripMat A * stripMat W * stripMat V = 1 := by
  have e := stripMat_mul_eq_one (wf2 hW hV) hA h
  rwa [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
    List.foldl_nil] at e

theorem sm11 {A W C D : List Nat} (hW : wfMat W = true) (hD : wfMat D = true)
    (hA : wfMat A = true) (hC : wfMat C = true) (h : AllStrips2 [W] [D] A C) :
    stripMat A * stripMat W = stripMat C * stripMat D := by
  have e := stripMat_mul_eq_of_allStrips2 (wf1 hW) (wf1 hD) hA hC h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil] at e

theorem conjF : stripMat W * stripMat F = stripMat F0 * stripMat W :=
  sm11 wf_F wf_W wf_W wf_F0 (by bm_strips2 CFSG.KC.BM.NativePair24.conjF 69)

theorem f0sq : stripMat F0 * stripMat F0 = 1 :=
  sm1one wf_F0 wf_F0 (by bm_strips CFSG.KC.BM.NativePair24.f0sq 69)

theorem f0ne : stripMat F0 ≠ 1 := notId_sound wf_F0 ne_F0

theorem rkF0 : stripMat PF0 * (stripMat F0 + 1) = stripMat QF0 :=
  stripMat_mul_add_one wf_F0 wf_PF0 (by bm_stripsx CFSG.KC.BM.NativePair24.rkF0_ 69)

theorem rankF0 : (stripMat F0 - 1).rank = 2158 :=
  CertificateChecks.KernelBM.Fix.rank_sub_one (by norm_num) rkF0 (shapeOK_sound wf_QF0 shapeF0)
    (echFrom_sound wf_PF0 echF0)

theorem ta : stripMat F * stripMat T = stripMat T * stripMat CFSG.KC.BM.Seeds.A1 :=
  sm11 wf_T CFSG.KC.BM.Seeds.wf_A1 wf_F wf_T (by bm_strips2 CFSG.KC.BM.NativePair24.ta 69)

theorem tb : stripMat NativePair.Q25 * stripMat T = stripMat T * stripMat CFSG.KC.BM.Seeds.A2 :=
  sm11 wf_T CFSG.KC.BM.Seeds.wf_A2 wf_Q25 wf_T (by bm_strips2 CFSG.KC.BM.NativePair24.tb 69)

theorem tinv : stripMat T * stripMat Ti = 1 :=
  sm1one wf_Ti wf_T (by bm_strips CFSG.KC.BM.NativePair24.tinv 69)

theorem bcube : stripMat NativePair.Q25 * stripMat NativePair.Q25 * stripMat NativePair.Q25 = 1 :=
  sm2one wf_Q25 wf_Q25 wf_Q25 (by bm_strips CFSG.KC.BM.NativePair24.bcube 69)

theorem bne : stripMat NativePair.Q25 ≠ 1 := notId_sound wf_Q25 ne_b

theorem cAB : stripMat F * stripMat NativePair.Q25 = stripMat AB :=
  sm1 wf_Q25 wf_F (by bm_strips CFSG.KC.BM.NativePair24.cAB 69)

theorem ab_sq1 : stripMat AB * stripMat AB = stripMat AB_sq1 :=
  sm1 wf_AB wf_AB (by bm_strips CFSG.KC.BM.NativePair24.cAB_sq1 69)

theorem ab_sq2 : stripMat AB_sq1 * stripMat AB_sq1 = stripMat AB_sq2 :=
  sm1 wf_AB_sq1 wf_AB_sq1 (by bm_strips CFSG.KC.BM.NativePair24.cAB_sq2 69)

theorem ab_sq3 : stripMat AB_sq2 * stripMat AB_sq2 = stripMat AB_sq3 :=
  sm1 wf_AB_sq2 wf_AB_sq2 (by bm_strips CFSG.KC.BM.NativePair24.cAB_sq3 69)

theorem ab_sq4 : stripMat AB_sq3 * stripMat AB_sq3 = stripMat AB_sq4 :=
  sm1 wf_AB_sq3 wf_AB_sq3 (by bm_strips CFSG.KC.BM.NativePair24.cAB_sq4 69)

theorem ab_sq5 : stripMat AB_sq4 * stripMat AB_sq4 = stripMat AB_sq5 :=
  sm1 wf_AB_sq4 wf_AB_sq4 (by bm_strips CFSG.KC.BM.NativePair24.cAB_sq5 69)

theorem ab_pp0 : stripMat AB_sq1 * stripMat AB_sq2 = stripMat oab_pp0 :=
  sm1 wf_AB_sq2 wf_AB_sq1 (by bm_strips CFSG.KC.BM.NativePair24.coab_pp0 69)

theorem ab_pp1 : stripMat oab_pp0 * stripMat AB_sq4 = stripMat oab_pp1 :=
  sm1 wf_AB_sq4 wf_oab_pp0 (by bm_strips CFSG.KC.BM.NativePair24.coab_pp1 69)

theorem ab_p : stripMat oab_pp1 * stripMat AB_sq5 = stripMat oab_p :=
  sm1 wf_AB_sq5 wf_oab_pp1 (by bm_strips CFSG.KC.BM.NativePair24.coab_p 69)

theorem ab_last : stripMat oab_p * stripMat AB = 1 :=
  sm1one wf_AB wf_oab_p (by bm_strips CFSG.KC.BM.NativePair24.oab_pow 69)

theorem ab_pow : stripMat AB ^ 55 = 1 := by
  have h2 : stripMat AB ^ 2 = stripMat AB_sq1 := by rw [sq, ab_sq1]
  have h4 : stripMat AB ^ 4 = stripMat AB_sq2 := sq_step h2 ab_sq2 rfl
  have h8 : stripMat AB ^ 8 = stripMat AB_sq3 := sq_step h4 ab_sq3 rfl
  have h16 : stripMat AB ^ 16 = stripMat AB_sq4 := sq_step h8 ab_sq4 rfl
  have h32 : stripMat AB ^ 32 = stripMat AB_sq5 := sq_step h16 ab_sq5 rfl
  have e : stripMat AB ^ 55 = stripMat AB ^ 2 * stripMat AB ^ 4 * stripMat AB ^ 16 *
      stripMat AB ^ 32 * stripMat AB := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_succ]
  rw [e, h2, h4, h16, h32, ab_pp0, ab_pp1, ab_p, ab_last]

theorem ab_ne : ∀ t, 0 < t → t < 55 → stripMat AB ^ t ≠ 1 :=
  orbOK_sound (m₁ := 54) rfl (by decide) wf_AB oab_orb

theorem pr_sq1 : stripMat PR * stripMat PR = stripMat PR_sq1 :=
  sm1 wf_PR wf_PR (by bm_strips CFSG.KC.BM.NativePair24.cPR_sq1 69)

theorem pr_sq2 : stripMat PR_sq1 * stripMat PR_sq1 = stripMat PR_sq2 :=
  sm1 wf_PR_sq1 wf_PR_sq1 (by bm_strips CFSG.KC.BM.NativePair24.cPR_sq2 69)

theorem pr_sq3 : stripMat PR_sq2 * stripMat PR_sq2 = stripMat PR_sq3 :=
  sm1 wf_PR_sq2 wf_PR_sq2 (by bm_strips CFSG.KC.BM.NativePair24.cPR_sq3 69)

theorem pr_sq4 : stripMat PR_sq3 * stripMat PR_sq3 = stripMat PR_sq4 :=
  sm1 wf_PR_sq3 wf_PR_sq3 (by bm_strips CFSG.KC.BM.NativePair24.cPR_sq4 69)

theorem pr_pp0 : stripMat PR_sq1 * stripMat PR_sq2 = stripMat opr_pp0 :=
  sm1 wf_PR_sq2 wf_PR_sq1 (by bm_strips CFSG.KC.BM.NativePair24.copr_pp0 69)

theorem pr_p : stripMat opr_pp0 * stripMat PR_sq4 = stripMat opr_p :=
  sm1 wf_PR_sq4 wf_opr_pp0 (by bm_strips CFSG.KC.BM.NativePair24.copr_p 69)

theorem pr_last : stripMat opr_p * stripMat PR = 1 :=
  sm1one wf_PR wf_opr_p (by bm_strips CFSG.KC.BM.NativePair24.opr_pow 69)

theorem pr_pow : stripMat PR ^ 23 = 1 := by
  have h2 : stripMat PR ^ 2 = stripMat PR_sq1 := by rw [sq, pr_sq1]
  have h4 : stripMat PR ^ 4 = stripMat PR_sq2 := sq_step h2 pr_sq2 rfl
  have h8 : stripMat PR ^ 8 = stripMat PR_sq3 := sq_step h4 pr_sq3 rfl
  have h16 : stripMat PR ^ 16 = stripMat PR_sq4 := sq_step h8 pr_sq4 rfl
  have e : stripMat PR ^ 23 = stripMat PR ^ 2 * stripMat PR ^ 4 * stripMat PR ^ 16 *
      stripMat PR := by
    rw [← pow_add, ← pow_add, ← pow_succ]
  rw [e, h2, h4, h16, pr_pp0, pr_p, pr_last]

theorem pr_ne : stripMat PR ≠ 1 := by
  have h := orbOK_sound (m₁ := 22) rfl (by decide) wf_PR opr_orb 1 (by norm_num) (by norm_num)
  rwa [pow_one] at h

end CertificateChecks.KernelBM.Pair

end
