module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Bridge
public import CFSG.Quasithin.Background.B4L3Inv

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 (A12 B12)
open CFSG.GF2Type.Smith1979.GammaU (vecOf)
open HJBridge (grpOf J12x hjTauM)
open HJ12 (wordR hjTauc)

noncomputable def hjOmega : MulAut W12 := hjAct J12x

theorem hjOmega_mem_centralizer : hjOmega ∈ Subgroup.centralizer (hjL0 : Set (MulAut W12)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  unfold hjL0 at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [hjOmega, ← map_mul, ← map_mul, HJBridge.J12x_comm_A12]
    · rw [hjOmega, ← map_mul, ← map_mul, HJBridge.J12x_comm_B12]
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]

theorem orderOf_hjOmega : orderOf hjOmega = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [hjOmega, ← map_pow, HJBridge.J12x_pow_three, map_one]
  · intro h
    exact HJBridge.J12x_ne_one (hjAct_injective (h.trans (map_one hjAct).symm))

noncomputable def hjX7 : MulAut W12 := hjWord HJ12.hj_x7Word
noncomputable def hjP3 : Subgroup (MulAut W12) := grpOf (HJ12.hj_p3Words.map wordR)
def hjV1 : W12 := Multiplicative.ofAdd (vecOf 4)
def hjV2 : W12 := Multiplicative.ofAdd (vecOf 1024)
noncomputable def hjTau : MulAut W12 := hjAct hjTauM
noncomputable def hjT0 : Subgroup (MulAut W12) := grpOf (HJ12.hj_t0Words.map wordR)
noncomputable def hjT1 : Subgroup (MulAut W12) := grpOf (HJ12.hj_t0Words.map wordR ++ [hjTauc])
noncomputable def hjA1 : Subgroup (MulAut W12) := grpOf (HJ12.hj_a1Words.map wordR)
noncomputable def hjA2 : Subgroup (MulAut W12) := grpOf (HJ12.hj_a2Words.map wordR)
noncomputable def hjS1 : Subgroup (MulAut W12) := grpOf (HJ12.hj_stab1Words.map wordR)
noncomputable def hjE : Subgroup (MulAut W12) := grpOf (HJ12.hj_eWords.map wordR)
noncomputable def hjK : Subgroup (MulAut W12) := grpOf (HJ12.hj_stWords.map wordR)

theorem gensOKN_eq : HJ12.gensOKN = CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK := rfl

theorem rowsOf_hjOmega : HJBridge.RowsOf hjOmega HJ12.hjJc := fun v => by
  rw [hjOmega, hjAct_apply, HJBridge.linOfRows_hjJc]

theorem mulR_lt {g h : Array ℕ} (hg : ∀ y ∈ g, y < 4096) :
    ∀ y ∈ CFSG.GF2Type.Smith1979.GammaU.StepA.mulR g h, y < 4096 := by
  intro y hy
  obtain ⟨z, -, rfl⟩ := Array.mem_map.1 hy
  exact CFSG.GF2Type.Smith1979.GammaU.StepA.appN_lt hg z

theorem four_le_rk_of_card_fixV_le {x : MulAut W12}
    (h : Nat.card (fixV (Subgroup.zpowers x)) ≤ 256) :
    4 ≤ rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) := by
  have hmul : Nat.card (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) *
      Nat.card (fixV (Subgroup.zpowers x)) = 4096 := by
    have h1 := card_commV_mul_card_fixV W12_sq x
    rw [commV_eq_commSub] at h1
    refine h1.trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  have h2 : Nat.card (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) =
      2 ^ rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) := card_eq_two_pow W12_sq _
  rw [h2] at hmul
  by_contra hlt
  push Not at hlt
  have hle : 2 ^ rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.mul_le_mul hle h
  rw [hmul] at h3
  norm_num at h3

theorem card_commSub_mul_card_fixV (x : MulAut W12) :
    Nat.card (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) *
      Nat.card (fixV (Subgroup.zpowers x)) = 4096 := by
  have h1 := card_commV_mul_card_fixV W12_sq x
  rw [commV_eq_commSub] at h1
  refine h1.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

theorem rk_commSub_eq_of_card_fixV {x : MulAut W12} {k : ℕ} (hk : k ≤ 12)
    (h : Nat.card (fixV (Subgroup.zpowers x)) = 2 ^ (12 - k)) :
    rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) = k := by
  have hmul := card_commSub_mul_card_fixV x
  rw [h, card_eq_two_pow W12_sq (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)),
    ← pow_add] at hmul
  have h2 : rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) + (12 - k) = 12 :=
    Nat.pow_right_injective (le_refl 2) (hmul.trans (by norm_num))
  omega

theorem canon_of_mem_enumGrp {gs : List (Array ℕ)}
    (hgs : CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK gs = true) {r : Array ℕ}
    (hr : r ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp gs) :
    r.size = 12 ∧ ∀ y ∈ r, y < 4096 :=
  CFSG.GF2Type.Smith1979.GammaU.Viol.okRows_spec
    (CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp_sound
      (CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK_spec hgs) r hr).1

theorem rows_eq_of_rowsOf {x : MulAut W12} {r s : Array ℕ} (hr : HJBridge.RowsOf x r)
    (hs : HJBridge.RowsOf x s) (hr' : r.size = 12 ∧ ∀ y ∈ r, y < 4096)
    (hs' : s.size = 12 ∧ ∀ y ∈ s, y < 4096) : r = s :=
  CFSG.GF2Type.Smith1979.GammaU.StepA.rows_eq hr'.1 hs'.1 hr'.2 hs'.2 fun v =>
    Multiplicative.ofAdd.injective ((hr v).symm.trans (hs v))

theorem mem_fixV_of_mem_fixCodes {x : MulAut W12} {r : Array ℕ} (hx : HJBridge.RowsOf x r)
    {s : ℕ} (hs : s ∈ HJ12.fixCodes r) :
    (Multiplicative.ofAdd (vecOf s) : W12) ∈ fixV (Subgroup.zpowers x) := by
  simp only [HJ12.fixCodes, List.mem_filter, List.mem_range, beq_iff_eq,
    CFSG.GF2Type.Smith1979.GammaU.native_appN] at hs
  rw [HJBridge.mem_fixV_zpowers_iff, hx, ← CFSG.GF2Type.Smith1979.GammaU.vecOf_appN, hs.2]

theorem hjWord_ne_one {w : List ℕ}
    (h : HJ12.wordR w ≠ CFSG.GF2Type.Smith1979.GammaU.StepA.idR) : hjWord w ≠ 1 := by
  intro h1
  have hr := HJBridge.rowsOf_hjWord w
  rw [h1] at hr
  obtain ⟨hs, hlt⟩ := HJBridge.wordR_canon w
  refine h (CFSG.GF2Type.Smith1979.GammaU.StepA.rows_eq hs rfl hlt (by decide) fun v => ?_)
  have e1 := hr v
  rw [HJBridge.rowsOf_one v] at e1
  exact (Multiplicative.ofAdd.injective e1).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
