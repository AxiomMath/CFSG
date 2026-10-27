module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aFix
public import CFSG.RankThree.PartOne.KF.BloomBasic
public import CFSG.Quasithin.Background.B1Transvection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_false_of_case168_3_cartan (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h3 : Case168_3 D ⊥ V hV L)
    (hN : Mbar D.M ⊥ V hV ≤ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))))
    {x : MulAut (Vtil ⊥ V hV)} (hx : CartanBar1614 D V hV 3 x) : False := by
  classical
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
  have hW : ∀ w : Vtil ⊥ V hV, w * w = 1 := fun w => by
    rw [← pow_two]
    exact hW2 w
  have hcardW : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have h := card_eq_two_pow (V := Vtil ⊥ V hV) hW2 ⊤
    rwa [Subgroup.card_top, h3.2.1] at h
  have hx7 : x ^ 7 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx.2.1] at h
    rwa [show (2 : ℕ) ^ 3 - 1 = 7 by norm_num] at h
  have hcardC :
      Nat.card ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x)) = 8 := by
    have h := hx.2.2.1
    rwa [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
  have hxN : x ∈ Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := hN hx.1
  let gx : Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := ⟨x, hxN⟩
  let F : Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) →*
      MulAut ↥(lBar ⊥ V hV L) := (lBar ⊥ V hV L).normalizerMonoidHom
  let α : MulAut ↥(lBar ⊥ V hV L) := F gx
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard27 : Nat.card ↥(lBar ⊥ V hV L) = 27 := by
    have h := h3.1.2.1
    rwa [show (3 : ℕ) ^ 3 = 27 by norm_num] at h
  have hcenter3 : Nat.card (Subgroup.center ↥(lBar ⊥ V hV L)) = 3 := by
    haveI : CFSG.IsExtraspecial 3 ↥(lBar ⊥ V hV L) := h3.1.1
    exact CFSG.IsExtraspecial.center_order_p 3 ↥(lBar ⊥ V hV L)
  have hα7 : α ^ 7 = 1 := by
    have hgx7 : gx ^ 7 = 1 := Subtype.ext (by
      change x ^ 7 = 1
      exact hx7)
    change (F gx) ^ 7 = 1
    rw [← map_pow, hgx7, map_one]
  have hα1 : α = 1 :=
    CFSG.RankThree.PartOne.KFBloom.aut_eq_one_of_card_27 (p := 7) hcard27 hcenter3
      (by norm_num) α hα7
  have hcomm : ∀ ℓ ∈ lBar ⊥ V hV L, x * ℓ = ℓ * x := by
    intro ℓ hℓ
    have hαℓ : α ⟨ℓ, hℓ⟩ = ⟨ℓ, hℓ⟩ := by rw [hα1]; rfl
    have hcoe : (↑(α ⟨ℓ, hℓ⟩) : MulAut (Vtil ⊥ V hV)) = x * ℓ * x⁻¹ := by
      change (↑(((lBar ⊥ V hV L).normalizerMonoidHom gx) ⟨ℓ, hℓ⟩) :
        MulAut (Vtil ⊥ V hV)) = x * ℓ * x⁻¹
      exact Subgroup.normalizerMonoidHom_apply_apply_coe (lBar ⊥ V hV L) gx ⟨ℓ, hℓ⟩
    have hxℓ : x * ℓ * x⁻¹ = ℓ := by
      rw [← hcoe]
      exact congrArg Subtype.val hαℓ
    calc x * ℓ = (x * ℓ * x⁻¹) * x := by group
      _ = ℓ * x := by rw [hxℓ]
  have hUinv : ∀ ℓ ∈ lBar ⊥ V hV L, ∀ u ∈ fixV (Subgroup.zpowers x),
      ℓ u ∈ fixV (Subgroup.zpowers x) := by
    intro ℓ hℓ u hu
    have hxu : x u = u := (mem_fixV.1 hu) x (Subgroup.mem_zpowers x)
    have hxℓu : x (ℓ u) = ℓ u := by
      have h := congrArg (fun f : MulAut (Vtil ⊥ V hV) => f u) (hcomm ℓ hℓ)
      rw [MulAut.mul_apply, MulAut.mul_apply, hxu] at h
      exact h
    rw [mem_fixV]
    intro g hg
    have hgs : g ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) (ℓ u) :=
      (Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hxℓu)) hg
    rwa [MulAction.mem_stabilizer_iff] at hgs
  have hfix : ∀ ℓ : ↥(lBar ⊥ V hV L), ℓ ∈ Subgroup.center ↥(lBar ⊥ V hV L) → ℓ ≠ 1 →
      ∀ u ∈ fixV (Subgroup.zpowers x), (ℓ : MulAut (Vtil ⊥ V hV)) u = u → u = 1 := by
    intro ℓ hℓ hℓ1 u _ hfixu
    exact s16c167_central_fixed_point_free (W := Vtil ⊥ V hV) hW hcardW
      (L := lBar ⊥ V hV L) h3.1 hℓ hℓ1 hfixu
  have hUbot_or_card : fixV (Subgroup.zpowers x) = ⊥ ∨
      Nat.card ↥(fixV (Subgroup.zpowers x)) = 2 ^ 6 :=
    s16c167_invariant_eq_bot_or_card (W := Vtil ⊥ V hV) hW hcardW
      (L := lBar ⊥ V hV L) h3.1 (fixV (Subgroup.zpowers x)) hUinv hfix
  obtain ⟨hsup, hinf, -, -⟩ :=
    CFSG.Quasithin.B1.zpowers_decomp (V := Vtil ⊥ V hV) hW2 (x := x) (r := 7)
      (by norm_num) hx7
  have hcardU : Nat.card ↥(fixV (Subgroup.zpowers x)) = 8 := by
    have h := card_sup_mul_card_inf (V := Vtil ⊥ V hV) (fixV (Subgroup.zpowers x))
      (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x))
    rw [hsup, hinf, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
    rw [hcardW, hcardC] at h
    norm_num at h
    omega
  rcases hUbot_or_card with hbot | hcard
  · rw [hbot, Subgroup.card_bot] at hcardU
    omega
  · norm_num at hcard
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
