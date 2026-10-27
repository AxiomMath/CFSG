module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LiftB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

@[expose] def PsuSixOuterRow : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : MulAut W),
      Is135Context Y L → t ∈ Y → t ∉ L → orderOf t = 2 →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 → Nat.card W = 2 ^ 20 →
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t))

private theorem w135c2_hnab_of_ctx {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
  have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]

private theorem w135c2_ne_bot_of_ctx {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, b, hb, hab⟩ := w135c2_hnab_of_ctx hctx
  rw [hbot] at ha hb
  rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb] at hab
  exact hab rfl

theorem psuSixOuterRow_of_gs03
    (h : GS03AlphaOuterFor fun t n f => t = .PSU ∧ n = 6 ∧ f = 1) : PsuSixOuterRow := by
  classical
  intro W _ _ h2 Y L t hctx htY htL ht2 hlie hcard
  haveI hZNorm : ((Zc L).subgroupOf Y).Normal := w135c2_Zc_normal_in hctx
  let N : Subgroup ↥Y := (Zc L).subgroupOf Y
  haveI hN' : N.Normal := hZNorm
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  let S : Subgroup (↥Y ⧸ N) := (L.subgroupOf Y).map π
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Finite ↥Y :=
    Finite.of_injective (fun y : ↥Y => (y : MulAut W)) Subtype.coe_injective
  haveI : Finite (↥Y ⧸ N) := inferInstance
  let tb : ↥Y ⧸ N := π ⟨t, htY⟩
  have ht_sq : t ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one t
    rwa [ht2] at hh
  have htb2 : tb ^ 2 = 1 := by
    dsimp [tb]
    rw [← map_pow, show (⟨t, htY⟩ : ↥Y) ^ 2 = 1 by
      apply Subtype.ext
      simpa using ht_sq, map_one]
  have htb1 : tb ≠ 1 := by
    intro h1
    have hmem : (⟨t, htY⟩ : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact w135c2_not_mem_Zc_of_order_two hctx ht2 (Subgroup.mem_subgroupOf.mp hmem)
  have hord : orderOf tb = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime htb2 htb1
  have hSnormal : S.Normal := w135c2_S_normal hctx
  have hScent : Subgroup.centralizer (S : Set (↥Y ⧸ N)) = ⊥ :=
    w135c2_S_centralizer hctx
  have hlieS : LieModel ↥S .PSU 6 2 1 := w135c2_lieModel_S hctx hlie
  have htbS : tb ∉ S := by
    intro hmem
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp hmem
    have hyN : y⁻¹ * ⟨t, htY⟩ ∈ N := QuotientGroup.eq.mp hyt
    have hz : (↑(y⁻¹ * ⟨t, htY⟩ : ↥Y) : MulAut W) ∈ Zc L :=
      Subgroup.mem_subgroupOf.mp hyN
    have hzL : (↑(y⁻¹ * ⟨t, htY⟩ : ↥Y) : MulAut W) ∈ L := w135c2_Zc_le L hz
    have hyL : (y : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hy
    apply htL
    have := L.mul_mem hyL hzL
    simpa using this
  obtain ⟨Tb, hTbcard, hTbconj, hTbgen⟩ :=
    h (↥Y ⧸ N) S hSnormal hScent .PSU 6 1 ⟨rfl, rfl, rfl⟩ hlieS tb hord htbS
  obtain ⟨T, hTcard, hTconj, hTgen⟩ := w135c2_lift_gen hctx htY Tb hTbconj hTbgen
  have hTcard6 : T.card ≤ 6 := by
    calc T.card ≤ Tb.card := hTcard
      _ ≤ gs03Bound .PSU 6 1 := hTbcard
      _ = 6 := by simp [gs03Bound]
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hLne : L ≠ ⊥ := w135c2_ne_bot_of_ctx hctx
  have hgen : rk W ≤ 6 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) :=
    w135c2_rk_le_mul_of_conj_gen h2 hirr hLne T hTconj hTgen hTcard6
  have hrk : rk W = 20 := by
    have h2eq : 2 ^ 20 = 2 ^ rk W := hcard.symm.trans (w135_card_eq_two_pow_rk h2)
    exact (Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2eq).symm
  omega

end CFSG.LocalAnalysis.WeakClosure81
