module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LiftB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
private theorem w135c2_hnab_of_ctx (hctx : Is135Context Y L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
  have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]

omit [Finite W] in
private theorem w135c2_ne_bot_of_ctx (hctx : Is135Context Y L) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, b, hb, hab⟩ := w135c2_hnab_of_ctx hctx
  rw [hbot] at ha hb
  rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb] at hab
  exact hab rfl

theorem w135c2_gen_of_gs03For {R : StatedLieTag → ℕ → ℕ → Prop} (hGS : GS03AlphaFor R)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2) {s : StatedLieTag} {n f : ℕ}
    (hR : R s n f) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) s n 2 f) :
    ∃ T : Finset (MulAut W), T.card ≤ gs03Bound s n f ∧ (∀ x ∈ T, ∃ g ∈ L, x = g * t * g⁻¹) ∧
      L ≤ Subgroup.closure (T : Set (MulAut W)) := by
  classical
  have hZNorm : ((Zc L).subgroupOf Y).Normal := w135c2_Zc_normal_in hctx
  let N : Subgroup ↥Y := (Zc L).subgroupOf Y
  have hN' : N.Normal := hZNorm
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  let S : Subgroup (↥Y ⧸ N) := (L.subgroupOf Y).map π
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite ↥Y :=
    Finite.of_injective (fun y : ↥Y => (y : MulAut W)) Subtype.coe_injective
  have : Finite (↥Y ⧸ N) := inferInstance
  let tb : ↥Y ⧸ N := π ⟨t, htY⟩
  have ht_sq : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2] at h
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
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime htb2 htb1
  have hSnormal : S.Normal := w135c2_S_normal hctx
  have hScent : Subgroup.centralizer (S : Set (↥Y ⧸ N)) = ⊥ :=
    w135c2_S_centralizer hctx
  obtain ⟨e⟩ := w135c2_S_equiv hctx
  obtain ⟨Tb, hTbcard, hTbconj, hTbgen⟩ :=
    hGS (↥Y ⧸ N) S hSnormal hScent s n f hR (LieModel.of_mulEquiv e hlie) tb hord
  obtain ⟨T, hTcard, hTconj, hLgen⟩ := w135c2_lift_gen hctx htY Tb hTbconj hTbgen
  exact ⟨T, hTcard.trans hTbcard, hTconj, hLgen⟩

theorem w135c2_four_le_mQuot_of_gs03 {R : StatedLieTag → ℕ → ℕ → Prop} (hGS : GS03AlphaFor R)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    {s : StatedLieTag} {n f : ℕ} (hR : R s n f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) s n 2 f) (hrk : 3 * gs03Bound s n f < rk W) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hL : L ≠ ⊥ := w135c2_ne_bot_of_ctx hctx
  obtain ⟨T, hTcard, hTconj, hTgen⟩ :=
    w135c2_gen_of_gs03For hGS hctx htY ht2 hR hlie
  have hgen : rk W ≤ gs03Bound s n f * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) :=
    w135c2_rk_le_mul_of_conj_gen hW hirr hL T hTconj hTgen hTcard
  by_contra h4
  have hm3 : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 := by omega
  have hle : rk W ≤ 3 * gs03Bound s n f := by
    calc rk W ≤ gs03Bound s n f * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hgen
      _ ≤ gs03Bound s n f * 3 := Nat.mul_le_mul_left _ hm3
      _ = 3 * gs03Bound s n f := Nat.mul_comm _ _
  omega

end CFSG.LocalAnalysis.WeakClosure81
