module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenBasic
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenLift
public import CFSG.RankThree.GF2n.Tim81.Cited.OddTranspRootL2
import CFSG.Quasithin.Background.C41PfW
import CFSG.Timmesfeld.Bridge.OddTranspSimple
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem conn_gen
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S))
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) {f : ℕ}
    (hcard : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ f) :
    ∃ g : X, SevenK.IsL2OrSz ↥(CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) g) f := by
  classical
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  have hP : CFSG.pCore 2 (X ⧸ Subgroup.center X) = ⊥ := by
    refine h.eq_bot_of_normal_isSolvable_quot _ (CFSG.BaerSuzuki.Helpers.pCore_normal 2) ?_
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 (X ⧸ Subgroup.center X)) :=
      (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2).isNilpotent
    infer_instance
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    h.eq_bot_of_normal_isSolvable_quot (Subgroup.center _) inferInstance
      (Group.isSolvable_of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
  have hO2 : ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN h2
    have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN h2
    rw [hP] at hle
    exact le_bot_iff.mp hle
  have hset : CFSG.Timmesfeld.Bridge.Asc72.Setup (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) := h.setup_quot hdeg
  have hst : QuotientGroup.mk' (Subgroup.center X) s ∈
      QuotientGroup.mk' (Subgroup.center X) '' dSet S := ⟨s, hsD, rfl⟩
  obtain ⟨xt, hxt, hxt_gt, hxt_odd⟩ := CFSG.Timmesfeld.exists_opposite hset.isClass
    (CFSG.Timmesfeld.Bridge.OddTransp.isRootInvolutionSet_of_isOddTransp hset.oddT) hO2 hst
  have hxtnc : ¬ Commute (QuotientGroup.mk' (Subgroup.center X) s) xt := by
    intro hc
    have hsq : (QuotientGroup.mk' (Subgroup.center X) s * xt) ^ 2 = 1 :=
      (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one (hset.oddT.mul_self_eq_one hst)
        (hset.oddT.mul_self_eq_one hxt)).1 hc
    have hdvd : orderOf (QuotientGroup.mk' (Subgroup.center X) s * xt) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    have hle : orderOf (QuotientGroup.mk' (Subgroup.center X) s * xt) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hdvd
    rcases hxt_odd with ⟨k, hk⟩
    omega
  have hL : CFSG.RankThree.GF2n.Tim81.IsL2Gen
      (CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s))
      (CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S) xt) := by
    have h0 := (CFSG.RankThree.GF2n.Tim81.oddTranspRootL2
      (K := X ⧸ Subgroup.center X)
      (D := QuotientGroup.mk' (Subgroup.center X) '' dSet S))
      hset hP hZ h.meetsSq_quot hconn (QuotientGroup.mk' (Subgroup.center X) s)
      hst xt hxt hxtnc
    simpa only [CFSG.Timmesfeld.rootGroup] using h0
  have hf2 : 2 ≤ f := by
    by_contra hf
    have hfl : f ≤ 1 := by omega
    have hle : Nat.card S ≤ 2 ^ f := by
      have h1 : Nat.card S ≤ Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) :=
        Subgroup.card_le_of_le (h.le_rootGroup hdeg hs hs1)
      rwa [hcard] at h1
    have hpow : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hfl
    simp at hpow
    exact (not_le.mpr h.card) (hle.trans hpow)
  have hcardA : Nat.card (CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s)) = 2 ^ f := by
    rw [← h.map_rootGroup hsD, h.card_map_rootGroup hsD, hcard]
  have hPSL : CFSG.Quasithin.IsPSL 2 2 f
      ↥(CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
        CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S) xt) := by
    obtain ⟨F, hF, hFfin, hFchar, φ, hφcard, -⟩ := hL
    letI : Field F := hF
    letI : Finite F := hFfin
    letI : CharP F 2 := hFchar
    refine CFSG.Quasithin.C41Pf.isPSL_two_two_of_equiv_sl2 hf2 ?_ φ
    rw [hφcard, hcardA]
  obtain ⟨x, hxD, hxxt⟩ := hxt
  obtain ⟨y, hy⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.isConj_of_isClass h.exists_isClass hsD hxD)
  have hxteq : xt = QuotientGroup.mk' (Subgroup.center X) y *
      QuotientGroup.mk' (Subgroup.center X) s *
      (QuotientGroup.mk' (Subgroup.center X) y)⁻¹ := by
    rw [← hxxt, ← hy]
    simp only [map_mul, map_inv]
  have hrootx : CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) xt =
      conjSubgroup (CFSG.Timmesfeld.rootGroup
        (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s))
        (QuotientGroup.mk' (Subgroup.center X) y)⁻¹ := by
    rw [hxteq, CFSG.Timmesfeld.rootGroup_conj hset.isClass]
    simp only [CFSG.Quasithin.conjSubgroup, inv_inv]
  have hmap : (CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) y⁻¹).map
        (QuotientGroup.mk' (Subgroup.center X)) =
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) ⊔
        CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S) xt := by
    rw [Subgroup.map_sup, map_conjSubgroup_mk, h.map_rootGroup hsD, hrootx]
    simp only [map_inv]
  refine ⟨y⁻¹, ?_⟩
  have hLimage : SevenK.IsL2OrSz ↥((CFSG.Timmesfeld.rootGroup (dSet S) s ⊔
      conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) y⁻¹).map
        (QuotientGroup.mk' (Subgroup.center X))) f := by
    rw [hmap]
    exact Or.inl hPSL
  have hB : IsPGroup 2 (conjSubgroup (CFSG.Timmesfeld.rootGroup (dSet S) s) y⁻¹) :=
    IsPGroup.map (CFSG.Timmesfeld.isPGroup_rootGroup h.root hsD) _
  exact h.isL2OrSz_of_map (CFSG.Timmesfeld.isPGroup_rootGroup h.root hsD) hB hLimage

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
