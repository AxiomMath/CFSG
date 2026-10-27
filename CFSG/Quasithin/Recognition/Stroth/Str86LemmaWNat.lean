module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbBase
public import CFSG.Quasithin.Background.SmithB45U3Nat

import CFSG.Quasithin.Recognition.Stroth.Str86XOne3
import CFSG.Quasithin.H13.KG14726Elim
import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni
import CFSG.Quasithin.Background.F7TwoInvAutWrap
import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2F5
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem pCore_le_chiefHom_ker {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) :
    pCore 2 ↥H ≤ (Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1)).ker := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU2
  intro g hg
  rw [MonoidHom.mem_ker]
  have hgH : ((g : ↥H) : G) ∈ pCoreOf 2 H := (F1.mem_pCore_iff_coe (H := H) g).mp hg
  exact (Ch3z.chiefHom_eq_one_iff hHL hHN hNL g).mpr
    (Ch3z.pCoreOf_le_centralizerMod hUH hstep hE hgH)

private theorem pCore_le_chiefPsi_ker {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) :
    pCore 2 ↥H ≤ (Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1)).ker := by
  intro g hg
  have h1 : Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) g = 1 :=
    MonoidHom.mem_ker.mp (pCore_le_chiefHom_ker hstep hUH hU2 hg)
  simpa [Ch3z.chiefHom] using congrArg Subtype.val h1

private noncomputable def chiefLift {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) :
    oTwoQuot ↥H →* MulAut ↥(Ch3z.chiefMod L N) :=
  QuotientGroup.lift (pCore 2 ↥H)
    (Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1))
    (pCore_le_chiefPsi_ker hstep hUH hU2)

private theorem chiefLift_range {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) :
    (chiefLift hstep hUH hU2).range = Ch3z.chiefAut H L N := by
  classical
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) y
    show (chiefLift hstep hUH hU2) ((QuotientGroup.mk' (pCore 2 ↥H)) g) ∈
      Ch3z.chiefAut H L N
    rw [chiefLift, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    exact (Ch3z.chiefHom hHL hHN g).2
  · intro hx
    obtain ⟨g, hg⟩ := Ch3z.chiefHom_surjective hHL hHN ⟨x, hx⟩
    refine ⟨QuotientGroup.mk' (pCore 2 ↥H) g, ?_⟩
    show (chiefLift hstep hUH hU2) ((QuotientGroup.mk' (pCore 2 ↥H)) g) = x
    rw [chiefLift, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    exact congrArg Subtype.val hg

private theorem chiefAut_perfect {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) (hqH : IsQuasisimple (oTwoQuot ↥H)) :
    Group.IsPerfect ↥(Ch3z.chiefAut H L N) := by
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hqH.1
  have h := Group.IsPerfect.range (chiefLift hstep hUH hU2)
  rwa [chiefLift_range hstep hUH hU2] at h

private theorem chiefAut_irreducible {H U L N : Subgroup G} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) :
    ∀ W : Subgroup ↥(Ch3z.chiefMod L N),
      (∀ g ∈ Ch3z.chiefAut H L N, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
  fun W hW => Ch3z.chiefMod_irr hstep hUH W hW

private theorem le_normalizer_centralizerMod {H U L N : Subgroup G}
    (hstep : IsChiefStep H U L N) (hUH : U ≤ H) :
    H ≤ Subgroup.normalizer (centralizerMod L H N : Set G) := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hKsub : (centralizerMod L H N).subgroupOf H = (Ch3z.chiefHom hHL hHN).ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, ← Ch3z.chiefHom_eq_one_iff hHL hHN hNL g,
      MonoidHom.mem_ker]
  have hN : ((centralizerMod L H N).subgroupOf H).Normal := by
    rw [hKsub]
    exact MonoidHom.normal_ker _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (H := centralizerMod L H N) (K := H) (fun x hx => hx.1)).mp hN

private theorem chiefPsi_ne_one {H U L N : Subgroup G} {t : G} {q : ℕ}
    (hstep : IsChiefStep H U L N) (hUH : U ≤ H) (hU2 : IsPGroup 2 U)
    (hnc : ¬ IsCentralStep H L N) (htH : t ∈ H) (ht2 : t * t = 1)
    (htO : t ∉ pCoreOf 2 H) (hqHq : IsSzU3Quot (oTwoQuot ↥H) q) :
    Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) ⟨t, htH⟩ ≠ 1 := by
  intro ht1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU2
  have hch1 : Ch3z.chiefHom hHL hHN ⟨t, htH⟩ = 1 := Subtype.ext ht1
  have htK : t ∈ centralizerMod L H N :=
    (Ch3z.chiefHom_eq_one_iff hHL hHN hNL ⟨t, htH⟩).mp hch1
  have hQK : pCoreOf 2 H ≤ centralizerMod L H N :=
    Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  rcases eq_or_mem_pCoreOf_of_normal (K := centralizerMod L H N) hqHq (fun x hx => hx.1)
    (le_normalizer_centralizerMod hstep hUH) hQK with hKH | h2el
  · refine hnc (fun g hg x hx => ?_)
    have hg' : g ∈ centralizerMod L H N := by
      rw [hKH]
      exact hg
    exact hg'.2.2 x hx
  · have htz : t ^ 2 ^ 1 = 1 := by
      simpa only [pow_one, pow_two] using ht2
    exact htO (h2el t htK ⟨1, htz⟩)

private theorem fixV_zpowers_chiefPsi_eq {H U L N : Subgroup G} {t : G}
    {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)} (hstep : IsChiefStep H U L N)
    (htH : t ∈ H) :
    @fixV ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Subgroup.zpowers (Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) ⟨t, htH⟩)) =
      (Subgroup.centralizer (secImg (Subgroup.normalizer (L : Set G)) L
        (Subgroup.zpowers t) : Set (SecQuot (Subgroup.normalizer (L : Set G)) L))).subgroupOf
        (Ch3z.chiefMod L N) := by
  classical
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  let A0 : Subgroup G := Subgroup.normalizer (L : Set G)
  let z : SecQuot A0 L := secMk A0 L ⟨t, D14.le_normalizer_of_isNormalIn hstep.2.1 htH⟩
  let n0 : Subgroup.normalizer
      ((Ch3z.chiefMod L N : Subgroup (SecQuot A0 L)) : Set (SecQuot A0 L)) :=
    ⟨z, secMk_mem_normalizer_secImg ((D14.le_normalizer_of_isNormalIn hstep.1) htH)⟩
  have htW_eq : Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) ⟨t, htH⟩ =
      conjAct (Ch3z.chiefMod L N) n0 := rfl
  have hsub : (Subgroup.zpowers t).subgroupOf A0 = Subgroup.zpowers
      ⟨t, D14.le_normalizer_of_isNormalIn hstep.2.1 htH⟩ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, Subtype.ext hn⟩, fun ⟨n, hn⟩ => ⟨n, congrArg Subtype.val hn⟩⟩
  have hδ : secImg A0 L (Subgroup.zpowers t) = Subgroup.zpowers z := by
    change ((Subgroup.zpowers t).subgroupOf A0).map (secMk A0 L) = _
    rw [hsub, MonoidHom.map_zpowers]
  rw [htW_eq, hδ]
  ext w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, mem_fixV_zpowers_iff_apply]
  constructor
  · intro hw y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : ((conjAct (Ch3z.chiefMod L N) n0 w : ↥(Ch3z.chiefMod L N)) :
        SecQuot A0 L) = (w : SecQuot A0 L) :=
      congrArg (fun x : ↥(Ch3z.chiefMod L N) => (x : SecQuot A0 L)) hw
    rw [AutOn.coe_conjAct_apply] at h1
    have hc : z * (w : SecQuot A0 L) = (w : SecQuot A0 L) * z := by
      calc z * (w : SecQuot A0 L) = (z * (w : SecQuot A0 L) * z⁻¹) * z := by group
        _ = (w : SecQuot A0 L) * z := by rw [h1]
    exact (Commute.zpow_left hc j).eq
  · intro hcent
    have hcw : z * (w : SecQuot A0 L) = (w : SecQuot A0 L) * z :=
      hcent _ (Subgroup.mem_zpowers z)
    apply Subtype.ext
    rw [AutOn.coe_conjAct_apply]
    calc z * (w : SecQuot A0 L) * z⁻¹ = ((w : SecQuot A0 L) * z) * z⁻¹ := by rw [hcw]
      _ = (w : SecQuot A0 L) := by group

private theorem index_fixV_zpowers_chiefPsi_eq {H U L N : Subgroup G} {t : G}
    {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (htH : t ∈ H) :
    (@fixV ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Subgroup.zpowers (Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) ⟨t, htH⟩))).index =
      (centralizerMod L N (Subgroup.zpowers t)).relIndex N := by
  rw [fixV_zpowers_chiefPsi_eq (hE := hE) hstep htH]
  change (Subgroup.centralizer (secImg (Subgroup.normalizer (L : Set G)) L
    (Subgroup.zpowers t) : Set (SecQuot (Subgroup.normalizer (L : Set G)) L))).relIndex
      (Ch3z.chiefMod L N) = (centralizerMod L N (Subgroup.zpowers t)).relIndex N
  rw [← Subgroup.inf_relIndex_right
    (Subgroup.centralizer (secImg (Subgroup.normalizer (L : Set G)) L
      (Subgroup.zpowers t) : Set (SecQuot (Subgroup.normalizer (L : Set G)) L)))
    (Ch3z.chiefMod L N), inf_comm]
  exact relIndex_secImg_fix (K := L) (E := N) (X := Subgroup.zpowers t)
    ((Subgroup.zpowers_le.mpr htH).trans (D14.le_normalizer_of_isNormalIn hstep.2.1))
    ((hstep.1.1.trans hUH).trans (D14.le_normalizer_of_isNormalIn hstep.2.1))

private theorem index_fixV_zpowers_chiefPsi_le {H U L N : Subgroup G} {t : G} {Q : ℕ}
    {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)} (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (htH : t ∈ H)
    (hbound : (centralizerMod ⊥ U (Subgroup.zpowers t)).relIndex U ≤ Q) :
    (@fixV ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
      (Subgroup.zpowers (Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) ⟨t, htH⟩))).index ≤ Q := by
  rw [index_fixV_zpowers_chiefPsi_eq (hE := hE) hstep hUH htH]
  exact (relIndex_centralizerMod_le_of_section (Z := ⊥) (Q := U) (Lo := L) (Hi := N)
    (A := Subgroup.zpowers t) bot_le hstep.1.1
    ((hstep.1.1.trans hUH).trans (D14.le_normalizer_of_isNormalIn hstep.2.1))).trans hbound

private theorem quotient_center_statedSU {X : Type} [Group X] [Finite X] {k : ℕ} {F : Type}
    [Field F] [Finite F] (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (e : X ≃* StatedSU 3 (2 ^ k) F) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 k F :=
    ⟨Nat.prime_two, by omega, by rw [hFc, ← pow_mul, Nat.mul_comm]⟩
  have hcenterSU := CFSG.LieType.SemisimpleCentralizers.HeldLang.center_statedSU_eq
    (N := 3) hdat (by norm_num)
  let e2 : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (2 ^ k) F) :=
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥(StatedSU 3 (2 ^ k) F))
      e (Subgroup.map_center_eq e)).trans (QuotientGroup.quotientMulEquivOfEq hcenterSU)
  exact ⟨e2⟩

private theorem quotient_center_statedProj {X : Type} [Group X] [Finite X] {k : ℕ} {F : Type}
    [Field F] [Finite F] (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (e : X ≃* StatedProj (StatedSU 3 (2 ^ k) F)) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  have h2k : 2 < 2 ^ k := by
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hnq : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ k = 2 := by simpa using congrArg Prod.snd h
    rw [h2] at h2k
    norm_num at h2k
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hFc 3
      (by norm_num) hnq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSUq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := k) (F := F) hFc (by norm_num) hnq
  have hnc : ∃ a b : StatedProj (StatedSU 3 (2 ^ k) F), a * b ≠ b * a :=
    CFSG.Quasithin.F6.InspRest.exists_noncomm_statedProj
      (StatedSU 3 (2 ^ k) F) hSUq.1 hsimple
  have hZbot : Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F)) = ⊥ :=
    CFSG.Quasithin.F7Two.center_eq_bot_of_isSimpleGroup hsimple hnc
  let e2 : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (2 ^ k) F) :=
    (QuotientGroup.congr (Subgroup.center X)
      (Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F))) e
      (Subgroup.map_center_eq e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
  exact ⟨e2⟩

private theorem chiefAut_center_quotient {H U L N : Subgroup G} {k : ℕ} {F : Type}
    [Field F] [Finite F] (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hU2 : IsPGroup 2 U) (hqH : IsQuasisimple (oTwoQuot ↥H)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥H ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥H ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    [Nontrivial ↥(Ch3z.chiefAut H L N)] :
    Nonempty (↥(Ch3z.chiefAut H L N) ⧸ Subgroup.center ↥(Ch3z.chiefAut H L N) ≃*
      StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  let Ψ := chiefLift hstep hUH hU2
  have hΨrange : Ψ.range = Ch3z.chiefAut H L N := chiefLift_range hstep hUH hU2
  let ΨL : oTwoQuot ↥H →* ↥(Ch3z.chiefAut H L N) :=
    Ψ.codRestrict _ (fun x => by rw [← hΨrange]; exact ⟨x, rfl⟩)
  have hΨLsurj : Function.Surjective ΨL := by
    intro l
    have hl : (l : MulAut ↥(Ch3z.chiefMod L N)) ∈ Ψ.range := by
      rw [hΨrange]
      exact l.2
    obtain ⟨x, hx⟩ := hl
    exact ⟨x, Subtype.ext hx⟩
  let eC := CFSG.Quasithin.H13.KG14726.quotientCenterEquivOfSurjective hqH ΨL hΨLsurj
  rcases hU3 with hSU | hPSU
  · obtain ⟨e⟩ := hSU
    obtain ⟨e2⟩ := quotient_center_statedSU hk hFc e
    exact ⟨eC.symm.trans e2⟩
  · obtain ⟨e⟩ := hPSU
    obtain ⟨e2⟩ := quotient_center_statedProj hk hFc e
    exact ⟨eC.symm.trans e2⟩

private theorem mem_sup_of_mem_p1_not_mem_q1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {t : G} (htP : t ∈ P1 L1 L2 S)
    (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1) :
    t ∈ L1 ⊔ S := by
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ (Q1 L1 L2 S).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hX2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  exact (str86_le_lhat_of_isPGroup hI hX2).1 (Subgroup.zpowers_le.mpr htP)
    (Subgroup.mem_zpowers t)

private theorem chiefPsi_mem_and_sq {H L N : Subgroup G} {t : G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (htH : t ∈ H) (ht2 : t * t = 1) :
    Ch3z.chiefPsi hHL hHN ⟨t, htH⟩ ∈ Ch3z.chiefAut H L N ∧
      Ch3z.chiefPsi hHL hHN ⟨t, htH⟩ * Ch3z.chiefPsi hHL hHN ⟨t, htH⟩ = 1 := by
  refine ⟨Ch3z.chiefPsi_mem hHL hHN ⟨t, htH⟩, ?_⟩
  have hsq : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = 1 := Subtype.ext (by simpa using ht2)
  calc Ch3z.chiefPsi hHL hHN ⟨t, htH⟩ * Ch3z.chiefPsi hHL hHN ⟨t, htH⟩ =
      Ch3z.chiefPsi hHL hHN (⟨t, htH⟩ * ⟨t, htH⟩) := by rw [map_mul]
    _ = 1 := by rw [hsq, map_one]

private theorem chiefMod_square_eq_one {L N : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (w : ↥(Ch3z.chiefMod L N)) :
    w * w = 1 := by
  apply Subtype.ext
  simpa [pow_two, Subgroup.coe_mul] using hE.2 w w.2

theorem Str86AbHyp.chiefFactor_natural
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L N)
    (hnc : ¬ IsCentralStep (L1 ⊔ S) L N) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) ≤ (2 ^ k) ^ 3) :
    ∃ hE : IsElemAbelian 2 (Ch3z.chiefMod L N),
      @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
        (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k := by
  classical
  let H : Subgroup G := L1 ⊔ S
  let V : Subgroup G := conjClosure (Z2 L1 L2 S) L1
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S :=
    u3LS_pCoreOf (k := k) (F := F) hI.hF hI.hSB h1
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
  obtain ⟨hVQ1, -, -⟩ := str86_conjClosure_frame hI hZQ
  have hVH : V ≤ H := hVQ1.trans (hQ1S.trans le_sup_right)
  have hV2 : IsPGroup 2 V := (pCoreOf_isPGroup 2 H).to_le (hpCoreH.symm ▸ hVQ1)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hVH hV2
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  have hWsq : ∀ w : ↥(Ch3z.chiefMod L N), w * w = 1 := fun w => chiefMod_square_eq_one hE w
  have hqL1 : IsQuasisimple (oTwoQuot ↥L1) :=
    isQuasisimple_oTwoQuot_of_u3 hI.hk hI.hFc hI.hU3
  have hqH : IsQuasisimple (oTwoQuot ↥H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (u3QEquiv hI.hF hI.hSB h1).symm hqL1
  have hqHq : IsSzU3Quot (oTwoQuot ↥H) (2 ^ k) :=
    IsSzU3Quot.of_mulEquiv (u3QEquiv hI.hF hI.hSB h1)
      (Or.inr ⟨k, hI.hk, rfl, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩)
  have htH : t ∈ H := mem_sup_of_mem_p1_not_mem_q1 hI htP htQ ht2
  have htO : t ∉ pCoreOf 2 H := by simpa [hpCoreH] using htQ
  let tW : MulAut ↥(Ch3z.chiefMod L N) := Ch3z.chiefPsi hHL hHN ⟨t, htH⟩
  obtain ⟨htWmem, htW2⟩ := chiefPsi_mem_and_sq hHL hHN htH ht2
  have htWne : tW ≠ 1 := chiefPsi_ne_one hstep hVH hV2 hnc htH ht2 htO hqHq
  haveI : Nontrivial ↥(Ch3z.chiefAut H L N) :=
    ⟨⟨⟨tW, htWmem⟩, 1, fun h => htWne (congrArg Subtype.val h)⟩⟩
  have hperf : Group.IsPerfect ↥(Ch3z.chiefAut H L N) :=
    chiefAut_perfect hstep hVH hV2 hqH
  have hirr : ∀ W : Subgroup ↥(Ch3z.chiefMod L N),
      (∀ g ∈ Ch3z.chiefAut H L N, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    chiefAut_irreducible hstep hVH
  have hU3H : Nonempty (oTwoQuot ↥H ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥H ≃* StatedProj (StatedSU 3 (2 ^ k) F)) :=
    u3HQU3 hI.hF hI.hSB hI.hU3 h1
  have hcenter := chiefAut_center_quotient hstep hVH hV2 hqH hI.hk hI.hFc hU3H
  have hbound : (centralizerMod ⊥ V (Subgroup.zpowers t)).relIndex V ≤ (2 ^ k) ^ 3 := by
    rw [centralizerMod_bot_eq, Subgroup.inf_relIndex_left]
    exact hdisp
  have hidx := index_fixV_zpowers_chiefPsi_le (hE := hE) hstep hVH htH hbound
  have hidx' : (fixV (Subgroup.zpowers tW)).index ≤ 2 ^ (3 * k) := by
    calc (fixV (Subgroup.zpowers tW)).index ≤ (2 ^ k) ^ 3 := by simpa only [tW] using hidx
      _ = 2 ^ (3 * k) := by rw [← pow_mul, Nat.mul_comm]
  exact ⟨hE, @u3NaturalOfSmallDisplacement_holds k hI.hk F _ _ hI.hFc
    ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE) _ hWsq
    (Ch3z.chiefAut H L N) hperf hirr hcenter ⟨tW, htWmem, htW2, htWne, hidx'⟩⟩

end CFSG.Quasithin.Stroth

end
