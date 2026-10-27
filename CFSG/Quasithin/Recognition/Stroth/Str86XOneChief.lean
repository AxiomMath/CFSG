module

public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.H13.KG14726Elim
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni
public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.Quasithin.Vol2.Ch3E215MH
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Recognition.Stroth.Str86XOne3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem index_fixV_zpowers_le_card {V : Type*} [CommGroup V] [Finite V] (t : MulAut V)
    (S : Subgroup V) (hS : ∀ v : V, t v * v⁻¹ ∈ S) :
    (fixV (Subgroup.zpowers t)).index ≤ Nat.card S := by
  classical
  let φ : V →* V :=
    { toFun := fun v => t v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm b⁻¹ a⁻¹]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : φ.ker = fixV (Subgroup.zpowers t) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_apply]
    change t v * v⁻¹ = 1 ↔ t v = v
    rw [mul_inv_eq_one]
  have hrange : φ.range ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hS v
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_of_le hrange

theorem str86_X1_chiefFactor_natural
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (u3X1 L1 L2 S) L N)
    (hnc : ¬ IsCentralStep (L1 ⊔ S) L N) (hZL : Z1 L1 L2 S ⊓ N ≤ L) :
    ∃ hE : IsElemAbelian 2 (Ch3z.chiefMod L N),
      @BinaryNaturalSU3 ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE)
        (Ch3z.chiefAut (L1 ⊔ S) L N) ⊤ ⊥ k := by
  classical
  let H : Subgroup G := u3LS L1 L2 S
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hX1H : u3X1 L1 L2 S ≤ H :=
    u3X1_le_q1.trans
      ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)).trans le_sup_right)
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hX1H).trans hHL
  have hLN : L ≤ N := hstep.2.2.1.le
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S :=
    u3LS_pCoreOf (k := k) (F := F) hF hSB h1
  have hX1P : IsPGroup 2 ↥(u3X1 L1 L2 S) :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le u3X1_le_q1
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hX1H hX1P
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  have hWsq : ∀ w : ↥(Ch3z.chiefMod L N), w * w = 1 := fun w => by
    apply Subtype.ext
    simpa [pow_two, Subgroup.coe_mul] using hE.2 w w.2
  have hker : pCore 2 ↥H ≤ (Ch3z.chiefHom hHL hHN).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    have hgH : ((g : ↥H) : G) ∈ pCoreOf 2 H := (F1.mem_pCore_iff_coe (H := H) g).mp hg
    exact (Ch3z.chiefHom_eq_one_iff hHL hHN hNL g).mpr
      (Ch3z.pCoreOf_le_centralizerMod hX1H hstep hE hgH)
  have hkerPsi : pCore 2 ↥H ≤ (Ch3z.chiefPsi hHL hHN).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    have h1 : Ch3z.chiefHom hHL hHN g = 1 := MonoidHom.mem_ker.mp (hker hg)
    simpa [Ch3z.chiefHom] using congrArg Subtype.val h1
  let Ψ : oTwoQuot ↥H →* MulAut ↥(Ch3z.chiefMod L N) :=
    QuotientGroup.lift (pCore 2 ↥H) (Ch3z.chiefPsi hHL hHN) hkerPsi
  have hΨrange : Ψ.range = Ch3z.chiefAut H L N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) y
      show (QuotientGroup.lift (pCore 2 ↥H) (Ch3z.chiefPsi hHL hHN) hkerPsi)
        ((QuotientGroup.mk' (pCore 2 ↥H)) g) ∈ Ch3z.chiefAut H L N
      rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
      exact (Ch3z.chiefHom hHL hHN g).2
    · intro hx
      obtain ⟨g, hg⟩ := Ch3z.chiefHom_surjective hHL hHN ⟨x, hx⟩
      refine ⟨QuotientGroup.mk' (pCore 2 ↥H) g, ?_⟩
      show (QuotientGroup.lift (pCore 2 ↥H) (Ch3z.chiefPsi hHL hHN) hkerPsi)
        ((QuotientGroup.mk' (pCore 2 ↥H)) g) = x
      rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
      exact congrArg Subtype.val hg
  have hqL1 : IsQuasisimple (oTwoQuot ↥L1) := isQuasisimple_oTwoQuot_of_u3 hk hFc hU3
  have hqH : IsQuasisimple (oTwoQuot ↥H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (u3QEquiv hF hSB h1).symm hqL1
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hqH.1
  have hperf : Group.IsPerfect ↥(Ch3z.chiefAut H L N) := by
    have h := Group.IsPerfect.range Ψ
    rwa [hΨrange] at h
  have hirr : ∀ U : Subgroup ↥(Ch3z.chiefMod L N),
      (∀ g ∈ Ch3z.chiefAut H L N, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => Ch3z.chiefMod_irr hstep hX1H U hU
  obtain ⟨z, hzZ2, hzQ1⟩ := Set.not_subset.mp hZQ
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))
  have hzH : z ∈ H := (le_sup_right : S ≤ H) (hZ2S hzZ2)
  have hz2 : z * z = 1 := by
    have := (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hzZ2
    simpa [pow_two] using this
  let zH : ↥H := ⟨z, hzH⟩
  let t : ↥(Ch3z.chiefAut H L N) := Ch3z.chiefHom hHL hHN zH
  have htcoe : (t : MulAut ↥(Ch3z.chiefMod L N)) = Ch3z.chiefPsi hHL hHN zH := rfl
  have ht2 : t * t = 1 := by
    show Ch3z.chiefHom hHL hHN zH * Ch3z.chiefHom hHL hHN zH = 1
    rw [← map_mul, show zH * zH = 1 from Subtype.ext (by simpa using hz2), map_one]
  have hqHq : IsSzU3Quot (oTwoQuot ↥H) (2 ^ k) :=
    IsSzU3Quot.of_mulEquiv (u3QEquiv hF hSB h1)
      (Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩)
  have hKnorm : H ≤ Subgroup.normalizer (centralizerMod L H N : Set G) := by
    have hKsub : (centralizerMod L H N).subgroupOf H = (Ch3z.chiefHom hHL hHN).ker := by
      ext g
      rw [Subgroup.mem_subgroupOf, ← Ch3z.chiefHom_eq_one_iff hHL hHN hNL g,
        MonoidHom.mem_ker]
    have hN : ((centralizerMod L H N).subgroupOf H).Normal := by
      rw [hKsub]
      exact MonoidHom.normal_ker _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := centralizerMod L H N) (K := H) (fun x hx => hx.1)).mp hN
  have htne : t ≠ 1 := by
    intro ht1
    have hzK : z ∈ centralizerMod L H N :=
      (Ch3z.chiefHom_eq_one_iff hHL hHN hNL zH).mp ht1
    have hQK : pCoreOf 2 H ≤ centralizerMod L H N :=
      Ch3z.pCoreOf_le_centralizerMod hX1H hstep hE
    rcases eq_or_mem_pCoreOf_of_normal (H := H) (K := centralizerMod L H N) hqHq
      (fun x hx => hx.1) hKnorm hQK with hKH | h2el
    · refine hnc (fun g hg x hx => ?_)
      have hg' : g ∈ centralizerMod L H N := by
        rw [hKH]
        exact hg
      exact hg'.2.2 x hx
    · have hzpow : z ^ 2 ^ 1 = 1 := by
        simpa only [pow_one, pow_two] using hz2
      have hzpc : z ∈ pCoreOf 2 H := h2el z hzK ⟨1, hzpow⟩
      rw [hpCoreH] at hzpc
      exact hzQ1 hzpc
  haveI : Nontrivial ↥(Ch3z.chiefAut H L N) := ⟨⟨t, 1, htne⟩⟩
  have hcenter : Nonempty (↥(Ch3z.chiefAut H L N) ⧸
      Subgroup.center ↥(Ch3z.chiefAut H L N) ≃*
        StatedProj (StatedSU 3 (2 ^ k) F)) := by
    let ΨL : oTwoQuot ↥H →* ↥(Ch3z.chiefAut H L N) :=
      Ψ.codRestrict _ (fun x => by rw [← hΨrange]; exact ⟨x, rfl⟩)
    have hΨLsurj : Function.Surjective ΨL := by
      intro l
      have hl : (l : MulAut ↥(Ch3z.chiefMod L N)) ∈ Ψ.range := by
        rw [hΨrange]
        exact l.2
      obtain ⟨x, hx⟩ := hl
      exact ⟨x, Subtype.ext hx⟩
    let eC : oTwoQuot ↥H ⧸ Subgroup.center (oTwoQuot ↥H) ≃*
        ↥(Ch3z.chiefAut H L N) ⧸ Subgroup.center ↥(Ch3z.chiefAut H L N) :=
      CFSG.Quasithin.H13.KG14726.quotientCenterEquivOfSurjective hqH ΨL hΨLsurj
    let eQ : oTwoQuot ↥H ≃* oTwoQuot ↥L1 := u3QEquiv hF hSB h1
    let e1 : oTwoQuot ↥H ⧸ Subgroup.center (oTwoQuot ↥H) ≃*
        oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) :=
      QuotientGroup.congr (Subgroup.center (oTwoQuot ↥H))
        (Subgroup.center (oTwoQuot ↥L1)) eQ (Subgroup.map_center_eq eQ)
    have h2k : 2 < 2 ^ k := by
      calc (2 : ℕ) < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hnq : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
      intro h
      have h2 : 2 ^ k = 2 := by simpa using congrArg Prod.snd h
      rw [h2] at h2k
      norm_num at h2k
    rcases hU3 with hSU | hPSU
    · obtain ⟨eSU⟩ := hSU
      have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 k F :=
        ⟨Nat.prime_two, by omega, by rw [hFc, ← pow_mul, Nat.mul_comm]⟩
      have hcenterSU := CFSG.LieType.SemisimpleCentralizers.HeldLang.center_statedSU_eq
        (N := 3) hdat (by norm_num)
      let e2 : oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) ≃*
          StatedProj (StatedSU 3 (2 ^ k) F) :=
        (QuotientGroup.congr (Subgroup.center (oTwoQuot ↥L1))
          (Subgroup.center ↥(StatedSU 3 (2 ^ k) F)) eSU (Subgroup.map_center_eq eSU)).trans
          (QuotientGroup.quotientMulEquivOfEq hcenterSU)
      exact ⟨eC.symm.trans (e1.trans e2)⟩
    · obtain ⟨ePSU⟩ := hPSU
      have hsimplePSU : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hFc 3
          (by norm_num) hnq
      have hqPSU : IsQuasisimple (StatedProj (StatedSU 3 (2 ^ k) F)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv ePSU hqL1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hSUq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (p := 2) (f := k) (F := F) hFc (by norm_num) hnq
      have hncPSU : ∃ a b : StatedProj (StatedSU 3 (2 ^ k) F), a * b ≠ b * a :=
        CFSG.Quasithin.F6.InspRest.exists_noncomm_statedProj
          (StatedSU 3 (2 ^ k) F) hSUq.1 hsimplePSU
      have hZbot : Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F)) = ⊥ :=
        CFSG.Quasithin.F7Two.center_eq_bot_of_isSimpleGroup hsimplePSU hncPSU
      let e2 : oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) ≃*
          StatedProj (StatedSU 3 (2 ^ k) F) :=
        (QuotientGroup.congr (Subgroup.center (oTwoQuot ↥L1))
          (Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F))) ePSU
          (Subgroup.map_center_eq ePSU)).trans
          ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
      exact ⟨eC.symm.trans (e1.trans e2)⟩
  let Y : Subgroup G := u3Y L1 L2 S
  have hZ1Y : Z1 L1 L2 S ≤ Y := u3Z1_le_u3Y hF hSB h1 hB2 h2 hZI
  have hYcard : Nat.card ↥Y = (2 ^ k) ^ 3 := by
    simpa [Y, u3Y] using hY
  let tW : MulAut ↥(Ch3z.chiefMod L N) := (t : MulAut ↥(Ch3z.chiefMod L N))
  have htWmem : tW ∈ Ch3z.chiefAut H L N := t.2
  have htW2 : tW * tW = 1 := congrArg Subtype.val ht2
  have htWne : tW ≠ 1 := fun h => htne (Subtype.ext h)
  let Simg : Subgroup ↥(Ch3z.chiefMod L N) :=
    ((N ⊓ Y).subgroupOf N).map (Ch3z.chiefIota hNL)
  have hS : ∀ w : ↥(Ch3z.chiefMod L N), tW w * w⁻¹ ∈ Simg := by
    intro w
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL w
    have hzn : z * (n : G) * z⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hHN hzH) (n : G)).mp n.2
    have hstep1 : tW (Ch3z.chiefIota hNL n) =
        Ch3z.chiefIota hNL ⟨z * n * z⁻¹, hzn⟩ := by
      rw [show tW = Ch3z.chiefPsi hHL hHN zH from htcoe]
      exact Ch3z.chiefPsi_iota hHL hHN hNL zH n hzn
    rw [hstep1]
    have hstep2 : Ch3z.chiefIota hNL ⟨z * n * z⁻¹, hzn⟩ * (Ch3z.chiefIota hNL n)⁻¹ =
        Ch3z.chiefIota hNL (⟨z * n * z⁻¹, hzn⟩ * n⁻¹) := by
      rw [← map_inv, ← map_mul]
    rw [hstep2]
    refine Subgroup.mem_map.mpr ⟨⟨z * n * z⁻¹, hzn⟩ * n⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨(⟨z * n * z⁻¹, hzn⟩ * n⁻¹ : ↥N).property, ?_⟩
    have hnQ1 : ((n : G)) ∈ Q1 L1 L2 S := u3X1_le_q1 (hstep.1.1 n.2)
    have hcomm := u3_commutator_q1_z2_le_u3Y (L1 := L1) (L2 := L2) (S := S) hF
      (Subgroup.commutator_mem_commutator hnQ1 hzZ2)
    have hinv := (u3Y L1 L2 S).inv_mem hcomm
    have heq : ((⟨z * n * z⁻¹, hzn⟩ * n⁻¹ : ↥N) : G) = ⁅(n : G), z⁆⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [heq]
    exact hinv
  have hSimgcard : Nat.card Simg ≤ (2 ^ k) ^ 2 := by
    have hkerIota : (Ch3z.chiefIota hNL).ker = L.subgroupOf N := by
      ext x
      rw [MonoidHom.mem_ker, Ch3z.chiefIota_eq_one_iff, Subgroup.mem_subgroupOf]
    have hNY : N ⊓ Y ≤ N := inf_le_left
    have hcard1 : Nat.card Simg = L.relIndex (N ⊓ Y) := by
      rw [show Simg = ((N ⊓ Y).subgroupOf N).map (Ch3z.chiefIota hNL) from rfl,
        ← Ch3E215M.card_map_eq_relIndex_ker, hkerIota, Subgroup.relIndex_subgroupOf hNY]
    have hcard2 : L.relIndex (N ⊓ Y) ≤ (Z1 L1 L2 S ⊓ N).relIndex (N ⊓ Y) := by
      have heq : (L ⊓ Y).subgroupOf (N ⊓ Y) = L.subgroupOf (N ⊓ Y) := by
        ext x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · rintro ⟨hx, -⟩
          exact hx
        · intro hx
          exact ⟨hx, (Subgroup.mem_inf.mp x.2).2⟩
      have h1 : L.relIndex (N ⊓ Y) = (L ⊓ Y).relIndex (N ⊓ Y) := by
        show (L.subgroupOf (N ⊓ Y)).index = ((L ⊓ Y).subgroupOf (N ⊓ Y)).index
        rw [heq]
      rw [h1]
      refine Subgroup.relIndex_le_of_le_left (H := Z1 L1 L2 S ⊓ N) (K := L ⊓ Y)
        (L := N ⊓ Y) (le_inf hZL (inf_le_left.trans hZ1Y)) ?_
      show ((Z1 L1 L2 S ⊓ N).subgroupOf (N ⊓ Y)).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    have hcard3 : (Z1 L1 L2 S ⊓ N).relIndex (N ⊓ Y) =
        (Z1 L1 L2 S).relIndex (N ⊓ Y) := by
      have heq : (Z1 L1 L2 S ⊓ N).subgroupOf (N ⊓ Y) =
          (Z1 L1 L2 S).subgroupOf (N ⊓ Y) := by
        ext x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · rintro ⟨hx, -⟩
          exact hx
        · intro hx
          exact ⟨hx, (Subgroup.mem_inf.mp x.2).1⟩
      show ((Z1 L1 L2 S ⊓ N).subgroupOf (N ⊓ Y)).index =
        ((Z1 L1 L2 S).subgroupOf (N ⊓ Y)).index
      rw [heq]
    have hcard4 : (Z1 L1 L2 S).relIndex (N ⊓ Y) ≤ (Z1 L1 L2 S).relIndex Y := by
      refine Subgroup.relIndex_le_of_le_right (H := Z1 L1 L2 S) (K := N ⊓ Y) (L := Y)
        inf_le_right ?_
      show ((Z1 L1 L2 S).subgroupOf Y).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    have hcard5 : (Z1 L1 L2 S).relIndex Y = (2 ^ k) ^ 2 := by
      have hmul := Subgroup.relIndex_mul_card (H := Z1 L1 L2 S) (K := Y)
      have hinf : Z1 L1 L2 S ⊓ Y = Z1 L1 L2 S := inf_of_le_left hZ1Y
      rw [hinf, show Nat.card ↥(Z1 L1 L2 S) = 2 ^ k from hZ1, hYcard] at hmul
      have hpos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
      rw [show (2 ^ k) ^ 3 = (2 ^ k) ^ 2 * 2 ^ k by ring] at hmul
      exact Nat.eq_of_mul_eq_mul_right hpos hmul
    calc Nat.card Simg = L.relIndex (N ⊓ Y) := hcard1
      _ ≤ (Z1 L1 L2 S ⊓ N).relIndex (N ⊓ Y) := hcard2
      _ = (Z1 L1 L2 S).relIndex (N ⊓ Y) := hcard3
      _ ≤ (Z1 L1 L2 S).relIndex Y := hcard4
      _ = (2 ^ k) ^ 2 := hcard5
  have hidx : (fixV (Subgroup.zpowers tW)).index ≤ 2 ^ (3 * k) := by
    refine (index_fixV_zpowers_le_card tW Simg hS).trans ?_
    refine hSimgcard.trans ?_
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨hE, @u3NaturalOfSmallDisplacement_holds k hk F _ _ hFc
    ↥(Ch3z.chiefMod L N) (commGroupOfElemAbelian hE) _ hWsq
    (Ch3z.chiefAut H L N) hperf hirr hcenter ⟨tW, htWmem, htW2, htWne, hidx⟩⟩

end CFSG.Quasithin.Stroth
