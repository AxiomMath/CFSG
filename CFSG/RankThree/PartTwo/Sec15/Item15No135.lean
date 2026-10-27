module

public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec15.Item156Proof
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec15.Item15Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eq_deltaZero_of_eq_delta' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYres : Y = oPrimeResidualOf 3 Y)
    (hYdelta : Y = delta A (lB A) Y) : Y = deltaZero A (lB A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdelta, -, hnorm⟩ := rank3II_14_5_of' h134 hJ2 h48 h415 hJ2c h hAY
  set D := deltaZero A (lB A) Y with hD
  set C' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC'
  have hYeq : Y = D ⊔ C' := hYdelta.trans hdelta
  have hYN : Y ≤ Subgroup.normalizer (D : Set G) := hYdelta.le.trans hnorm
  have hDY : D ≤ Y := deltaZero_le Y
  have hC'N : C' ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hYN
  have hN : (D.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).mpr hYN
  have hcop : Nat.Coprime 3 (Nat.card C') :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  have key : ∀ x : Y, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ D.subgroupOf Y := by
    rintro x ⟨k, hk⟩
    have hx : (x : G) ∈ ((D : Set G) * (C' : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left D C' hC'N, ← hYeq]
      exact x.2
    obtain ⟨d, hd, c, hc, hdc⟩ := hx
    have hcY : c ∈ Y := (Subgroup.mem_inf.mp hc).2
    have hdY : d ∈ Y := hDY hd
    let π : Y →* Y ⧸ D.subgroupOf Y := QuotientGroup.mk' (D.subgroupOf Y)
    have hπd : π ⟨d, hdY⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mpr (Subgroup.mem_subgroupOf.mpr hd)
    have hπx : π x = π ⟨c, hcY⟩ := by
      have hxdc : x = ⟨d, hdY⟩ * ⟨c, hcY⟩ := Subtype.ext hdc.symm
      rw [hxdc, map_mul, hπd, one_mul]
    have hc1 : (⟨c, hcY⟩ : Y) ^ Nat.card C' = 1 := by
      have h : (⟨c, hc⟩ : C') ^ Nat.card C' = 1 := pow_card_eq_one'
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h' ⊢
      exact h'
    have h1 : π x ^ Nat.card C' = 1 := by rw [hπx, ← map_pow, hc1, map_one]
    have h2 : π x ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hord : orderOf (π x) = 1 := Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1))
    rw [orderOf_eq_one_iff] at hord
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mp hord
  have hres : oPrimeResidualOf 3 Y ≤ D := by
    unfold oPrimeResidualOf oPrimeResidual
    rw [← Subgroup.map_subgroupOf_eq_of_le hDY]
    exact Subgroup.map_mono ((Subgroup.closure_le _).mpr fun x hx => key x hx)
  exact le_antisymm (hYres.le.trans hres) hDY

theorem exists_hj_of_sl25'
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {Y M X : Subgroup G} (hctx : Ctx152 A (lB A) Y M X) :
    ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      deltaZero A (lB A) X = pPrimeCoreOf 3 (deltaZero A (lB A) X) ⊔
        deltaZero A (lB A) (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ∧
      ∃ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have hX := hctx.mem_comp
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h' => hctx.mem_y2.1.1 (top_le_iff.mp (h' ▸ hXM))
  have hXY : X ∈ scriptY A := ⟨hXtop, hctx.norm_x⟩
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  have hθ : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 ∧
      CFSG.pPrimeCore 3 ↥X = aschbacherSolvableCore 3 ↥X := by
    rcases hctx.sl25 with he | he
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
  obtain ⟨h60, hcore⟩ := hθ
  have hY1 := ne_bot_of_mem_scriptY4 hctx.mem_y4
  have hX3 : X = oPrimeResidualOf 3 X := eq_oPrimeResidualOf_of_le hXp hXq hctx.le_x
    hctx.mem_y4.2.1 (isPerfect_of_mem_scriptY4 hctx.mem_y4) hY1
  have hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
  have hXΔ0 : X = deltaZero A (lB A) X :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415 hJ2c h hctx.norm_x hX3
      hctx.delta_x
  let := ker148_normal hXY.2
  obtain ⟨ψ⟩ := nonempty_img148_equiv hXY.2
  have he : Nonempty (↥(img148 A X (deltaZero A (lB A) X)) ≃*
      ↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [← hXΔ0]
    exact ⟨ψ.trans (QuotientGroup.quotientMulEquivOfEq hcore)⟩
  obtain ⟨e⟩ := he
  have hqI : IsQuasisimple ↥(img148 A X (deltaZero A (lB A) X)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hXq
  have hcardI : Nat.card ↥(img148 A X (deltaZero A (lB A) X)) = 60 ∨
      Nat.card ↥(img148 A X (deltaZero A (lB A) X)) = 1080 := by
    left
    rw [Nat.card_congr e.toEquiv]
    exact h60
  exact exists_hj_of_img148 h148 hXY h.toSec13Data.isElemAbelian.1 h.chosen136 hqI hcardI

theorem rank3II_15_2_of'
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h44 : Sec4.Item4_4) (h148 : Item148 A (lB A)) (h1411 : Item1411_1 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : StellmacherKP) (hcomp : Step152Comp A (lB A))
    (hexcl : Step152Excl A (lB A)) (hconf : Step152Conf A (lB A)) (hgen : KS152HJGen)
    (hend : Step152End A (lB A)) : Item152 A (lB A) := by
  intro Y hY M hM hYM hF
  obtain ⟨X, hX, hYX, hΔ⟩ := hcomp Y hY M hM hYM hF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  by_cases hq : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)
  · exact ⟨X, hX, hYX, mem_scriptY0_of_isQuasisimple hY hM hF hX hYX hAX hΔ hq⟩
  ·
    exfalso
    have hsl := (isQuasisimple_or_isSL25Case h.toTheoremFourHyp h44 hexcl hY hM hYM hF hX hYX
      hΔ).resolve_left hq
    have hctx : Ctx152 A (lB A) Y M X := ⟨hY, hM, hYM, hF, hX, hYX, hAX, hΔ, hsl, hq⟩
    obtain ⟨c', hc', hdec, L', hL', hJ⟩ := exists_hj_of_sl25' h h148 h134 h48 h415 hctx
    obtain ⟨d, p, P, T, K, S, hD⟩ := hconf Y M X hctx c' L' hc' hL' hJ hdec
    have hSG := hD.mem_scriptQPiStar_top hst h.isSimpleGroup
    have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hD.norm_w h1411 hSG
    have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hD.omega, mem_lA := hD.mem_lA }
    exact hend Y M X hctx c' L' d p P T K S hD hSH
      (hgen G A c' L' h' Y M X hctx d p P T K S hD hSH)

theorem exists_data156_of_small'
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hD : Step156D A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (htype : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))) :
    ∃ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A (lB A) Y c₀ L₀ d X₁ := by
  have hY0 : Y ∈ scriptY0 A (lB A) := hY.prop
  have hY4 : Y ∈ scriptY4 A (lB A) := hY0.1
  have hYY : Y ∈ scriptY A := hY4.1
  have hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
  have hYΔ : Y = deltaZero A (lB A) Y :=
    rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415 hJ2c h hY4
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY4.2.2.2
  have hcardQ : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 60 ∨
      Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 1080 := by
    rcases htype with he | h6
    · obtain ⟨e⟩ := he
      left
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    · right
      rw [card_of_isTripleCover h6, card_alternatingGroup_six]
  have hZ3 : IsPGroup 3 (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
    rcases htype with he | h6
    · obtain ⟨e⟩ := he
      have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
      have hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := e.isSimpleGroup
      have hnab : ∃ a b : ↥Y ⧸ CFSG.pCore 2 ↥Y, a * b ≠ b * a := by
        obtain ⟨-, -, a, b, hab⟩ := hq
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        refine ⟨a, b, fun h => hab ?_⟩
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
      rw [center_eq_bot_of_isSimpleGroup hs hnab]
      exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1) (by rw [h6.1, pow_one])
  have h3 : 3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rcases hcardQ with h | h <;> rw [h] <;> norm_num
  have hcore : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isQuasisimple hq h3 hZ3)
  let := ker148_normal hYY.2
  obtain ⟨ψ⟩ := nonempty_img148_equiv hYY.2
  have he : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [← hYΔ]
    exact ⟨ψ.trans (QuotientGroup.quotientMulEquivOfEq hcore)⟩
  obtain ⟨e⟩ := he
  have hqI : IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hcardI : Nat.card ↥(img148 A Y (deltaZero A (lB A) Y)) = 60 ∨
      Nat.card ↥(img148 A Y (deltaZero A (lB A) Y)) = 1080 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcardQ
  obtain ⟨c₀, hc₀, hdec, L₀, hL₀, hJ⟩ :=
    exists_hj_of_img148 h148 hYY h.isElemAbelian.1 h.chosen136 hqI hcardI
  have hO : pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y := by
    rw [pPrimeCoreOf, hcore, CFSG.Open.pCoreOf]
  have hcY := mem_sectionCentralizer_of_eq_sup h.isE27 (Subgroup.zpowers_le.mp hc₀.1) hYY.2
    hYΔ hdec hO
  obtain ⟨d, hdA, hd1, hdL, hcent⟩ := hD Y hY htype c₀ L₀ hc₀ hL₀ hJ hcY
  exact ⟨c₀, L₀, d, Y, ⟨hc₀, hL₀, hJ, hY0, le_rfl, htype, hdA, hd1, hdL, hcent,
    Or.inr (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).symm⟩⟩

end CFSG.RankThree.PartTwo.Sec15
