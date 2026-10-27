module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
public import CFSG.RankThree.PartTwo.Sec15.Wales154HJ
import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Uniq
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
public import CFSG.RankThree.PartTwo.Sec15.Wales154When

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_card_nine_trivial {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J : Subgroup G} (hO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥)
    {E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hBtriv : ∀ b ∈ B, ∀ y ∈ J, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hBJ1 : B ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro b ⟨hbB, hbJ⟩
    have hb3 : b ^ 3 = 1 := hAe.2 b (hBA hbB)
    set bJ : ↥J := ⟨b, hbJ⟩ with hbJdef
    have hZb : QuotientGroup.mk' (CFSG.pCore 2 ↥J) bJ ∈
        Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) z
      have h1 : ((bJ * y * bJ⁻¹ * y⁻¹ : ↥J) : G) ∈ CFSG.Open.pCoreOf 2 J := by
        simpa [hbJdef] using hBtriv b hbB y y.2
      have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      show (y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) =
        (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J)
      calc (y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) =
          (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J) *
            (bJ : ↥J ⧸ CFSG.pCore 2 ↥J)⁻¹ * (y : ↥J ⧸ CFSG.pCore 2 ↥J)⁻¹ *
            ((y : ↥J ⧸ CFSG.pCore 2 ↥J) * (bJ : ↥J ⧸ CFSG.pCore 2 ↥J)) := by
            rw [h2, one_mul]
        _ = (bJ : ↥J ⧸ CFSG.pCore 2 ↥J) * (y : ↥J ⧸ CFSG.pCore 2 ↥J) := by group
    rw [hZ, Subgroup.mem_bot] at hZb
    have hbO : b ∈ CFSG.Open.pCoreOf 2 J :=
      (Proof156Res4.mem_pCoreOf_iff_mk_eq_one bJ).mpr hZb
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J) ⟨b, hbO⟩
    have hb2 : b ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hco : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
    have h1 := (pow_gcd_eq_one (a := b)).mpr ⟨hb2, hb3⟩
    rw [hco.gcd_eq_one, pow_one] at h1
    exact Subgroup.mem_bot.mpr h1
  exact Proof155w3.false_of_le_E9_of_trivial h hO hBA hB9 (hBA.trans hAJ) hBtriv hBJ1 hE hE9

omit [Finite G] in
theorem mem_centralizerSection_of_trivial {Y : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (htriv : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) :
    x ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y) := by
  refine ⟨hx, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hx, fun y hy => ?_⟩
  have e : ⁅y, x⁆ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact inv_mem (htriv y hy)

omit [Finite G] in
theorem trivial_of_mem_centralizerSection {Y : Subgroup G} {x : G}
    (hx : x ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) :
    ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  intro y hy
  have e : x * y * x⁻¹ * y⁻¹ = (⁅y, x⁆)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact inv_mem (hx.2.2 y hy)

theorem pPrimeCoreOf_eq_pCoreOf {Y : Subgroup G}
    (heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y) :
    pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y := by
  rw [pPrimeCoreOf, CFSG.Open.pCoreOf, heq]

theorem pPrimeCore_eq_pCore_of_center_eq_bot {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y : Subgroup G} (hY : Y ∈ scriptY4 A LB)
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) :
    CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
  Proof1515.pPrimeCore_three_eq_pCore_two_of hY.2.2.2
    (Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY) fun Z _ hZc _ _ => by
      rw [hZ] at hZc
      exact le_bot_iff.mp hZc

omit [Finite G] in
theorem not_isTripleCover_of_j2
    {X : Type} {S : Type*}
    [Group X] [Finite X] [Group S] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ Sec4.IsTripleCover X S := by
  rintro ⟨h3, -⟩
  rw [KFacts.KS14.Native.center_eq_bot_of_j2 hX, Subgroup.card_bot] at h3
  omega

theorem point_of_j2
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    AllPointsHJ A ∧ ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      ∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  obtain ⟨φ⟩ := hJ
  have hZ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φ⟩
  have heq := pPrimeCore_eq_pCore_of_center_eq_bot hY hZ
  set e3 : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2 :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans φ
  have hO := pPrimeCoreOf_eq_pCoreOf heq
  have hJ3 : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) := ⟨e3⟩
  have hc := Nat.card_congr e3.toEquiv
  rw [KFacts.KS14.card_nativeJ2] at hc
  by_cases hHJ : AllPointsHJ A
  · refine ⟨hHJ, ?_⟩
    rcases read154_hj h148 h134 h48 hR hHJ hY with ⟨c', hc', htriv, -⟩ | h6 | ⟨⟨φ5⟩⟩ | hON |
        ⟨⟨φ7⟩⟩ | ⟨_, ⟨φL⟩⟩
    · exact ⟨c', hc', hO ▸ htriv⟩
    · exact (not_isTripleCover_of_j2 hJ3 h6).elim
    · rw [Nat.card_congr φ5.toEquiv, Sec15.card_alternatingGroup_five] at hc
      omega
    · exact (not_isTripleCover_of_j2 hJ3 hON).elim
    · exact (KFacts.KS14.ks17J2NotList.2.1.false (e3.symm.trans φ7)).elim
    · exact (KFacts.KS14.not_isLThreeEpsAt_j2 7 1 (Or.inl ⟨e3.symm.trans φL⟩)).elim
  · exfalso
    rcases read154_nhj h148 h134 h48 hR hHJ hY with
      ⟨c', hc', -, L', hL', ⟨⟨φ1⟩⟩ | ⟨-, ⟨φ7⟩⟩ | ⟨p, f, e, hp, -, -, -, hε⟩⟩ | ⟨φ10⟩ |
        ⟨-, -, n, m, -, -, hn, -, hiso, -⟩
    · exact hHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' ⟨φ1.symm.trans e3⟩)
    · exact KFacts.KS14.ks17J2NotList.2.1.false (e3.symm.trans φ7)
    · exact KFacts.KS14.not_isLThreeEpsAt_j2 p f (IsLThreeEpsAt.of_mulEquiv e3 hε)
    · obtain ⟨φ10⟩ := φ10
      rw [Nat.card_congr φ10.toEquiv, Sec15.card_alternatingGroup_ten] at hc
      omega
    · exact KFacts.KS14.ks17J2NotList.1 2 (3 * n) (Proof155w3.isoLThreePi_of_mulEquiv e3 hiso)

section Dclause


theorem not_mem_centralizerSection_of_threeCentral (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hYO : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A)
    (htriv : ∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    d ∉ centralizerSection Y (CFSG.Open.pCoreOf 2 Y) := by
  intro hdC
  have hA := hR.toSec14Std.isE27'
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hR.toSec13Data.isElemAbelian
  obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
  have hc'1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'3
    omega
  by_cases hdc' : d ∈ Subgroup.zpowers c'
  ·
    apply Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48 hR.toSec14Std hJL hdA hd1 hdc
    have hd3 : orderOf d = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (hAe.2 d hdA) hd1
    have hle : Subgroup.zpowers d ≤ Subgroup.zpowers c' := Subgroup.zpowers_le.mpr hdc'
    have heq : Subgroup.zpowers d = Subgroup.zpowers c' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc'3, Nat.card_zpowers, hd3])
    rw [heq]
    exact hc'
  · obtain ⟨φ⟩ := hJ
    have hZ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φ⟩
    obtain ⟨E, hE, hE9⟩ := Proof155w3.exists_elemAbelian_nine_of_j2 ⟨φ⟩
    set B := Subgroup.closure ({c', d} : Set G) with hBdef
    have hB9 : Nat.card B = 9 :=
      Sec4.Item424Proof.card_closure_pair_eq_nine hAe hA.2 hc'A hdA hc'1 hdc'
    have hBA : B ≤ A := by
      rw [hBdef, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact hc'A
      · rw [Set.mem_singleton_iff.mp hx]; exact hdA
    have hBC : B ≤ centralizerSection Y (CFSG.Open.pCoreOf 2 Y) := by
      rw [hBdef, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact mem_centralizerSection_of_trivial (hAY hc'A) htriv
      · rw [Set.mem_singleton_iff.mp hx]; exact hdC
    exact false_of_card_nine_trivial hR.toSec14Std hYO hAY hZ hE hE9 hBA hB9
      fun b hb y hy => trivial_of_mem_centralizerSection (hBC hb) y hy

theorem commutator_mem_of_threeCentral (h134 : Item134) (h48 : Sec4.Item4_8)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A))
    (hX5 : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    ∀ x ∈ X, ⁅x, d⁆ ∈ CFSG.Open.pCoreOf 2 X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := hR.toSec14Std.isE27'
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hR.toSec13Data.isElemAbelian
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  set N := Subgroup.normalizer (X : Set G) with hNdef
  set A' := A.subgroupOf N with hA'
  set f := Sec17.Proof17Res6.actQ X with hf
  obtain ⟨e5⟩ := hX5
  have hAut : Nat.card (MulAut (↥X ⧸ CFSG.pCore 2 ↥X)) = 120 :=
    (Nat.card_congr (MulAut.congr e5).toEquiv).trans Proof15Res8Diag.card_mulAut_five
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hA.2]
  have hI3 : IsPGroup 3 (A'.map f) := by
    have hA'3 : IsPGroup 3 A' := hA.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAX).symm
    exact hA'3.map f
  have hIle : Nat.card (A'.map f) ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hI3
    have hdvd : Nat.card (A'.map f) ∣ 120 := hAut ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra hk1
      push Not at hk1
      have : 3 ^ 2 ∣ 120 := (pow_dvd_pow 3 hk1).trans hdvd
      norm_num at this
    interval_cases k <;> norm_num
  set H := (f.ker ⊓ A').map N.subtype with hHdef
  have hHcard : Nat.card H = Nat.card (f.ker ⊓ A' : Subgroup N) := by
    rw [hHdef, Subgroup.card_map_of_injective N.subtype_injective]
  have h27 : f.ker.relIndex A' * Nat.card (f.ker ⊓ A' : Subgroup N) = 27 :=
    (Subgroup.relIndex_mul_card f.ker A').trans hA'27
  rw [Subgroup.relIndex_ker] at h27
  have hH9 : 9 ≤ Nat.card H := by
    rw [hHcard]
    by_contra hlt
    push Not at hlt
    have : Nat.card (A'.map f) * Nat.card (f.ker ⊓ A' : Subgroup N) ≤ 3 * 8 :=
      Nat.mul_le_mul hIle (by omega)
    omega
  have hHA : H ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
  have hHC : ∀ h ∈ H, h ∈ centralizerSection X (CFSG.Open.pCoreOf 2 X) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (actQ_eq_one_iff x).mp (Subgroup.mem_inf.mp hx).1
  have hHtriv : ∀ b ∈ H, ∀ y ∈ X, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    fun b hb y hy => trivial_of_mem_centralizerSection (hHC b hb) y hy
  have hHdvd : Nat.card H ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
    exact Subgroup.card_dvd_of_le hHA
  have h27' : Nat.card H ≠ 27 := by
    intro h27H
    have hHeq : H = A := Subgroup.eq_of_le_of_card_ge hHA (by rw [hA.2, h27H])
    obtain ⟨B, hB, hLB⟩ := hbot G A c L hR.toSec14Std
    refine Proof155w3.false_of_trivial_of_lB_eq_bot hR.toSec14Std hX hB hLB fun b hb y hy => ?_
    have hbH : b ∈ H := by
      rw [hHeq]
      exact hB.1 hb
    exact hHtriv b hbH y hy
  have h9 : Nat.card H = 9 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hHdvd
    rw [hk'] at hH9 h27' ⊢
    interval_cases k
    · norm_num at hH9
    · norm_num at hH9
    · norm_num
    · exact absurd (by norm_num) h27'
  have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, h9]⟩
  have hlB : lB A H ≠ ⊥ := fun hlB =>
    Proof155w3.false_of_trivial_of_lB_eq_bot hR.toSec14Std hX hH hlB hHtriv
  obtain ⟨b, d', Lb, hconf⟩ : ∃ b d' Lb, IsLBConfig A H b d' Lb := by
    by_contra hno
    push Not at hno
    exact hlB (lB_eq_bot hno)
  have hzd := Sec14.Ronan148W.zpowers_eq_of_isLBConfig_of_theta h134 h48 hR.toSec14Std hH hconf
    hR.toSec13Data.zpowers_mem_omegaA hR.toSec13Data.mem_lA hJL hdA hd1 hdc
  have hd'H : d' ∈ H := by
    rw [hconf.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton d'))
  have hdH : d ∈ H := by
    have : d ∈ Subgroup.zpowers d' := hzd ▸ Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr hd'H) this
  intro x hx
  exact (hHC d hdH).2.2 x hx

end Dclause

section Branch


theorem item154ProperWhen_j2 (hKf : KS154J2PerfNorm) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hbot : Item145BotS14) :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX hJ R hRm
  obtain ⟨hHJ, c', hc', htriv⟩ := point_of_j2 h148 h134 h48 hR hY.1 hJ
  have hJL := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hR.toSec13Data.zpowers_mem_omegaA
    hR.toSec13Data.mem_lA
  have hYO : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.2.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.2
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  rcases hj_branch hKf hR.toSec14Std hYO hAY hJ hXY (isPerfect_of_mem_scriptY4 hX)
      (ne_bot_of_mem_scriptY4 hX) hX.1.2 hRm.1 hR2 ((le_sup_left : A ≤ A ⊔ X).trans hRm.2.2)
      ((le_sup_right : X ≤ A ⊔ X).trans hRm.2.2) with h | ⟨hX5, hrel, hsq, hd⟩
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨hJ, hX5, hrel, hsq, fun d hdA hd1 hdc => hd d hdA ?_ ?_⟩)
    · exact not_mem_centralizerSection_of_threeCentral h134 h48 hR hJL hYO hAY hJ hc' htriv hdA
        hd1 hdc
    · exact commutator_mem_of_threeCentral h134 h48 hbot hR hJL hX hX5 hdA hd1 hdc

end Branch

end CFSG.RankThree.PartTwo.Sec15.Wales154
