module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4Proof
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofEnd
import CFSG.RankThree.PartTwo.Sec15.Item1523Proof
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res10

open Proof15Res4

theorem le_normalizer_commutator (h : Conf1515HJ A c L Y) :
    Y ≤ Subgroup.normalizer
      ((⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  have hD := h.sec13Data
  refine h.eq_Y.le.trans (sup_le ?_ ?_)
  · intro m hm
    exact mem_normalizer_commutator (h.le_normalizer_pCoreOf hm.1)
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers c
        (hD.le_centralizer hm.2))
  · exact Subgroup.normalizer_commutator_ge_left _ _

theorem le_centralizer_commutator
    (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hV : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G)) :
    Y ≤ Subgroup.centralizer
      ((⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  set V := ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ with hVdef
  set O := CFSG.Open.pCoreOf 2 Y with hO
  set CV := Subgroup.centralizer (V : Set G) with hCV
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := le_normalizer_commutator h
  have hdY : d ∈ Subgroup.normalizer (Y : Set G) := h.A_le_normalizer hdA
  have hdCV : d ∈ CV := by
    rw [hCV, Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hV hv)
  have hconjCV : ∀ y ∈ Y, ∀ x ∈ CV, y * x * y⁻¹ ∈ CV := by
    intro y hy x hx
    rw [hCV, Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : y⁻¹ * v * y ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hYV (Y.inv_mem hy)) v).mp hv
      simpa using this
    have hxv := hx _ hv'
    calc v * (y * x * y⁻¹) = y * ((y⁻¹ * v * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * v * y)) * y⁻¹ := by rw [hxv]
      _ = y * x * y⁻¹ * v := by group
  have hcomm : ∀ y ∈ Y, d * y * d⁻¹ * y⁻¹ ∈ Y ⊓ CV := by
    intro y hy
    refine ⟨Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hdY y).mp hy) (Y.inv_mem hy), ?_⟩
    have h1 : y * d⁻¹ * y⁻¹ ∈ CV := hconjCV y hy _ (CV.inv_mem hdCV)
    have e : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
    rw [e]
    exact CV.mul_mem hdCV h1
  obtain ⟨eJ⟩ := h.quot_pCore_two_equiv
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimp : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := eJ.isSimpleGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  set C' : Subgroup ↥Y := CV.subgroupOf Y with hC'
  have hC'n : C'.Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [hC', Subgroup.mem_subgroupOf] at hx ⊢
    have := hconjCV y y.2 x hx
    simpa using this
  have hmapn : (C'.map π).Normal := hC'n.map π (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal (C'.map π) with hbot | htop
  ·
    exfalso
    have hle : C' ≤ CFSG.pCore 2 ↥Y := by
      intro x hx
      have hx' : π x ∈ C'.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    have hdsec : d ∈ Late.sectionCentralizer A Y O := by
      refine ⟨hdA, fun y hy => ?_⟩
      have hm := hcomm y hy
      have hx : (⟨_, hm.1⟩ : ↥Y) ∈ C' := by
        rw [hC', Subgroup.mem_subgroupOf]
        exact hm.2
      exact (mem_pCoreOf_iff1523 _).mpr (hle hx)
    have hdc := h.mem_zpowers_of_mem_sectionCentralizer hdsec
    have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
    have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
    have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hd3, hD.orderOf_eq])
    apply (j2_point_facts hD h.j2).1
    have hcd : c ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hdL) hcd
  ·
    have hYle : Y ≤ (Y ⊓ CV) ⊔ O := by
      intro y hy
      have hy' : π ⟨y, hy⟩ ∈ C'.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨z, hz, hzy⟩ := hy'
      have hp : z⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y := QuotientGroup.eq.mp hzy
      have hzY : (z : G) ∈ Y ⊓ CV := ⟨z.2, Subgroup.mem_subgroupOf.mp hz⟩
      have hpO : (z : G)⁻¹ * y ∈ O := by
        have := (mem_pCoreOf_iff1523 (z⁻¹ * ⟨y, hy⟩)).mpr hp
        simpa using this
      have e : y = (z : G) * ((z : G)⁻¹ * y) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left hzY) (Subgroup.mem_sup_right hpO)
    have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hcop : Nat.Coprime 3 (Nat.card O) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hOY : O ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
    have hON : O ≤ Subgroup.normalizer ((Y ⊓ CV : Subgroup G) : Set G) := by
      refine Late.le_normalizer_inf (hOY.trans Subgroup.le_normalizer) ?_
      intro o ho
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hconjCV o (hOY ho) x hx
      · intro hx
        have := hconjCV o⁻¹ (Y.inv_mem (hOY ho)) _ hx
        simpa [mul_assoc] using this
    have hres := Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hcop hON hYle
    have hY3 : Y = oPrimeResidualOf 3 Y := h.mem_scriptY0Star.prop.1.2.1
    intro y hy
    exact (hres (hY3.le hy)).2

theorem commutator_mem (h : Conf1515HJ A c L Y) {y : G} (hy : y ∈ Y) :
    c * y * c⁻¹ * y⁻¹ ∈ ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ := by
  have hD := h.sec13Data
  set V := ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ with hVdef
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hYLO : Y ⊓ L ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_left.trans h.le_normalizer_pCoreOf
  obtain ⟨m, hm, o, ho, rfl⟩ := exists_mul_of_mem_sup hYLO (h.eq_Y.le hy)
  have hcm : c * m = m * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hm.2)).symm
  rw [conj_mul_eq hcm]
  have h1 : c * o * c⁻¹ * o⁻¹ ∈ V := by
    have hoc : ⁅o, c⁆ ∈ V := Subgroup.commutator_mem_commutator ho (Subgroup.mem_zpowers c)
    have e : c * o * c⁻¹ * o⁻¹ = ⁅o, c⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.inv_mem hoc
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator h hm.1) _).mp h1

theorem le_centralizer_c
    (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hV : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G)) :
    Y ≤ Subgroup.centralizer ({c} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYC := le_centralizer_commutator h hdA hd1 hdL hV
  set V := ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ with hVdef
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hVO : V ≤ O := by
    rw [hVdef, Subgroup.commutator_le]
    intro o ho g hg
    rw [commutatorElement_def]
    have hgO : g ∈ Subgroup.normalizer (O : Set G) :=
      h.A_le_normalizer_pCoreOf ((Subgroup.zpowers_le.mpr h.sec13Data.mem_A) hg)
    have h1 : g * o⁻¹ * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hgO o⁻¹).mp (inv_mem ho)
    have e : o * g * o⁻¹ * g⁻¹ = o * (g * o⁻¹ * g⁻¹) := by group
    rw [e]
    exact mul_mem ho h1
  have hV2 : IsPGroup 2 V := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hVO
  have hY3 : Y = oPrimeResidualOf 3 Y := h.mem_scriptY0Star.prop.1.2.1
  intro y hy
  have hy' : y ∈ oPrimeResidualOf 3 Y := hY3.le hy
  rw [oPrimeResidualOf_eq_closure] at hy'
  refine (Subgroup.closure_le _).mpr ?_ hy'
  rintro x ⟨hxY, k, hxk⟩
  set u := c * x * c⁻¹ * x⁻¹ with hu
  have huV : u ∈ V := commutator_mem h hxY
  have hux : Commute u x := Subgroup.mem_centralizer_iff.mp (hYC hxY) u huV
  have hcx : c * x * c⁻¹ = u * x := by rw [hu]; group
  have hpow : ∀ n : ℕ, c * x ^ n * c⁻¹ = u ^ n * x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc c * x ^ (n + 1) * c⁻¹ = (c * x ^ n * c⁻¹) * (c * x * c⁻¹) := by
            rw [pow_succ]; group
        _ = u ^ n * x ^ n * (u * x) := by rw [ih, hcx]
        _ = u ^ (n + 1) * x ^ (n + 1) := by
            rw [pow_succ, pow_succ]
            have hc : Commute (x ^ n) u := (hux.symm.pow_left n)
            calc u ^ n * x ^ n * (u * x) = u ^ n * (x ^ n * u) * x := by group
              _ = u ^ n * (u * x ^ n) * x := by rw [hc.eq]
              _ = u ^ n * u * (x ^ n * x) := by group
  have hu3 : u ^ (3 ^ k) = 1 := by
    have := hpow (3 ^ k)
    rw [hxk, mul_one, mul_one, mul_inv_cancel] at this
    exact this.symm
  obtain ⟨m, hm⟩ := hV2 ⟨u, huV⟩
  have hu2 : u ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (2 ^ m) :=
    Nat.Coprime.pow k m (by norm_num)
  have hord : orderOf u = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3)
      (orderOf_dvd_of_pow_eq_one hu2))
  rw [orderOf_eq_one_iff] at hord
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have e : c * x = u * x * c := by rw [hu]; group
  rw [e, hord, one_mul]

theorem commutator_eq_bot
    (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hV : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G)) :
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = ⊥ := by
  have hYc := le_centralizer_c h hdA hd1 hdL hV
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hoc : Commute o c :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hYc ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y) ho))
  exact ((hoc.zpow_right k).symm).eq

end Proof15Res10

open Proof15Res4 Proof15Res10

section Provers


theorem step1515HJVTail_of_res10 : Step1515HJVTail := by
  intro G _ _ A c L hR' hJ Y hY hm hYL hLY hΩ d hdA hd1 hdZ hV _hP
  have h : Conf1515HJ A c L Y := ⟨hR', hJ, hY, hm, hYL, hLY, hΩ⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans
    (le_centralizer_c h hdA hd1 (mem_of_isZCentral hdZ) hV)

theorem step1515HJVFour_of_res10 : Step1515HJVFour := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hV _hP hV1
  exact (hV1 (commutator_eq_bot h hdA hd1 (mem_of_isZCentral hdZ) hV)).elim

theorem step1515HJVR_of_res10 : Step1515HJVR := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hV _hP h4
  rw [commutator_eq_bot h hdA hd1 (mem_of_isZCentral hdZ) hV, Subgroup.card_bot] at h4
  omega

theorem step1515HJVBlockM_of_res10 : Step1515HJVBlockM := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hV _hP h4 _hR
  rw [commutator_eq_bot h hdA hd1 (mem_of_isZCentral hdZ) hV, Subgroup.card_bot] at h4
  omega

end Provers

end CFSG.RankThree.PartTwo.Sec15
