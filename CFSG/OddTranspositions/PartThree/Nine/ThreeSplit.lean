module

public import CFSG.OddTranspositions.PartThree.Nine.Setup
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar
public import CFSG.GroupTheory.OddCoreQuotient
public import CFSG.Holt.General.OrbitCountBasic
public import CFSG.RankThree.PartOne.U5K.Perfect
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.Holt.Fixed
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.OddTranspositions.Width
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

section Abstract

variable {K : Type} [Group K] [Finite K]

theorem even_card_of_isBenderGroup {X : Type*} [Group X] [Finite X]
    (hB : CFSG.BenderSuzuki.IsBenderGroup X) : Even (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
  have h4 := IsBenderGroup.four_le_card_center hB Q
  have hle : Nat.card (Subgroup.center (Q : Subgroup X)) ≤ Nat.card (Q : Subgroup X) :=
    Subgroup.card_le_card_group _
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have h2Q : 2 ∣ Nat.card (Q : Subgroup X) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact even_iff_two_dvd.mpr (h2Q.trans (Subgroup.card_subgroup_dvd_card _))

theorem oddCore_le_center_of_isBenderGroup
    (hB : CFSG.BenderSuzuki.IsBenderGroup (K ⧸ Subgroup.center K)) :
    CFSG.oddCore K ≤ Subgroup.center K := by
  have := IsBenderGroup.isSimpleGroup hB
  have hNn : ((CFSG.oddCore K).map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    (CFSG.oddCore_normal K).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.oddCore K).map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center K) x ∈
        (CFSG.oddCore K).map (QuotientGroup.mk' (Subgroup.center K)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  · exfalso
    have hdvd := Subgroup.card_map_dvd (CFSG.oddCore K) (QuotientGroup.mk' (Subgroup.center K))
    rw [h, Subgroup.card_top] at hdvd
    have hodd : Odd (Nat.card (CFSG.oddCore K)) := CFSG.ABGLocalTools.odd_card_oddCore
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd hdvd)) (even_card_of_isBenderGroup hB)

omit [Finite K] in
theorem mem_of_pow_two_pow_mem_of_odd {M : Subgroup K} {x : K} {k : ℕ} (hxk : x ^ 2 ^ k ∈ M)
    (hodd : Odd (orderOf x)) : x ∈ M := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  rw [← hm]
  exact M.pow_mem hxk m

omit [Finite K] in
theorem mem_pCore_of_mem_center {p : ℕ} {x : K} (hx : x ∈ Subgroup.center K)
    (hp : IsPGroup p (Subgroup.zpowers x)) : x ∈ CFSG.pCore p K :=
  (le_sSup (show Subgroup.zpowers x ∈ {N : Subgroup K | N.Normal ∧ IsPGroup p N} from
    ⟨Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hx), hp⟩) :
    Subgroup.zpowers x ≤ CFSG.pCore p K) (Subgroup.mem_zpowers x)

omit [Finite K] in
theorem mem_oddCore_of_mem_center {x : K} (hx : x ∈ Subgroup.center K)
    (hodd : Odd (orderOf x)) : x ∈ CFSG.oddCore K :=
  CFSG.ABGLocalTools.le_oddCore_of_normal
    (Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hx))
    (by rwa [Nat.card_zpowers]) (Subgroup.mem_zpowers x)

theorem center_le_pCore_sup_oddCore :
    Subgroup.center K ≤ CFSG.pCore 2 K ⊔ CFSG.oddCore K := by
  intro z hz
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  have ha : z ^ m ∈ CFSG.pCore 2 K := by
    refine mem_pCore_of_mem_center (Subgroup.pow_mem _ hz m) ?_
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, orderOf_pow' z hm.pos.ne',
      hkm, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel _ hm.pos
  have hb : z ^ 2 ^ k ∈ CFSG.oddCore K := by
    refine mem_oddCore_of_mem_center (Subgroup.pow_mem _ hz _) ?_
    rw [orderOf_pow' z (pow_ne_zero _ two_ne_zero), hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hm
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  have hz' : z = (z ^ m) ^ (Nat.gcdA m (2 ^ k)) * (z ^ 2 ^ k) ^ (Nat.gcdB m (2 ^ k)) := by
    rw [← zpow_natCast, ← zpow_natCast z (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
      zpow_one]
  rw [hz']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _ ha _))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hb _))

theorem pCore_split {E₀ : Set K} (hS : Setup K E₀)
    (hrad : CFSG.solvableRadical K = Subgroup.center K)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (K ⧸ Subgroup.center K)) :
    CFSG.pCore 2 K ≤ Subgroup.center K ∧ Nat.card (CFSG.pCore 2 K) ≤ 2 ∧
      CFSG.pCore 2 K ⊔ CFSG.Quasithin.pResidual 2 K = ⊤ ∧
      Disjoint (CFSG.pCore 2 K) (CFSG.Quasithin.pResidual 2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center K with hZ
  set O := CFSG.oddCore K with hO
  set P := CFSG.pCore 2 K with hP
  set R := CFSG.Quasithin.pResidual 2 K with hR
  have hOZ : O ≤ Z := oddCore_le_center_of_isBenderGroup hB
  have hPZ : P ≤ Z := hrad ▸ CFSG.pCore_le_solvableRadical 2 K
  have hOodd : Odd (Nat.card O) := CFSG.ABGLocalTools.odd_card_oddCore
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hPO : P ⊓ O = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hOodd)
  let π : K →* K ⧸ O := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  let E : Subgroup (K ⧸ O) := Z.map π
  have hEc : E ≤ Subgroup.center (K ⧸ O) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨t, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hs t)]
  have hEn : E.Normal := Subgroup.normal_of_le_center hEc
  have hE2 : IsPGroup 2 E := CFSG.GroupTheory.isPGroup_two_map_mk_oddCore_of_le_center le_rfl
  have hB' : CFSG.BenderSuzuki.IsBenderGroup ((K ⧸ O) ⧸ E) :=
    isBenderGroup_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient O Z hOZ) hB
  have hS' : Setup (K ⧸ O) (π '' E₀) := by
    refine hS.map π hπs fun d hd h1 => ?_
    have hdO : d ∈ O := (QuotientGroup.eq_one_iff d).mp h1
    exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card hOodd (hS.oddT.orderOf_eq_two hd) hdO
  have hcompl := isCompl_commutator_of_isBenderGroup hS' hEc hE2 hB'
  have hEcard : Nat.card E ≤ 2 := card_le_two_of_isBenderGroup hS' hEc hE2 hB'
  have hcommmap : (commutator K).map π = commutator (K ⧸ O) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπs]
  set C := commutator K ⊔ O with hC
  have hCn : C.Normal := Subgroup.sup_normal _ _
  have hZC : Z ⊓ C ≤ O := by
    rintro z ⟨hzZ, hzC⟩
    have h1 : π z ∈ E ⊓ commutator (K ⧸ O) := by
      refine ⟨Subgroup.mem_map_of_mem π hzZ, ?_⟩
      have : π z ∈ C.map π := Subgroup.mem_map_of_mem π hzC
      rwa [hC, Subgroup.map_sup, hcommmap, QuotientGroup.map_mk'_self, sup_bot_eq] at this
    rw [hcompl.inf_eq_bot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff z).mp h1
  have hZCtop : Z ⊔ C = ⊤ := by
    have h := Subgroup.comap_map_eq π (Z ⊔ commutator K)
    rw [Subgroup.map_sup, hcommmap, hcompl.sup_eq_top, Subgroup.comap_top, hker] at h
    rw [hC, ← sup_assoc, h]
  have hOR : O ≤ R := by
    refine le_iInf fun N => le_iInf fun _ => le_iInf fun hNp => ?_
    intro x hx
    obtain ⟨k, hk⟩ := hNp x
    refine mem_of_pow_two_pow_mem_of_odd hk ?_
    rw [← Subgroup.orderOf_mk x hx]
    exact Odd.of_dvd_nat hOodd (orderOf_dvd_natCard _)
  have hperf : ⁅commutator K, commutator K⁆ = commutator K := by
    have hp : Group.IsPerfect (K ⧸ Subgroup.center K) :=
      ⟨IsBenderGroup.commutator_eq_top hB⟩
    exact Subgroup.isPerfect_iff.mp (CFSG.RankThree.PartOne.U5K.isPerfect_commutator hp)
  have hKR : commutator K ≤ R := by
    refine le_iInf fun N => le_iInf fun hN => le_iInf fun hNp => ?_
    have := hN
    refine CFSG.Holt.General.le_of_isPerfect_of_forall_pow_mem (p := 2) hperf ?_
      fun g _ => hNp g
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hCR : C ≤ R := sup_le hKR hOR
  have hRC : R ≤ C := by
    refine CFSG.Quasithin.pResidual_le fun x => ?_
    obtain ⟨z, hz, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
      (show x ∈ Z ⊔ C from hZCtop ▸ Subgroup.mem_top x)
    obtain ⟨k, hk⟩ := hE2 ⟨π z, Subgroup.mem_map_of_mem π hz⟩
    have hzk : z ^ 2 ^ k ∈ O := by
      have h1 : π (z ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact (QuotientGroup.eq_one_iff _).mp h1
    refine ⟨k, ?_⟩
    have hzc : Commute z c := (Subgroup.mem_center_iff.mp hz c).symm
    rw [hzc.mul_pow]
    exact C.mul_mem (Subgroup.mem_sup_right hzk) (C.pow_mem hc _)
  have hRCeq : R = C := le_antisymm hRC hCR
  refine ⟨hPZ, ?_, ?_, ?_⟩
  ·
    have hinj : Function.Injective fun x : P =>
        (⟨π x, Subgroup.mem_map_of_mem π (hPZ x.2)⟩ : E) := by
      intro x y hxy
      have h1 : π ((x : K)⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hxy
      have h2 : (x : K)⁻¹ * y ∈ P ⊓ O :=
        ⟨P.mul_mem (P.inv_mem x.2) y.2, (QuotientGroup.eq_one_iff _).mp h1⟩
      rw [hPO, Subgroup.mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2
    exact (Nat.card_le_card_of_injective _ hinj).trans hEcard
  ·
    rw [eq_top_iff, ← hZCtop, ← hRCeq]
    refine sup_le ((center_le_pCore_sup_oddCore).trans (sup_le le_sup_left
      (hOR.trans le_sup_right))) le_sup_right
  ·
    rw [Subgroup.disjoint_def]
    intro x hxP hxR
    have hxO : x ∈ O := hZC ⟨hPZ hxP, hRCeq ▸ hxR⟩
    have : x ∈ P ⊓ O := ⟨hxP, hxO⟩
    rwa [hPO, Subgroup.mem_bot] at this

end Abstract

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem setup_DstarH (hC : HypothesisC D) : Setup (Halpha D hC.alpha) (DstarH hC) :=
  ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩

theorem Halpha_pCore_split (hC : HypothesisC D) (hH : Th91Hyp D hC) :
    (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
        (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
      Nat.card ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) ≤ 2 ∧
      (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) = Halpha D hC.alpha ∧
      Disjoint ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
        (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  obtain ⟨hPZ, hcard, hsup, hdisj⟩ := pCore_split (setup_DstarH hC) hH.rad hH.bender
  have hinj := (Halpha D hC.alpha).subtype_injective
  refine ⟨Subgroup.map_mono hPZ, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective hinj]
  · rw [CFSG.Quasithin.pResidualOf, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · exact Subgroup.disjoint_map hinj hdisj

end CFSG.OddTranspositions.PartThree.Nine
