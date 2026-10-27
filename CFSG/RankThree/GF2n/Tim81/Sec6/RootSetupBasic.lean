module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetup
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
import CFSG.GroupTheory.OddCentralQuotient
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.InvariantSubgroup
import CFSG.RankThree.GF2n.Tim79aSec22Adapter

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection CFSG.GroupTheory

variable {K : Type} [Group K] [Finite K] {X : Subgroup K} {Δ : Set (Subgroup K)} {f : ℕ}

theorem RootSetup.isPGroup (h : RootSetup X Δ f) {A : Subgroup K} (hA : A ∈ Δ) :
    IsPGroup 2 A :=
  IsPGroup.of_card (h.card A hA)

private theorem RootSetup.four_le_pow (h : RootSetup X Δ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num) h.two_le

theorem RootSetup.isPerfect (h : RootSetup X Δ f) : Group.IsPerfect ↥X := by
  rw [Subgroup.isPerfect_iff]
  haveI : X.Normal := h.normal
  refine le_antisymm (Subgroup.commutator_le_left X X) ?_
  conv_lhs => rw [h.gen]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨B, hB, hAB⟩ := h.partner A hA
  have h4 : 4 ≤ Nat.card A := by
    rw [h.card A hA]
    exact h.four_le_pow
  have hABle : A ⊔ B ≤ X := sup_le (h.le A hA) (h.le B hB)
  haveI : IsSimpleGroup ↥(A ⊔ B) := hAB.isSimpleGroup h4
  have hnab : ¬ IsMulCommutative ↥(A ⊔ B) := by
    intro hc
    haveI := hc
    exact hAB.not_commuting fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ B))
        (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B)))
  have hcommtop : commutator ↥(A ⊔ B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(A ⊔ B)) with h | h
    · exact absurd ((commutator_eq_bot_iff ↥(A ⊔ B)).mp h) hnab
    · exact h
  have hH : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := Subgroup.isPerfect_iff.mp ⟨hcommtop⟩
  calc A ≤ A ⊔ B := le_sup_left
    _ = ⁅A ⊔ B, A ⊔ B⁆ := hH.symm
    _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hABle hABle

theorem RootSetup.odd_card_center (h : RootSetup X Δ f) :
    Odd (Nat.card (Subgroup.center ↥X)) := by
  by_contra hnot
  rw [Nat.not_odd_iff_even] at hnot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup ↥X := Subgroup.center ↥X
  let P : Sylow 2 ↥Z := Classical.arbitrary _
  have hPle : (P : Subgroup ↥Z).map Z.subtype ≤ pCore 2 ↥X := by
    refine le_sSup ⟨?_, ?_⟩
    · exact Subgroup.normal_of_le_center (Subgroup.map_subtype_le (P : Subgroup ↥Z))
    · exact P.isPGroup'.map Z.subtype
  rw [h.pCore_eq_bot] at hPle
  have hPbot : (P : Subgroup ↥Z) = ⊥ := by
    apply Subgroup.map_injective (f := Z.subtype) Z.subtype_injective
    rw [Subgroup.map_bot]
    exact le_bot_iff.mp hPle
  exact Sylow.ne_bot_of_dvd_card P hnot.two_dvd hPbot

private theorem RootSetup.inf_center_eq_bot (h : RootSetup X Δ f) {A : Subgroup K}
    (hA : A ∈ Δ) : A.subgroupOf X ⊓ Subgroup.center ↥X = ⊥ := by
  have hAcard : Nat.card (A.subgroupOf X) = 2 ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le A hA)).toEquiv, h.card A hA]
  have hcop : Nat.Coprime (Nat.card (A.subgroupOf X)) (Nat.card (Subgroup.center ↥X)) := by
    rw [hAcard]
    exact Nat.Coprime.pow_left f h.odd_card_center.coprime_two_left
  exact Subgroup.inf_eq_bot_of_coprime hcop

theorem RootSetup.le_center_of_isNilpotent (h : RootSetup X Δ f) (N : Subgroup ↥X)
    (hN : N.Normal) (hnil : Group.IsNilpotent N) : N ≤ Subgroup.center ↥X := by
  haveI := hnil
  haveI : N.Normal := hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card N) := by
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    let P : Sylow 2 N := Classical.arbitrary _
    have hPchar : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P inferInstance
    haveI : (P : Subgroup N).Characteristic := hPchar
    have hPle : (P : Subgroup N).map N.subtype ≤ pCore 2 ↥X :=
      le_sSup ⟨inferInstance, P.isPGroup'.map N.subtype⟩
    rw [h.pCore_eq_bot] at hPle
    have hPbot : (P : Subgroup N) = ⊥ := by
      apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
      rw [Subgroup.map_bot]
      exact le_bot_iff.mp hPle
    exact Sylow.ne_bot_of_dvd_card P hnot.two_dvd hPbot
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hodd
  exact (le_sSup ⟨hN, hcop⟩ : N ≤ pPrimeCore 2 ↥X).trans h.oddCore_le

theorem RootSetup.center_quot (h : RootSetup X Δ f) : Subgroup.center (quotY X) = ⊥ := by
  haveI : Group.IsPerfect ↥X := h.isPerfect
  exact Group.IsPerfect.center_quotient_center_eq_bot ↥X

theorem RootSetup.no_nilpotent_quot (h : RootSetup X Δ f) :
    ∀ N : Subgroup (quotY X), N.Normal → Group.IsNilpotent N → N = ⊥ := by
  intro N hN hnil
  exact CFSG.GroupTheory.eq_bot_of_isNilpotent_quotient_center
    (fun M hM hMnil => h.le_center_of_isNilpotent M hM hMnil) N hN hnil

theorem RootSetup.card_quotSub (h : RootSetup X Δ f) {A : Subgroup K} (hA : A ∈ Δ) :
    Nat.card (quotSub X A) = 2 ^ f := by
  have hker : A.subgroupOf X ⊓ (quotMap X).ker = ⊥ := by
    rw [show (quotMap X).ker = Subgroup.center ↥X from QuotientGroup.ker_mk' _]
    exact h.inf_center_eq_bot hA
  have hcard := CFSG.card_map_eq_card_of_inf_ker_eq_bot (quotMap X) hker
  have hAcard : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le A hA)).toEquiv
  rw [hcard, hAcard, h.card A hA]

private theorem RootSetup.quotSub_ne_bot (h : RootSetup X Δ f) {A : Subgroup K}
    (hA : A ∈ Δ) : quotSub X A ≠ ⊥ := by
  intro hbot
  have hcard := h.card_quotSub hA
  rw [hbot, Subgroup.card_bot] at hcard
  have h4 := h.four_le_pow
  omega

theorem RootSetup.quotSub_inj (h : RootSetup X Δ f) {A B : Subgroup K} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hAB : quotSub X A = quotSub X B) : A = B := by
  have h' : A.subgroupOf X = B.subgroupOf X :=
    CFSG.GroupTheory.eq_of_map_mk_eq_of_le_center le_rfl h.odd_card_center
      (h.isPGroup hA).comap_subtype (h.isPGroup hB).comap_subtype hAB
  exact (Timmesfeld.ARS.subgroupOf_inj_of_le (h.le A hA) (h.le B hB)).mp h'

theorem RootSetup.isL2Gen_quotSub (h : RootSetup X Δ f) {A B : Subgroup K} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hl : IsL2Gen A B) : IsL2Gen (quotSub X A) (quotSub X B) := by
  have hA' : IsL2Gen (A.subgroupOf X) (B.subgroupOf X) :=
    hl.subgroupOf (h.le A hA) (h.le B hB)
  have h4 : 4 ≤ Nat.card (A.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le A hA)).toEquiv, h.card A hA]
    exact h.four_le_pow
  have hnot : ¬ A.subgroupOf X ≤ (quotMap X).ker := by
    intro hle
    have hmap : (A.subgroupOf X).map (quotMap X) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr hle
    have hcard : Nat.card ↥((A.subgroupOf X).map (quotMap X)) = 2 ^ f := h.card_quotSub hA
    rw [hmap, Subgroup.card_bot] at hcard
    have h4' := h.four_le_pow
    omega
  exact hA'.map (quotMap X) (hA'.ker_inf_eq_bot h4 (quotMap X) hnot)

theorem RootSetup.commutator_quotSub_eq_bot_iff (h : RootSetup X Δ f) {A B : Subgroup K}
    (hA : A ∈ Δ) (hB : B ∈ Δ) :
    ⁅quotSub X A, quotSub X B⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  constructor
  · intro hbot
    by_cases hAB : A = B
    · subst hAB
      obtain ⟨C, hC, hAC⟩ := h.partner A hA
      refine commuting_iff_commutator_eq_bot.mp fun a ha b hb =>
        commute_of_mul_self (H := A) (fun x hx => by
          simpa [pow_two] using hAC.isElemAbelian.2 x hx) ha hb
    · rcases h.pair A hA B hB hAB with hcomm | hL2
      · exact hcomm
      · exact absurd hbot (h.isL2Gen_quotSub hA hB hL2).commutator_ne_bot
  · intro hbot
    have hcK : Commuting A B := commuting_iff_commutator_eq_bot.mpr hbot
    have hcX : Commuting (A.subgroupOf X) (B.subgroupOf X) := by
      intro x hx y hy
      exact Subtype.ext (hcK (x : K) (Subgroup.mem_subgroupOf.mp hx) (y : K)
        (Subgroup.mem_subgroupOf.mp hy)).eq
    have hbotX : ⁅A.subgroupOf X, B.subgroupOf X⁆ = ⊥ :=
      commuting_iff_commutator_eq_bot.mp hcX
    change ⁅(A.subgroupOf X).map (quotMap X), (B.subgroupOf X).map (quotMap X)⁆ = ⊥
    rw [← Subgroup.map_commutator, hbotX, Subgroup.map_bot]

theorem RootSetup.conj_mem_quotDelta (h : RootSetup X Δ f) :
    ∀ A' ∈ quotDelta X Δ, ∀ y : quotY X, conjSubgroup y A' ∈ quotDelta X Δ := by
  rintro A' ⟨A, hA, rfl⟩ y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥X) y
  refine ⟨conjSubgroup (x : K) A, h.conj_mem A hA (x : K) x.2, ?_⟩
  rw [quotSub, Tim79a.subgroupOf_conjSubgroup, ← CFSG.GroupTheory.map_conjSubgroup]

theorem RootSetup.quot_pair (h : RootSetup X Δ f) : ∀ A' ∈ quotDelta X Δ,
    ∀ B' ∈ quotDelta X Δ, A' ≠ B' → ⁅A', B'⁆ = ⊥ ∨ IsL2Gen A' B' := by
  rintro A' ⟨A, hA, rfl⟩ B' ⟨B, hB, rfl⟩ hne
  have hAB : A ≠ B := fun hEq => hne (by rw [hEq])
  rcases h.pair A hA B hB hAB with hcomm | hL2
  · exact Or.inl ((h.commutator_quotSub_eq_bot_iff hA hB).mpr hcomm)
  · exact Or.inr (h.isL2Gen_quotSub hA hB hL2)

private theorem RootSetup.isRootClass_quot (h : RootSetup X Δ f) :
    IsRootClass (quotDelta X Δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨A₀, hA₀⟩ := h.nonempty
    refine ⟨quotSub X A₀, ?_⟩
    ext C'
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨x, hx, rfl⟩ := h.conj A₀ hA₀ C hC
      refine ⟨QuotientGroup.mk' (Subgroup.center ↥X) ⟨x, hx⟩, ?_⟩
      rw [quotSub, quotSub,
        show (conjSubgroup x A₀).subgroupOf X =
          conjSubgroup ⟨x, hx⟩ (A₀.subgroupOf X) from
          Tim79a.subgroupOf_conjSubgroup X A₀ ⟨x, hx⟩]
      exact CFSG.GroupTheory.map_conjSubgroup (quotMap X) (A₀.subgroupOf X) ⟨x, hx⟩
    · rintro ⟨y, rfl⟩
      exact h.conj_mem_quotDelta (quotSub X A₀) ⟨A₀, hA₀, rfl⟩ y
  · rintro A' ⟨A, hA, rfl⟩
    exact h.quotSub_ne_bot hA
  · rintro A' ⟨A, hA, rfl⟩ a ha
    obtain ⟨B, hB, hAB⟩ := h.partner A hA
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hx2 : x * x = 1 := by
      apply Subtype.ext
      simpa [pow_two, Subgroup.coe_mul] using hAB.isElemAbelian.2 (x : K)
        (Subgroup.mem_subgroupOf.mp hx)
    rw [← map_mul, hx2, map_one]
  · rintro A' ⟨A, hA, rfl⟩ B' ⟨B, hB, rfl⟩ hne
    have hAB : A ≠ B := fun hEq => hne (by rw [hEq])
    rcases h.pair A hA B hB hAB with hcomm | hL2
    · left
      have hcK : Commuting A B := commuting_iff_commutator_eq_bot.mpr hcomm
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      have hxy : x * y = y * x :=
        Subtype.ext (hcK (x : K) (Subgroup.mem_subgroupOf.mp hx) (y : K)
          (Subgroup.mem_subgroupOf.mp hy)).eq
      change quotMap X x * quotMap X y = quotMap X y * quotMap X x
      simpa only [map_mul] using congrArg (quotMap X) hxy
    · exact Or.inr (Or.inl (h.isL2Gen_quotSub hA hB hL2).opposite)
  · have hmap : (⨆ A ∈ Δ, A.subgroupOf X).map X.subtype = ⨆ A ∈ Δ, A := by
      simp_rw [Subgroup.map_iSup]
      apply iSup_congr
      intro A
      apply iSup_congr
      intro hA
      exact Subgroup.map_subgroupOf_eq_of_le (h.le A hA)
    have htop : (⊤ : Subgroup ↥X) = ⨆ A ∈ Δ, A.subgroupOf X := by
      apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
      rw [hmap, Subgroup.map_top, Subgroup.range_subtype, h.gen]
    rw [quotDelta, iSup_image]
    calc ⨆ A ∈ Δ, quotSub X A
        = (⨆ A ∈ Δ, A.subgroupOf X).map (quotMap X) := by
          simp_rw [Subgroup.map_iSup]
      _ = (⊤ : Subgroup ↥X).map (quotMap X) := by rw [htop]
      _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem RootSetup.isTransvectionClass_quot (h : RootSetup X Δ f) :
    IsTransvectionClass (quotDelta X Δ) := by
  refine ⟨h.isRootClass_quot, ?_⟩
  rintro A' ⟨A, hA, rfl⟩ B' ⟨B, hB, rfl⟩ hsp
  by_cases hAB : A = B
  · subst hAB
    obtain ⟨C, -, hAC⟩ := h.partner A hA
    have hAA : ⁅quotSub X A, quotSub X A⁆ = ⊥ := by
      refine (h.commutator_quotSub_eq_bot_iff hA hA).mpr ?_
      refine commuting_iff_commutator_eq_bot.mp ?_
      intro a ha b hb
      exact commute_of_mul_self (H := A) (fun x hx => by
        simpa [pow_two] using hAC.isElemAbelian.2 x hx) ha hb
    have hsp1 := hsp.1
    rw [hAA] at hsp1
    obtain ⟨C', hC', hC'bot⟩ := hsp1
    exact h.quotSub_ne_bot hC' hC'bot
  · rcases h.pair A hA B hB hAB with hcomm | hL2
    · have hbot : ⁅quotSub X A, quotSub X B⁆ = ⊥ :=
        (h.commutator_quotSub_eq_bot_iff hA hB).mpr hcomm
      have hsp1 := hsp.1
      rw [hbot] at hsp1
      obtain ⟨C', hC', hC'bot⟩ := hsp1
      exact h.quotSub_ne_bot hC' hC'bot
    · exact (h.isL2Gen_quotSub hA hB hL2).not_special (quotDelta X Δ) hsp
