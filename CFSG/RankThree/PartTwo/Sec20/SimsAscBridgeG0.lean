module

import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem le_inSubgroup_pPrimeCore_of_sup_eq {H G₀ U : Subgroup G} (hUH : U ≤ H)
    (hG₀U : G₀ ≤ Subgroup.normalizer (U : Set G))
    (hcov : G₀ ⊔ inSubgroup (CFSG.pPrimeCore 3) H = H) (hU : Nat.Coprime 3 (Nat.card U)) :
    U ≤ inSubgroup (CFSG.pPrimeCore 3) H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K₀ := inSubgroup (CFSG.pPrimeCore 3) H with hK₀
  have hHK₀ : H ≤ Subgroup.normalizer (K₀ : Set G) :=
    Res6.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hK₀H : K₀ ≤ H := Res6.inSubgroup_pPrimeCore_le 3 H
  have hG₀H : G₀ ≤ H := hcov ▸ le_sup_left
  set W := U ⊔ K₀ with hW
  have hWH : W ≤ H := sup_le hUH hK₀H
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hcov]
    refine sup_le (fun g hg => Res6.mem_normalizer_sup (hG₀U hg) (hHK₀ (hG₀H hg))) ?_
    exact (le_sup_right : K₀ ≤ W).trans Subgroup.le_normalizer
  have hWc : Nat.Coprime 3 (Nat.card W) := by
    have h := Sec6.card_sup_mul_card_inf (X := U) (N := K₀) (hUH.trans hHK₀)
    have hK₀c := Res6.coprime_card_inSubgroup_pPrimeCore 3 H
    have hc : Nat.Coprime 3 (Nat.card U * Nat.card K₀) := Nat.Coprime.mul_right hU hK₀c
    rw [← h] at hc
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hc
  exact le_sup_left.trans (Res6.le_inSubgroup_pPrimeCore hWH hHW hWc)

theorem inSubgroup_pPrimeCore_eq_inf {H G₀ : Subgroup G} (hG₀H : G₀ ≤ H)
    (hcov : G₀ ⊔ inSubgroup (CFSG.pPrimeCore 3) H = H) :
    inSubgroup (CFSG.pPrimeCore 3) G₀ = G₀ ⊓ inSubgroup (CFSG.pPrimeCore 3) H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · refine le_inf (Res6.inSubgroup_pPrimeCore_le 3 G₀) ?_
    exact le_inSubgroup_pPrimeCore_of_sup_eq ((Res6.inSubgroup_pPrimeCore_le 3 G₀).trans hG₀H)
      (Res6.le_normalizer_inSubgroup_pPrimeCore 3 G₀) hcov
      (Res6.coprime_card_inSubgroup_pPrimeCore 3 G₀)
  · refine Res6.le_inSubgroup_pPrimeCore inf_le_left ?_ ?_
    · exact fun g hg => Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hg)
        (Res6.le_normalizer_inSubgroup_pPrimeCore 3 H (hG₀H hg))
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (Res6.coprime_card_inSubgroup_pPrimeCore 3 H)

theorem isSylowOf_sup_of_le {p : ℕ} [Fact p.Prime] {V O Q S : Subgroup G}
    (hVO : V ≤ Subgroup.normalizer (O : Set G)) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q O)
    (hQV : Q ≤ V) (hS : CFSG.ABGLocalTools.IsSylowOf p S V) :
    CFSG.ABGLocalTools.IsSylowOf p S (V ⊔ O) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hQVO : CFSG.ABGLocalTools.IsSylowOf p Q (V ⊓ O) :=
    hQ.of_le (le_inf hQV hQ.le) inf_le_right
  have hfac : (Nat.card O).factorization p = (Nat.card (V ⊓ O : Subgroup G)).factorization p := by
    have h := hQ.card_eq.symm.trans hQVO.card_eq
    exact Nat.pow_right_injective hp h
  have hmul := Sec6.card_sup_mul_card_inf (X := V) (N := O) hVO
  have h4 : (Nat.card (V ⊔ O : Subgroup G)).factorization p = (Nat.card V).factorization p := by
    have h := congrArg (fun n => n.factorization p) hmul
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Finsupp.add_apply, ← hfac] at h
    omega
  refine CFSG.ABGLocalTools.isSylowOf_of_card (hS.le.trans le_sup_left) ?_
  rw [hS.card_eq, h4]

section Setting

variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P : Subgroup G}

theorem pCoreOf_kTwenty_le (hset : Setting204 G A M L N c T i j P) :
    CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hset.sylow.le
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    ((hTM.trans hMK).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))

theorem inf_inSubgroup_pPrimeCore_le (hset : Setting204 G A M L N c T i j P) {H : Subgroup G}
    (hKH : kTwenty M c ≤ H) :
    kTwenty M c ⊓ inSubgroup (CFSG.pPrimeCore 3) H ≤ CFSG.Open.pCoreOf 2 (kTwenty M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set K₀ := inSubgroup (CFSG.pPrimeCore 3) H with hK₀def
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := Res6.isSimpleGroup_of_setting204 hset
  set W : Subgroup ↥K := (K ⊓ K₀).subgroupOf K with hWdef
  have hWn : W.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_
    exact Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk)
      (Res6.le_normalizer_inSubgroup_pPrimeCore 3 H (hKH hk))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hWπ : (W.map π).Normal := hWn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map π) with h | h
  · rintro x ⟨hxK, hxK₀⟩
    have hx : π ⟨x, hxK⟩ ∈ W.map π := ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr ⟨hxK, hxK₀⟩, rfl⟩
    rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact (CFSG.mem_openPCoreOf_iff _).mpr hx
  · exfalso
    have hc3 := Res6.orderOf_c_of_setting204 hset
    have hcK : c ∈ K := self_mem_normalClosureIn M c
    have hcO : (⟨c, hcK⟩ : ↥K) ∉ CFSG.pCore 2 ↥K := by
      intro hc
      exact Res6.not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hc3
        ((CFSG.mem_openPCoreOf_iff _).mpr hc)
    have hord : orderOf (π ⟨c, hcK⟩) = 3 := by
      have h1 : π ⟨c, hcK⟩ ^ 3 = 1 := by
        rw [← map_pow, show (⟨c, hcK⟩ : ↥K) ^ 3 = 1 from Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc3, pow_orderOf_eq_one]), map_one]
      have h2 : π ⟨c, hcK⟩ ≠ 1 := by
        rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        exact hcO
      exact orderOf_eq_prime h1 h2
    have hmem : π ⟨c, hcK⟩ ∈ W.map π := by rw [h]; exact Subgroup.mem_top _
    have hdvd : 3 ∣ Nat.card (W.map π) := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    have hWc : Nat.Coprime 3 (Nat.card W) := by
      have heq : Nat.card W = Nat.card (K ⊓ K₀ : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [heq]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (Res6.coprime_card_inSubgroup_pPrimeCore 3 H)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hWc
      (hdvd.trans (Subgroup.card_map_dvd W π))

theorem pCoreOf_le_of_mem_scriptM (hset : Setting204 G A M L N c T i j P) {X : Subgroup G}
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hXO : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRKT : R ≤ kTwenty M c ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hZ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 X ⊔ R : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_sup_of_normal_left' hR2
      ((hRKT.trans hKTX).trans hXO)
  have hZmem : (CFSG.Open.pCoreOf 2 X ⊔ R : Subgroup G) ∈
      invariantPiSubgroups ⊤ (kTwenty M c ⊔ T) (piOf 2) := by
    refine (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hZ2, fun x hx => ?_⟩
    exact Res6.mem_normalizer_sup (hXO (hKTX hx))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx)
  have heq := (mem_maxInvariantPiSubgroups_iff.mp hset.maxInvariant).2 _ hZmem le_sup_right
  exact le_sup_left.trans heq.le

theorem isSylowOf_sup_inf_normalizer (hset : Setting204 G A M L N c T i j P) {X : Subgroup G}
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))
      (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ⊔ (oThreePrimeYR M X T c ⊓
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set D := K₀ ⊓ Subgroup.normalizer (R : Set G) with hDdef
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKX : K ≤ X := le_sup_left.trans hKTX
  have hTX : T ≤ X := le_sup_right.trans hKTX
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYRK₀ : Y ⊔ R ≤ Subgroup.normalizer (K₀ : Set G) :=
    Res6.le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R)
  have hKK₀ : K ≤ Subgroup.normalizer (K₀ : Set G) := (hKY.trans le_sup_left).trans hYRK₀
  have hKTR : K ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTX.trans (le_normalizer_normalClosureIn X c)
  have hTYR : T ≤ Subgroup.normalizer ((Y ⊔ R : Subgroup G) : Set G) := fun t ht =>
    Res6.mem_normalizer_sup (hTY ht) (hKTR (Subgroup.mem_sup_right ht))
  have hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G) :=
    hTYR.trans (Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R))
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := inf_le_right
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := fun t ht =>
    Sec20.mem_normalizer_inf_of_mem (hTK₀ ht)
      (Subgroup.le_normalizer (hKTR (Subgroup.mem_sup_right ht)))
  have hcomm : ∀ d ∈ D, ∀ k ∈ K, k * d * k⁻¹ * d⁻¹ ∈ R := by
    intro d hd k hk
    have h1 : k * d * k⁻¹ * d⁻¹ ∈ K := by
      have h : d * k⁻¹ * d⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hset.normalizer_le hd.2) _).mp (K.inv_mem hk)
      have e : k * d * k⁻¹ * d⁻¹ = k * (d * k⁻¹ * d⁻¹) := by group
      rw [e]
      exact K.mul_mem hk h
    have h2 : k * d * k⁻¹ * d⁻¹ ∈ K₀ :=
      K₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKK₀ hk) d).mp hd.1) (K₀.inv_mem hd.1)
    exact pCoreOf_kTwenty_le hset
      (inf_inSubgroup_pPrimeCore_le hset (hKY.trans le_sup_left) ⟨h1, h2⟩)
  have hRD : ∀ p ∈ R ⊔ D, ∀ k ∈ K, k * p * k⁻¹ * p⁻¹ ∈ R := by
    intro p hp k hk
    have hp' : p ∈ ((D : Set G) * (R : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D R hDR, sup_comm]
      exact hp
    obtain ⟨d, hd, r, hr, rfl⟩ := hp'
    have e : k * (d * r) * k⁻¹ * (d * r)⁻¹ =
        (k * d * k⁻¹ * d⁻¹) * (d * (k * r * k⁻¹ * r⁻¹) * d⁻¹) := by group
    rw [e]
    refine R.mul_mem (hcomm d hd k hk) ?_
    have hkr : k * r * k⁻¹ * r⁻¹ ∈ R :=
      R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKTR (Subgroup.mem_sup_left hk)) r).mp hr)
        (R.inv_mem hr)
    exact (Subgroup.mem_normalizer_iff.mp (hDR hd) _).mp hkr
  have hT2 : IsPGroup 2 T := hset.sylow.isPGroup
  obtain ⟨S', hS', hTS'⟩ := Sec20.exists_isSylowOf_le hT2 (le_sup_right : T ≤ (R ⊔ D) ⊔ T)
  have hTRD : T ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) := fun t ht =>
    Res6.mem_normalizer_sup (hKTR (Subgroup.mem_sup_right ht)) (hTD ht)
  have hRDn : (R ⊔ D) ⊔ T ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hTRD
  have hQsyl := hS'.inf_of_le_normalizer le_sup_left hRDn
  have hRR : (R ⊔ D) ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hDR) (le_sup_right.trans hKTR)
  have hRS' : R ≤ S' := Res6.le_of_isSylowOf_of_le_normalizer hR2
    (le_sup_left.trans le_sup_left) le_rfl hRR hS'
  have hRQ : R ≤ S' ⊓ (R ⊔ D) := le_inf hRS' le_sup_left
  have hQinv : S' ⊓ (R ⊔ D) ∈ invariantPiSubgroups ⊤ (K ⊔ T) (piOf 2) := by
    refine (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hQsyl.isPGroup, ?_⟩
    refine sup_le (fun k hk => ?_) (fun t ht => ?_)
    · refine Subgroup.mem_normalizer_fintype fun q hq => ?_
      have e : k * q * k⁻¹ = (k * q * k⁻¹ * q⁻¹) * q := by group
      rw [e]
      exact (S' ⊓ (R ⊔ D)).mul_mem (hRQ (hRD q hq.2 k hk)) hq
    · exact Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hTS' ht)) (hTRD ht)
  have heq : S' ⊓ (R ⊔ D) = R :=
    (mem_maxInvariantPiSubgroups_iff.mp hset.maxInvariant).2 _ hQinv hRQ
  rw [heq] at hQsyl
  exact hQsyl

theorem le_of_isPGroup_of_le_oThreePrimeYR (hset : Setting204 G A M L N c T i j P)
    {X : Subgroup G} (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQK₀ : Q ≤ oThreePrimeYR M X T c)
    (hRQ : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  refine Sec15.le_of_inf_normalizer_le155 hR2 hQ hRQ ?_
  set Q' := Q ⊓ Subgroup.normalizer (R : Set G) with hQ'def
  have hQ'2 : IsPGroup 2 Q' := hQ.to_le inf_le_left
  have hRQ'2 : IsPGroup 2 (R ⊔ Q' : Subgroup G) := hR2.to_sup_of_normal_left' hQ'2 inf_le_right
  have hle : R ⊔ Q' ≤ R ⊔ (oThreePrimeYR M X T c ⊓ Subgroup.normalizer (R : Set G)) :=
    sup_le_sup_left (inf_le_inf_right _ hQK₀) _
  have heq := (isSylowOf_sup_inf_normalizer hset hX).eq_of_le le_sup_left hle hRQ'2
  exact le_sup_right.trans heq.le

end Setting

@[expose] def CoverYR (M X T : Subgroup G) (c : G) (H : Subgroup G) : Prop :=
  CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ H ∧
    H ≤ yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ∧
    H ⊔ oThreePrimeYR M X T c = yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)

theorem exists_minimal_coverYR (M X T : Subgroup G) (c : G) :
    ∃ G₀ : Subgroup G, Minimal (CoverYR M X T c) G₀ := by
  have h : CoverYR M X T c (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) :=
    ⟨le_sup_right, le_rfl, sup_eq_left.mpr (Res6.inSubgroup_pPrimeCore_le 3 _)⟩
  obtain ⟨G₀, -, hG₀⟩ := Finite.exists_le_minimal h
  exact ⟨G₀, hG₀⟩

section MinimalCover

variable {M X T : Subgroup G} {c : G} {G₀ : Subgroup G}

theorem inSubgroup_pPrimeCore_eq_of_minimal (hG₀ : Minimal (CoverYR M X T c) G₀) :
    inSubgroup (CFSG.pPrimeCore 3) G₀ = G₀ ⊓ oThreePrimeYR M X T c :=
  inSubgroup_pPrimeCore_eq_inf hG₀.prop.2.1 hG₀.prop.2.2

theorem pCoreOf_le_inSubgroup_pPrimeCore (H : Subgroup G) :
    CFSG.Open.pCoreOf 2 H ≤ inSubgroup (CFSG.pPrimeCore 3) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Res6.le_inSubgroup_pPrimeCore (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    (Res6.coprime_card_of_isPGroup Nat.prime_three (by norm_num)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H))

theorem isSylowOf_pCoreOf_of_minimal (hG₀ : Minimal (CoverYR M X T c) G₀) :
    CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 G₀)
      (inSubgroup (CFSG.pPrimeCore 3) G₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set O := inSubgroup (CFSG.pPrimeCore 3) G₀ with hOdef
  obtain ⟨hRG, hGYR, hcov⟩ := hG₀.prop
  have hGO : G₀ ≤ Subgroup.normalizer (O : Set G) := Res6.le_normalizer_inSubgroup_pPrimeCore 3 G₀
  have hOG : O ≤ G₀ := Res6.inSubgroup_pPrimeCore_le 3 G₀
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨S₁, hS₁, hRS₁⟩ := Sec20.exists_isSylowOf_le hR2 (le_sup_left : R ≤ R ⊔ O)
  have hROn : R ⊔ O ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (hRG.trans hGO) Subgroup.le_normalizer
  have hP₁ := hS₁.inf_of_le_normalizer le_sup_right hROn
  have hRP₁ : R ≤ Subgroup.normalizer ((S₁ ⊓ O : Subgroup G) : Set G) := fun r hr =>
    Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hRS₁ hr)) (hGO (hRG hr))
  have hH₁ : CoverYR M X T c (G₀ ⊓ Subgroup.normalizer ((S₁ ⊓ O : Subgroup G) : Set G)) := by
    refine ⟨le_inf hRG hRP₁, inf_le_left.trans hGYR, le_antisymm
      (sup_le (inf_le_left.trans hGYR) (Res6.inSubgroup_pPrimeCore_le 3 _)) ?_⟩
    rw [← hcov]
    refine sup_le (fun g hg => ?_) le_sup_right
    obtain ⟨n, hn, m, hm, rfl⟩ := Sec18.exists_mul_of_isSylowOf hP₁ hGO hg
    have hmG : m ∈ G₀ := by
      have h := G₀.mul_mem (G₀.inv_mem (hOG hn)) hg
      rwa [inv_mul_cancel_left] at h
    have hnK₀ : n ∈ oThreePrimeYR M X T c := by
      have h := hn
      rw [hOdef, inSubgroup_pPrimeCore_eq_of_minimal hG₀] at h
      exact h.2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnK₀) (Subgroup.mem_sup_left ⟨hmG, hm⟩)
  have hle : G₀ ≤ G₀ ⊓ Subgroup.normalizer ((S₁ ⊓ O : Subgroup G) : Set G) :=
    hG₀.2 hH₁ inf_le_left
  have hP₁Q : S₁ ⊓ O ≤ CFSG.Open.pCoreOf 2 G₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans hOG)
      (hle.trans inf_le_right) hP₁.isPGroup
  have heq := hP₁.eq_of_le hP₁Q (pCoreOf_le_inSubgroup_pPrimeCore G₀)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀)
  rw [heq]
  exact hP₁

end MinimalCover

section SettingCover

variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P : Subgroup G}
  {X G₀ : Subgroup G}

theorem pCoreOf_le_of_minimal (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hG₀ : Minimal (CoverYR M X T c) G₀) :
    CFSG.Open.pCoreOf 2 G₀ ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRG, hGYR, hcov⟩ := hG₀.prop
  have hQ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have hGQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀
  have hQK₀ : CFSG.Open.pCoreOf 2 G₀ ≤ oThreePrimeYR M X T c :=
    le_inSubgroup_pPrimeCore_of_sup_eq ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₀).trans hGYR) hGQ
      hcov (Res6.coprime_card_of_isPGroup Nat.prime_three (by norm_num) hQ2)
  exact le_of_isPGroup_of_le_oThreePrimeYR hset hX hQ2 hQK₀ (hRG.trans hGQ)

theorem eq_top_of_minimal (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hG₀ : Minimal (CoverYR M X T c) G₀) (H : Subgroup ↥G₀) (hQH : CFSG.pCore 2 ↥G₀ ≤ H)
    (hcovH : H ⊔ CFSG.pPrimeCore 3 ↥G₀ = ⊤) : H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set O := inSubgroup (CFSG.pPrimeCore 3) G₀ with hOdef
  set Q := CFSG.Open.pCoreOf 2 G₀ with hQdef
  set H' := H.map G₀.subtype with hH'def
  obtain ⟨hRG, hGYR, hcov⟩ := hG₀.prop
  have hGO : G₀ ≤ Subgroup.normalizer (O : Set G) := Res6.le_normalizer_inSubgroup_pPrimeCore 3 G₀
  have hOG : O ≤ G₀ := Res6.inSubgroup_pPrimeCore_le 3 G₀
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have hH'G : H' ≤ G₀ := Subgroup.map_subtype_le H
  have hH'O : H' ⊔ O = G₀ := by
    have h := congrArg (Subgroup.map G₀.subtype) hcovH
    rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hQH' : Q ≤ H' := Subgroup.map_mono hQH
  have hQO : Q ≤ O := pCoreOf_le_inSubgroup_pPrimeCore G₀
  have hQsyl := isSylowOf_pCoreOf_of_minimal hG₀
  have hQR : Q ≤ R := pCoreOf_le_of_minimal hset hX hG₀
  set V := H' ⊓ (R ⊔ O) with hVdef
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans (hH'G.trans hGO)
  have hQV : Q ≤ V := le_inf hQH' (hQO.trans le_sup_right)
  have hVOeq : V ⊔ O = R ⊔ O := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) (sup_le (fun r hr => ?_) le_sup_right)
    have hr' : r ∈ ((H' : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H' O (hH'G.trans hGO), hH'O]
      exact hRG hr
    obtain ⟨h, hh, o, ho, rfl⟩ := hr'
    have hhRO : h ∈ R ⊔ O := by
      have h1 := (R ⊔ O).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right (O.inv_mem ho))
      rwa [mul_inv_cancel_right] at h1
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hh, hhRO⟩) (Subgroup.mem_sup_right ho)
  obtain ⟨S, hS, -⟩ := Sec20.exists_isSylowOf_le hQ2 hQV
  have hSRO : CFSG.ABGLocalTools.IsSylowOf 2 S (R ⊔ O) := by
    rw [← hVOeq]
    exact isSylowOf_sup_of_le hVO hQsyl hQV hS
  have hRR : CFSG.ABGLocalTools.IsSylowOf 2 R R :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_rfl, hR2, by rw [Subgroup.relIndex_self]; norm_num⟩
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R (R ⊔ O) :=
    isSylowOf_sup_of_le (hRG.trans hGO) hQsyl hQR hRR
  obtain ⟨n, hn, hSn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hRsyl hSRO
  have hnG : n ∈ G₀ := (sup_le hRG hOG) hn
  set H'' := H'.map (MulAut.conj n⁻¹).toMonoidHom with hH''def
  have hRH'' : R ≤ H'' := by
    intro r hr
    have hnr : n * r * n⁻¹ ∈ S := by rw [hSn]; exact ⟨r, hr, rfl⟩
    refine ⟨n * r * n⁻¹, (hS.le hnr).1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hH''G : H'' ≤ G₀ := by
    rintro _ ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hnG) (hH'G hh)) (G₀.inv_mem (G₀.inv_mem hnG))
  have hcov'' : CoverYR M X T c H'' := by
    refine ⟨hRH'', hH''G.trans hGYR, le_antisymm
      (sup_le (hH''G.trans hGYR) (Res6.inSubgroup_pPrimeCore_le 3 _)) ?_⟩
    rw [← hcov]
    refine sup_le (fun g hg => ?_) le_sup_right
    have hg' : n * g * n⁻¹ ∈ ((H' : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H' O (hH'G.trans hGO), hH'O]
      exact G₀.mul_mem (G₀.mul_mem hnG hg) (G₀.inv_mem hnG)
    obtain ⟨h, hh, o, ho, hho⟩ := hg'
    have e : g = (n⁻¹ * h * n) * (n⁻¹ * o * n) := by
      calc g = n⁻¹ * (n * g * n⁻¹) * n := by group
        _ = n⁻¹ * (h * o) * n := by rw [← hho]
        _ = (n⁻¹ * h * n) * (n⁻¹ * o * n) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, hh, by simp [MulAut.conj_apply]⟩)
      (Subgroup.mem_sup_right ?_)
    have hoO : n⁻¹ * o * n ∈ O := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hGO (G₀.inv_mem hnG)) o).mp ho
      rwa [inv_inv] at h1
    rw [hOdef, inSubgroup_pPrimeCore_eq_of_minimal hG₀] at hoO
    exact hoO.2
  have hG₀H'' : G₀ ≤ H'' := hG₀.2 hcov'' hH''G
  have hcard : Nat.card G₀ ≤ Nat.card H' := by
    have h1 : Nat.card H'' = Nat.card H' :=
      Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective
    rw [← h1]
    exact Subgroup.card_le_of_le hG₀H''
  have hH'eq : H' = G₀ := Subgroup.eq_of_le_of_card_ge hH'G hcard
  apply Subgroup.map_injective G₀.subtype_injective
  rw [← hH'def, hH'eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem generalizedFitting_eq_of_minimal (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hG₀ : Minimal (CoverYR M X T c) G₀) :
    CFSG.generalizedFitting ↥G₀ = CFSG.pCore 2 ↥G₀ := by
  obtain ⟨hRG, hGYR, -⟩ := hG₀.prop
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hcX : c ∈ X := hKTX (Subgroup.mem_sup_left (self_mem_normalClosureIn M c))
  have hYRX : yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ X :=
    sup_le (normalClosureIn_le hcX) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX)
  have hX2 : CFSG.Assembly.IsTwoLocal X := by
    obtain ⟨Q, hQ, hQ2, hXQ⟩ := hX.1.1
    exact ⟨Q, hQ, hQ2, hXQ⟩
  exact Sec18.Item183NMProof.generalizedFitting_eq_of_pCoreOf_le hset.charTwoType hX2
    (hGYR.trans hYRX) ((pCoreOf_le_of_mem_scriptM hset hX).trans hRG)

end SettingCover

theorem eq_top_of_isPerfect_of_isPGroup {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (N : Subgroup Γ) [N.Normal] (h2 : IsPGroup 2 (Γ ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial (Γ ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  have : Group.IsPerfect (Γ ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have : Group.IsNilpotent (Γ ⧸ N) := h2.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (Γ ⧸ N) inferInstance

section Back

variable {M X T : Subgroup G} {c : G}

theorem coveredByNormalizer_of_coverYR
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G))
    (hY : Group.IsPerfect ↥(yAlpha M X T c)) {H : Subgroup G} (hH : CoverYR M X T c H)
    {k : Fin 4} (hHk : H ≤ Subgroup.normalizer
      (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) k : Set G)) :
    CoveredByNormalizer M X T c k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRH, hHYR, hcov⟩ := hH
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set N₁ := Subgroup.normalizer (Sec18.fourChar R k : Set G) with hN₁def
  set W := Y ⊓ N₁ with hWdef
  haveI := CFSG.pPrimeCore_normal (p := 3) (G := ↥YR)
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYRY : YR ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hRY
  have hHK₀ : H ≤ Subgroup.normalizer (K₀ : Set G) :=
    hHYR.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 YR)
  have hdec : ∀ x : ↥YR, ∃ y ∈ W, ∃ r ∈ R, ∃ (hy : y ∈ YR) (hr : r ∈ YR),
      π x = π ⟨y, hy⟩ * π ⟨r, hr⟩ := by
    intro x
    have hx : (x : G) ∈ ((H : Set G) * (K₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K₀ hHK₀, hcov]
      exact x.2
    obtain ⟨h, hh, k₀, hk₀, hhk⟩ := hx
    have hh' : h ∈ ((Y : Set G) * (R : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY]
      exact hHYR hh
    obtain ⟨y, hy, r, hr, rfl⟩ := hh'
    have hrN : r ∈ N₁ := hHk (hRH hr)
    have hyN : y ∈ N₁ := by
      have h1 := N₁.mul_mem (hHk hh) (N₁.inv_mem hrN)
      rwa [mul_inv_cancel_right] at h1
    refine ⟨y, ⟨hy, hyN⟩, r, hr, Subgroup.mem_sup_left hy, Subgroup.mem_sup_right hr, ?_⟩
    obtain ⟨k', hk', hk'k⟩ := Subgroup.mem_map.mp hk₀
    have hxe : x = ⟨y, Subgroup.mem_sup_left hy⟩ * ⟨r, Subgroup.mem_sup_right hr⟩ * k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hhk]
      exact congrArg _ hk'k.symm
    have hk1 : π k' = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk'
    rw [hxe, map_mul, hk1, mul_one, map_mul]
  set Wb := (W.subgroupOf YR).map π with hWbdef
  have hWbn : Wb.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨y, hyW, r, hr, hy, hr', hxe⟩ := hdec x
    rw [hxe]
    have hyr : (y * r) * (w : G) * (y * r)⁻¹ ∈ W := by
      have hyrN : y * r ∈ N₁ := N₁.mul_mem hyW.2 (hHk (hRH hr))
      have hyrY : y * r ∈ Subgroup.normalizer (Y : Set G) :=
        hYRY (YR.mul_mem (Subgroup.mem_sup_left hyW.1) (Subgroup.mem_sup_right hr))
      have hwW : (w : G) ∈ W := hw
      exact ⟨(Subgroup.mem_normalizer_iff.mp hyrY _).mp hwW.1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hyrN) _).mp hwW.2⟩
    refine ⟨⟨y, hy⟩ * ⟨r, hr'⟩ * w * (⟨y, hy⟩ * ⟨r, hr'⟩)⁻¹, hyr, ?_⟩
    simp only [map_mul, map_inv]
  set Yb := yAlpha M X T c with hYbdef
  have hYbWb : Yb ≤ Wb := by
    haveI : (Wb.subgroupOf Yb).Normal := Subgroup.Normal.subgroupOf hWbn Yb
    have h2 : IsPGroup 2 (↥Yb ⧸ Wb.subgroupOf Yb) := by
      intro q
      obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y₀, hy₀, rfl⟩ := hz
      obtain ⟨y, hyW, r, hr, hy, hr', hxe⟩ := hdec y₀
      obtain ⟨a, ha⟩ := hR2 ⟨r, hr⟩
      have hyb : π ⟨y, hy⟩ ∈ Yb := ⟨⟨y, hy⟩, hyW.1, rfl⟩
      have hrb : π ⟨r, hr'⟩ ∈ Yb := by
        have h1 := Yb.mul_mem (Yb.inv_mem hyb) (show π y₀ ∈ Yb from ⟨y₀, hy₀, rfl⟩)
        rwa [hxe, inv_mul_cancel_left] at h1
      have hywb : (⟨π ⟨y, hy⟩, hyb⟩ : ↥Yb) ∈ Wb.subgroupOf Yb :=
        Subgroup.mem_subgroupOf.mpr ⟨⟨y, hy⟩, hyW, rfl⟩
      have he : (⟨π y₀, ⟨y₀, hy₀, rfl⟩⟩ : ↥Yb) = ⟨π ⟨y, hy⟩, hyb⟩ * ⟨π ⟨r, hr'⟩, hrb⟩ :=
        Subtype.ext hxe
      refine ⟨a, ?_⟩
      rw [he, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hywb, one_mul,
        ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have hra : (⟨π ⟨r, hr'⟩, hrb⟩ : ↥Yb) ^ 2 ^ a = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
        have : (⟨r, hr'⟩ : ↥YR) ^ 2 ^ a = 1 := by
          apply Subtype.ext
          have := congrArg Subtype.val ha
          simpa using this
        rw [this, map_one]
      rw [hra]
      exact Subgroup.one_mem _
    have htop := eq_top_of_isPerfect_of_isPGroup (Wb.subgroupOf Yb) h2
    intro z hz
    have : (⟨z, hz⟩ : ↥Yb) ∈ Wb.subgroupOf Yb := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  intro y hy
  have hyYR : y ∈ YR := Subgroup.mem_sup_left hy
  have hyb : π ⟨y, hyYR⟩ ∈ Yb := ⟨⟨y, hyYR⟩, hy, rfl⟩
  obtain ⟨w, hw, hwe⟩ := hYbWb hyb
  have hk : (w⁻¹ * ⟨y, hyYR⟩ : ↥YR) ∈ CFSG.pPrimeCore 3 ↥YR := by
    rw [← QuotientGroup.eq]
    exact hwe
  have hk₀ : (w : G)⁻¹ * y ∈ K₀ := ⟨_, hk, rfl⟩
  have hwW : (w : G) ∈ W := hw
  have e : y = (w : G) * ((w : G)⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwW) (Subgroup.mem_sup_right hk₀)

end Back

end AscBridge

end CFSG.RankThree.PartTwo.Sec20
