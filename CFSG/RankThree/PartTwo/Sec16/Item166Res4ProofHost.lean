module

public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Abstract

variable {U : Type} [Group U] [Finite U]

theorem inf_pPrimeCore_eq_bot {P : Subgroup U} (hP : IsPGroup 2 P) :
    P ⊓ CFSG.pPrimeCore 2 U = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left k (CFSG.pPrimeCore_coprime_card (p := 2) (G := U))

theorem eq_one_of_mem_pPrimeCore {q : U} (hq : q ∈ CFSG.pPrimeCore 2 U) {k : ℕ}
    (hk : q ^ 2 ^ k = 1) : q = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf q ∣ Nat.card (CFSG.pPrimeCore 2 U) := by
    rw [← Subgroup.orderOf_mk (ha := hq)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.pPrimeCore 2 U)) :=
    Nat.Coprime.pow_left k (CFSG.pPrimeCore_coprime_card (p := 2) (G := U))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem pPrimeCore_le_centralizer_pCore :
    CFSG.pPrimeCore 2 U ≤ Subgroup.centralizer (CFSG.pCore 2 U : Set U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ⁅CFSG.pPrimeCore 2 U, CFSG.pCore 2 U⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_le_inf _ _).trans ?_)
    rw [inf_comm, inf_pPrimeCore_eq_bot CFSG.pCore_isPGroup]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc

theorem centralizer_pCore_le_of_center
    (hF : generalizedFitting U = CFSG.pCore 2 U ⊔ Subgroup.center U) :
    Subgroup.centralizer (CFSG.pCore 2 U : Set U) ≤ CFSG.pCore 2 U ⊔ Subgroup.center U := by
  intro x hx
  rw [← hF]
  refine CFSG.centralizer_generalizedFitting_le U ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hF] at hy
  have hle : CFSG.pCore 2 U ⊔ Subgroup.center U ≤ Subgroup.centralizer ({x} : Set U) := by
    refine sup_le (fun p hp => ?_) (fun z hz => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx p hp)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hz x).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem pPrimeCore_two_le_center
    (hF : generalizedFitting U = CFSG.pCore 2 U ⊔ Subgroup.center U) :
    CFSG.pPrimeCore 2 U ≤ Subgroup.center U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center U) with hπ
  have hle : CFSG.pPrimeCore 2 U ≤ CFSG.pCore 2 U ⊔ Subgroup.center U :=
    pPrimeCore_le_centralizer_pCore.trans (centralizer_pCore_le_of_center hF)
  have hZ : (Subgroup.center U).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hmap : (CFSG.pPrimeCore 2 U).map π ≤ (CFSG.pCore 2 U).map π := by
    refine (Subgroup.map_mono hle).trans ?_
    rw [Subgroup.map_sup, hZ, sup_bot_eq]
  have h2 : IsPGroup 2 ((CFSG.pPrimeCore 2 U).map π) :=
    (CFSG.pCore_isPGroup.map π).to_le hmap
  have hcop : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 U).map π)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := U))
  have hbot : (CFSG.pPrimeCore 2 U).map π = ⊥ := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at hcop
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · exact absurd hcop (by rw [Nat.coprime_pow_right_iff (Nat.succ_pos k)]; decide)
  rwa [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot

theorem exists_pow_mem_pPrimeCore {z : U} (hz : z ∈ Subgroup.center U) :
    ∃ b : ℕ, z ^ 2 ^ b ∈ CFSG.pPrimeCore 2 U := by
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨b, ?_⟩
  have hord : orderOf (z ^ 2 ^ b) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero b two_ne_zero) (hbm ▸ Dvd.intro m rfl), hbm,
      Nat.mul_div_cancel_left m (pow_pos two_pos b)]
  have hcen : Subgroup.zpowers (z ^ 2 ^ b) ≤ Subgroup.center U :=
    Subgroup.zpowers_le.mpr (pow_mem hz _)
  have hnorm : (Subgroup.zpowers (z ^ 2 ^ b)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.mp (hcen hn) g, mul_inv_cancel_right]
      exact hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers (z ^ 2 ^ b))) := by
    rw [Nat.card_zpowers, hord]
    exact Nat.coprime_two_left.mpr hm
  exact (le_sSup ⟨hnorm, hcop⟩ : Subgroup.zpowers (z ^ 2 ^ b) ≤ CFSG.pPrimeCore 2 U)
    (Subgroup.mem_zpowers _)

theorem centralizer_pCore_quot_le
    (hF : generalizedFitting U = CFSG.pCore 2 U ⊔ Subgroup.center U) :
    Subgroup.centralizer (CFSG.pCore 2 (U ⧸ CFSG.pPrimeCore 2 U) : Set (U ⧸ CFSG.pPrimeCore 2 U)) ≤
      CFSG.pCore 2 (U ⧸ CFSG.pPrimeCore 2 U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pPrimeCore 2 U with hQ
  set P := CFSG.pCore 2 U with hP
  set π := QuotientGroup.mk' Q with hπ
  have hPbar : P.map π ≤ CFSG.pCore 2 (U ⧸ Q) :=
    le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := U)).map π (QuotientGroup.mk'_surjective Q),
      CFSG.pCore_isPGroup.map π⟩
  have hC2 : IsPGroup 2 (Subgroup.centralizer (CFSG.pCore 2 (U ⧸ Q) : Set (U ⧸ Q))) := by
    rintro ⟨xbar, hx⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q xbar
    have hxP : x ∈ Subgroup.centralizer (P : Set U) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hc := Subgroup.mem_centralizer_iff.mp hx (π p) (hPbar ⟨p, hp, rfl⟩)
      have hQmem : p * x * p⁻¹ * x⁻¹ ∈ Q := by
        rw [← QuotientGroup.eq_one_iff]
        change π (p * x * p⁻¹ * x⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right,
          mul_inv_cancel]
      have hPmem : p * x * p⁻¹ * x⁻¹ ∈ P := by
        have h1 : x * p⁻¹ * x⁻¹ ∈ P :=
          (CFSG.pCore_normal (p := 2) (G := U)).conj_mem _ (inv_mem hp) x
        have h2 := mul_mem hp h1
        rwa [show p * (x * p⁻¹ * x⁻¹) = p * x * p⁻¹ * x⁻¹ by group] at h2
      have h1 : p * x * p⁻¹ * x⁻¹ = 1 := by
        have hmem : p * x * p⁻¹ * x⁻¹ ∈ P ⊓ Q := ⟨hPmem, hQmem⟩
        rwa [inf_pPrimeCore_eq_bot CFSG.pCore_isPGroup, Subgroup.mem_bot] at hmem
      calc p * x = (p * x * p⁻¹ * x⁻¹) * (x * p) := by group
        _ = x * p := by rw [h1, one_mul]
    have hxPZ := centralizer_pCore_le_of_center hF hxP
    rw [← SetLike.mem_coe, Subgroup.mul_normal P (Subgroup.center U)] at hxPZ
    obtain ⟨p, hp, z, hz, rfl⟩ := hxPZ
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := U) ⟨p, hp⟩
    obtain ⟨b, hb⟩ := exists_pow_mem_pPrimeCore hz
    have hpa : p ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    have hcomm : Commute p z := Subgroup.mem_center_iff.mp hz p
    have hp1 : p ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, hpa, one_pow]
    have hz1 : π (z ^ 2 ^ (a + b)) = 1 := by
      rw [pow_add, mul_comm (2 ^ a) (2 ^ b), pow_mul, map_pow,
        show π (z ^ 2 ^ b) = 1 from (QuotientGroup.eq_one_iff _).mpr hb, one_pow]
    change π (p * z) ^ 2 ^ (a + b) = 1
    rw [← map_pow, hcomm.mul_pow, map_mul, hp1, map_one, one_mul, hz1]
  exact le_sSup ⟨Subgroup.normal_centralizer, hC2⟩

theorem stellmacherWSz_map_normal_of_center (hU3 : ¬ 3 ∣ Nat.card U)
    (hSzU : S4Free.SzSections U)
    (hF : generalizedFitting U = CFSG.pCore 2 U ⊔ Subgroup.center U) {S : Type} [Group S]
    (ι : S →* U) (hι : Function.Injective ι) (hsyl : ∃ P : Sylow 2 U, (P : Subgroup U) = ι.range) :
    ((S4Free.stellmacherWSz.{0, 0} S).map ι).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pPrimeCore 2 U with hQ
  set π := QuotientGroup.mk' Q with hπ
  obtain ⟨P0, hP0⟩ := hsyl
  have hS2 : IsPGroup 2 ι.range := hP0 ▸ P0.isPGroup'
  have hfin : Finite S := Finite.of_injective ι hι
  have hadm : S4Free.IsAdmissibleHost (π.comp ι) := by
    refine S4Free.isAdmissibleHost_of_not_three_dvd ?_ ?_ ?_ ?_
    · exact fun h3 => hU3 (h3.trans (Subgroup.card_quotient_dvd_card Q))
    · intro s t hst
      apply hι
      have h1 : (ι s)⁻¹ * ι t ∈ Q := QuotientGroup.eq.mp hst
      have h2 : (ι s)⁻¹ * ι t ∈ ι.range := ⟨s⁻¹ * t, by rw [map_mul, map_inv]⟩
      have h3 : (ι s)⁻¹ * ι t ∈ ι.range ⊓ Q := ⟨h2, h1⟩
      rw [inf_pPrimeCore_eq_bot hS2, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact h3
    · refine ⟨P0.mapSurjective (QuotientGroup.mk'_surjective Q), ?_⟩
      rw [Sylow.coe_mapSurjective, hP0, MonoidHom.range_comp]
    · rw [Sec15.oTwo_eq_pCore]
      exact centralizer_pCore_quot_le hF
  have hW := S4Free.stellmacherWSz_normal hadm (hSzU.quotient Q)
  set W := S4Free.stellmacherWSz.{0, 0} S with hWdef
  have hQc := pPrimeCore_two_le_center hF
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hn
  have hmem : π (g * ι w * g⁻¹) ∈ W.map (π.comp ι) := by
    rw [map_mul, map_mul, map_inv]
    exact hW.conj_mem _ ⟨w, hw, rfl⟩ (π g)
  obtain ⟨w', hw', hw'eq⟩ := hmem
  have hq : (ι w')⁻¹ * (g * ι w * g⁻¹) ∈ Q := QuotientGroup.eq.mp hw'eq
  set q := (ι w')⁻¹ * (g * ι w * g⁻¹) with hqdef
  have hqc : q ∈ Subgroup.center U := hQc hq
  have hSpow : ∀ s : S, s ^ Nat.card S = 1 := fun s => pow_card_eq_one'
  have hcardS : ∃ k, Nat.card S = 2 ^ k := by
    have h := hS2.exists_card_eq
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv)
  obtain ⟨k, hk⟩ := hcardS
  have hq1 : q ^ 2 ^ k = 1 := by
    have hqeq : g * ι w * g⁻¹ = ι w' * q := by rw [hqdef, mul_inv_cancel_left]
    have hcomm : Commute (ι w') q := Subgroup.mem_center_iff.mp hqc (ι w')
    have h1 : (g * ι w * g⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow, ← map_pow, ← hk, hSpow, map_one, mul_one, mul_inv_cancel]
    rw [hqeq, hcomm.mul_pow, ← map_pow, ← hk, hSpow, map_one, one_mul] at h1
    rwa [hk] at h1
  have hq1' : q = 1 := eq_one_of_mem_pPrimeCore hq hq1
  have hfinal : g * ι w * g⁻¹ = ι w' := by
    have h := hq1'
    rw [hqdef, inv_mul_eq_one] at h
    exact h.symm
  rw [hfinal]
  exact ⟨w', hw', rfl⟩

end Abstract

theorem le_normalizer_stellmacherSub_of_center {G : Type} [Group G] [Finite G]
    (hSz : KFacts.KPSz) (hR : TheoremFourHyp G) {T U : Subgroup G}
    (hTU : T ≤ U) (hU3 : ¬ 3 ∣ Nat.card U) (hsyl : CFSG.Open.fusionIsSylowIn 2 T U)
    (hF : generalizedFitting ↥U = CFSG.pCore 2 ↥U ⊔ Subgroup.center ↥U) :
    U ≤ Subgroup.normalizer (Proof165.stellmacherSub T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : ↥T →* ↥U := Subgroup.inclusion hTU with hι
  have hrange : ι.range = T.subgroupOf U := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr s.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  obtain ⟨P, hP⟩ := Proof165.sylow_of_fusionIsSylowIn hsyl
  set W := S4Free.stellmacherWSz.{0, 0} ↥T with hW
  have hWU : (W.map ι).Normal := stellmacherWSz_map_normal_of_center hU3
    (hR.szSections hSz hU3) hF ι (Subgroup.inclusion_injective hTU) ⟨P, by rw [hrange, hP]⟩
  have hCU : W.map T.subtype ≤ U := (Subgroup.map_subtype_le W).trans hTU
  have heq : (W.map T.subtype).subgroupOf U = W.map ι := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwx⟩
      exact ⟨w, hw, Subtype.ext hwx⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [Proof165.stellmacherSub, ← Subgroup.normal_subgroupOf_iff_le_normalizer hCU, heq]
  exact hWU

end CFSG.RankThree.PartTwo.Sec16.Proof166Res4
