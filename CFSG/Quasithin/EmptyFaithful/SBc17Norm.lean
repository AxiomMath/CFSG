module

public import CFSG.Quasithin.EmptyFaithful.SBc13J1Main
public import CFSG.Quasithin.EmptyFaithful.SBc13JRaMain
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.A3Structure37
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Quasi
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Rank
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isQuasisimple_conjSub {J : Subgroup G}
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (x : G) :
    CFSG.IsQuasisimple (↥(conjSub x J) ⧸ CFSG.pCore 2 ↥(conjSub x J)) := by
  let e : ↥J ≃* ↥(conjSub x J) := (MulAut.conj x).subgroupMap J
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥(conjSub x J)) e
      (CFSG.pCore_map_iso 2 e)) hJq

omit [Finite G] in
theorem isElemAbelian_zpowers_of_orderOf {p : ℕ} {a : G} (ha : orderOf a = p) :
    IsElemAbelian p (Subgroup.zpowers a) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 u.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 v.2
    apply Subtype.ext
    change (u : G) * v = v * u
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]

omit [Finite G] in
theorem mul_pow_three_mem {Y N : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) {j j' : G} (hj : j ∈ Y) (hj' : j' ∈ Y)
    (h1 : j ^ 3 ∈ N) (h2 : j' ^ 3 ∈ N) (h3 : ⁅j, j'⁆ ∈ N) : (j * j') ^ 3 ∈ N := by
  have hN : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  let π : ↥Y →* ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y)
  let a : ↥Y := ⟨j, hj⟩
  let b : ↥Y := ⟨j', hj'⟩
  have ha : a ^ 3 ∈ N.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    exact h1
  have hb : b ^ 3 ∈ N.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    exact h2
  have hab : ⁅a, b⁆ ∈ N.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    exact h3
  have ha' : π a ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hb' : π b ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hb
  have hc : π a * π b = π b * π a := by
    have h : ⁅π a, π b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hab
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hprod : π ((a * b) ^ 3) = 1 := by
    rw [map_pow, map_mul, Commute.mul_pow (show Commute (π a) (π b) from hc), ha', hb', one_mul]
  have hmem : (a * b) ^ 3 ∈ N.subgroupOf Y := (QuotientGroup.eq_one_iff _).mp hprod
  rw [Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem pCoreOf_le_pCoreOf_sup {J J₂ : Subgroup G}
    (h : J₂ ≤ Subgroup.normalizer (J : Set G)) : pCoreOf 2 J ≤ pCoreOf 2 (J ⊔ J₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
      (h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)

theorem commutator_le_pCoreOf_pair {X J J₂ : Subgroup G}
    (h36 : A36Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hJ : J ∈ cComp X) (hJ₂ : J₂ ∈ cComp X)
    (hne : J ≠ J₂) : ⁅J, J₂⁆ ≤ pCoreOf 2 J ∧ ⁅J₂, J⁆ ≤ pCoreOf 2 J₂ := by
  obtain ⟨h12, -⟩ := lemma_1_2_1_two_of_a3 (A37.a37_of_a36 h36) hJ hJ₂ hne
  exact ⟨h12.trans inf_le_left, (Subgroup.commutator_comm J₂ J).le.trans (h12.trans inf_le_right)⟩

theorem pow_three_mem_of_central {X J : Subgroup G} (hX : SQTKGroup ↥X)
    (h36 : A36Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hJ : J ∈ cComp X)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) {j : G} (hjJ : j ∈ J)
    (hcomm : ∀ z ∈ J, ⁅z, j⁆ ∈ pCoreOf 2 J) : j ^ 3 ∈ pCoreOf 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hQ : SQTKHyp (↥X ⧸ CFSG.pCore 2 ↥X) := SQTKHyp.of_sqtkGroup ↥X hX
  let π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥X) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥X) := IsPGroup.isNilpotent CFSG.pCore_isPGroup
    infer_instance
  set Jt : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := (J.subgroupOf X).map π with hJtdef
  have hJt : Jt ∈ cComp (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    (cComp_quotient_bijOn (CFSG.pCore 2 ↥X) hsolv).mapsTo (subgroupOf_mem_cComp hJ)
  let ι : ↥J →* ↥X := Subgroup.inclusion hJX
  have hmem : ∀ y : ↥J, π (ι y) ∈ Jt := fun y =>
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr y.2)
  let ρ : ↥J →* ↥Jt := (π.comp ι).codRestrict Jt hmem
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩
  have hker_iff : ∀ y : ↥J, ρ y = 1 ↔ ι y ∈ CFSG.pCore 2 ↥X := by
    intro y
    rw [← OneMemClass.coe_eq_one]
    exact QuotientGroup.eq_one_iff _
  have hker_le : ρ.ker ≤ CFSG.pCore 2 ↥J := by
    refine le_sSup ⟨inferInstance, ?_⟩
    intro g
    have hg : ι g.1 ∈ CFSG.pCore 2 ↥X := (hker_iff g.1).mp g.2
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨ι g.1, hg⟩
    refine ⟨n, ?_⟩
    have h1 : (ι g.1) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h2 : ι (g.1 ^ 2 ^ n) = ι 1 := by
      rw [map_pow, map_one]
      exact h1
    have h3 : g.1 ^ 2 ^ n = 1 := Subgroup.inclusion_injective hJX h2
    apply Subtype.ext
    simpa using h3
  have hker_ge : CFSG.pCore 2 ↥J ≤ ρ.ker := by
    have hmap : (CFSG.pCore 2 ↥J).map ρ ≤ CFSG.pCore 2 ↥Jt :=
      le_sSup ⟨Subgroup.Normal.map inferInstance ρ hρsurj, IsPGroup.map CFSG.pCore_isPGroup ρ⟩
    have hbot : CFSG.pCore 2 ↥Jt = ⊥ := hQ.pCore_two_of_subnormal (subnormal_of_mem_cComp hJt)
    rw [hbot, le_bot_iff] at hmap
    intro x hx
    have h1 : ρ x ∈ (CFSG.pCore 2 ↥J).map ρ := Subgroup.mem_map_of_mem ρ hx
    rw [hmap] at h1
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp h1)
  have hker : ρ.ker = CFSG.pCore 2 ↥J := le_antisymm hker_le hker_ge
  let e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥Jt :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)
  have hqJt : CFSG.IsQuasisimple ↥Jt := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hJq
  have hZ := SBc13.card_center_of_quasisimple hqJt (h36 Jt hJt).2.1
  let jj : ↥J := ⟨j, hjJ⟩
  have hcent : ρ jj ∈ Subgroup.center ↥Jt := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hρsurj y
    obtain ⟨w, hw, hwx⟩ := hcomm x x.2
    have hw' : w ∈ CFSG.pCore 2 ↥J := by
      exact hw
    have hwc : w = ⁅x, jj⁆ := Subtype.ext hwx
    have h1 : ρ ⁅x, jj⁆ = 1 := by
      rw [← hwc]
      exact MonoidHom.mem_ker.mp (hker_ge hw')
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hpow : (ρ jj) ^ 3 = 1 := by
    have h1 : (⟨ρ jj, hcent⟩ : ↥(Subgroup.center ↥Jt)) ^ Nat.card ↥(Subgroup.center ↥Jt) = 1 :=
      pow_card_eq_one'
    rcases hZ with h | h
    · rw [h, pow_one] at h1
      have h2 : ρ jj = 1 := congrArg Subtype.val h1
      rw [h2, one_pow]
    · rw [h] at h1
      have h2 := congrArg Subtype.val h1
      simpa using h2
  have h3 : jj ^ 3 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hpow
  rw [hker] at h3
  have h4 := Subgroup.mem_map_of_mem J.subtype h3
  rw [SBc13.map_pCore_eq_pCoreOf_J1] at h4
  exact h4

theorem not_mem_sup_of_five {X J J₂ : Subgroup G} (hX : SQTKGroup ↥X)
    (h36 : A36Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hJ : J ∈ cComp X) (hJ₂ : J₂ ∈ cComp X)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hJ₂q : CFSG.IsQuasisimple (↥J₂ ⧸ CFSG.pCore 2 ↥J₂)) (hne : J ≠ J₂) {k : G}
    (hk5 : orderOf k = 5) (hkJ : ∀ z ∈ J, ⁅z, k⁆ ∈ pCoreOf 2 J)
    (hkJ₂ : ∀ z ∈ J₂, ⁅z, k⁆ ∈ pCoreOf 2 J₂) (hkNJ : k ∈ Subgroup.normalizer (J : Set G)) :
    k ∉ J ⊔ J₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hkY
  obtain ⟨h1, h2⟩ := commutator_le_pCoreOf_pair h36 hJ hJ₂ hne
  have hJ₂N : J₂ ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_mem_cComp hJ hJ₂
  have hJN : J ≤ Subgroup.normalizer (J₂ : Set G) := le_normalizer_of_mem_cComp hJ₂ hJ
  have hk' : k ∈ ((J ⊔ J₂ : Subgroup G) : Set G) := hkY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J J₂ hJN] at hk'
  obtain ⟨j, hj, j₂, hj₂, hkjj⟩ := Set.mem_mul.mp hk'
  have hj3 : j ^ 3 ∈ pCoreOf 2 J := by
    refine pow_three_mem_of_central hX h36 hJ hJq hj fun z hz => ?_
    have hjeq : j = k * j₂⁻¹ := by rw [← hkjj]; group
    have e : ⁅z, k * j₂⁻¹⁆ = ⁅z, k⁆ * (k * ⁅z, j₂⁻¹⁆ * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hjeq, e]
    refine (pCoreOf 2 J).mul_mem (hkJ z hz) ?_
    have hn : k ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hkNJ
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp
      (h1 (Subgroup.commutator_mem_commutator hz (J₂.inv_mem hj₂)))
  have hj₂3 : j₂ ^ 3 ∈ pCoreOf 2 J₂ := by
    refine pow_three_mem_of_central hX h36 hJ₂ hJ₂q hj₂ fun z hz => ?_
    have hjeq : j₂ = j⁻¹ * k := by rw [← hkjj]; group
    have e : ⁅z, j⁻¹ * k⁆ = ⁅z, j⁻¹⁆ * (j⁻¹ * ⁅z, k⁆ * j⁻¹⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hjeq, e]
    refine (pCoreOf 2 J₂).mul_mem
      (h2 (Subgroup.commutator_mem_commutator hz (J.inv_mem hj))) ?_
    have hn : j⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 J₂ : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J₂ (hJN (J.inv_mem hj))
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hkJ₂ z hz)
  have hWY : pCoreOf 2 J ≤ pCoreOf 2 (J ⊔ J₂) := pCoreOf_le_pCoreOf_sup hJ₂N
  have hW₂Y : pCoreOf 2 J₂ ≤ pCoreOf 2 (J ⊔ J₂) := by
    rw [sup_comm]
    exact pCoreOf_le_pCoreOf_sup hJN
  have hcube : (j * j₂) ^ 3 ∈ pCoreOf 2 (J ⊔ J₂) :=
    mul_pow_three_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 (J ⊔ J₂))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ J₂)) (Subgroup.mem_sup_left hj)
      (Subgroup.mem_sup_right hj₂) (hWY hj3) (hW₂Y hj₂3)
      (hWY (h1 (Subgroup.commutator_mem_commutator hj hj₂)))
  rw [hkjj] at hcube
  have hk1 : k ^ 5 = 1 := by
    rw [← hk5]
    exact pow_orderOf_eq_one k
  have hkN : k ∈ pCoreOf 2 (J ⊔ J₂) := by
    have hk6 : k = (k ^ 3) ^ 2 := by
      rw [← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_succ, hk1, one_mul]
    rw [hk6]
    exact (pCoreOf 2 (J ⊔ J₂)).pow_mem hcube 2
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊔ J₂)) ⟨k, hkN⟩
  have hkm : orderOf k = 2 ^ m := by
    rw [← hm]
    exact Subgroup.orderOf_coe (⟨k, hkN⟩ : ↥(pCoreOf 2 (J ⊔ J₂)))
  rw [hk5] at hkm
  have h5 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) (dvd_of_eq hkm)
  omega

theorem false_of_two_components {X J J₂ K₂ : Subgroup G} (hX : SQTKGroup ↥X)
    (h36 : A36Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hJ : J ∈ cComp X) (hJ₂ : J₂ ∈ cComp X)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hJ₂q : CFSG.IsQuasisimple (↥J₂ ⧸ CFSG.pCore 2 ↥J₂)) (hne : J ≠ J₂) (hK₂X : K₂ ≤ X)
    (hXK₂ : X ≤ Subgroup.normalizer (K₂ : Set G)) (hJK₂ : ¬ J ≤ K₂) (hJ₂K₂ : ¬ J₂ ≤ K₂)
    {k : G} (hkK : k ∈ K₂) (hk5 : orderOf k = 5) {a a₂ : G} (haJ : a ∈ J)
    (ha5 : orderOf a = 5) (ha₂J : a₂ ∈ J₂) (ha₂5 : orderOf a₂ = 5) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hJ₂X : J₂ ≤ X := le_of_mem_cComp hJ₂
  obtain ⟨h1, -⟩ := commutator_le_pCoreOf_pair h36 hJ hJ₂ hne
  have hJ₂N : J₂ ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_mem_cComp hJ hJ₂
  have hJN : J ≤ Subgroup.normalizer (J₂ : Set G) := le_normalizer_of_mem_cComp hJ₂ hJ
  have hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G) :=
    SBc13.normalizer_le_of_normal_of_not_le hK₂X hXK₂ hJ hJK₂
  have hK₂N₂ : K₂ ≤ Subgroup.normalizer (J₂ : Set G) :=
    SBc13.normalizer_le_of_normal_of_not_le hK₂X hXK₂ hJ₂ hJ₂K₂
  have hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J :=
    SBc13.commutator_le_pCore_of_normal hK₂X hXK₂ hJ hJq hJK₂
  have hK₂c₂ : ⁅J₂, K₂⁆ ≤ pCoreOf 2 J₂ :=
    SBc13.commutator_le_pCore_of_normal hK₂X hXK₂ hJ₂ hJ₂q hJ₂K₂
  have hkJ : ∀ z ∈ J, ⁅z, k⁆ ∈ pCoreOf 2 J := fun z hz =>
    hK₂c (Subgroup.commutator_mem_commutator hz hkK)
  have hkJ₂ : ∀ z ∈ J₂, ⁅z, k⁆ ∈ pCoreOf 2 J₂ := fun z hz =>
    hK₂c₂ (Subgroup.commutator_mem_commutator hz hkK)
  have hYX : J ⊔ J₂ ≤ X := sup_le hJX hJ₂X
  have ha₂c : ∀ z ∈ J, ⁅z, a₂⁆ ∈ pCoreOf 2 J := fun z hz =>
    h1 (Subgroup.commutator_mem_commutator hz ha₂J)
  have hnotJ : a₂ ∉ J := SBc13.not_mem_of_commutes hX h36 hJ hJq ha₂5 ha₂c
  have hr1 : CFSG.Open.pRank 5 J + 1 ≤ CFSG.Open.pRank 5 (J ⊔ J₂) :=
    SBc13.pRank_succ_le_of_commutes (p := 5) (by norm_num) le_sup_left
      (Subgroup.mem_sup_right ha₂J) (hJ₂N ha₂J) ha₂5 hnotJ ha₂c
  have hone : 1 ≤ CFSG.Open.pRank 5 J :=
    CFSG.Quasithin.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr haJ)
      (isElemAbelian_zpowers_of_orderOf ha5) (k := 1)
      (by rw [Nat.card_zpowers, ha5, pow_one])
  have hkY : k ∉ J ⊔ J₂ :=
    not_mem_sup_of_five hX h36 hJ hJ₂ hJq hJ₂q hne hk5 hkJ hkJ₂ (hK₂N hkK)
  have hkNY : k ∈ Subgroup.normalizer ((J ⊔ J₂ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup J J₂ ⟨hK₂N hkK, hK₂N₂ hkK⟩
  have hWY : pCoreOf 2 J ≤ pCoreOf 2 (J ⊔ J₂) := pCoreOf_le_pCoreOf_sup hJ₂N
  have hW₂Y : pCoreOf 2 J₂ ≤ pCoreOf 2 (J ⊔ J₂) := by
    rw [sup_comm]
    exact pCoreOf_le_pCoreOf_sup hJN
  have hcommY : ∀ y ∈ J ⊔ J₂, ⁅y, k⁆ ∈ pCoreOf 2 (J ⊔ J₂) := by
    intro y hy
    have hle : ⁅Subgroup.zpowers k, J ⊔ J₂⁆ ≤ pCoreOf 2 (J ⊔ J₂) := by
      refine SBc13.commutator_sup_le_of_conj le_sup_left le_sup_right (fun g hg x hx => ?_) ?_ ?_
      · exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ J₂) hg) x).mp hx
      · rw [Subgroup.commutator_comm]
        exact ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hkK)).trans hK₂c).trans
          hWY
      · rw [Subgroup.commutator_comm]
        exact ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hkK)).trans hK₂c₂).trans
          hW₂Y
    have h := Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers k)
    rw [Subgroup.commutator_comm] at h
    exact hle h
  have hr2 : CFSG.Open.pRank 5 (J ⊔ J₂) + 1 ≤ CFSG.Open.pRank 5 X :=
    SBc13.pRank_succ_le_of_commutes (p := 5) (by norm_num) hYX (hK₂X hkK) hkNY hk5 hkY hcommY
  have hX2 : CFSG.Open.pRank 5 X ≤ 2 := by
    have h : CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) ≤ 2 := hX.1 5 (by norm_num) (by norm_num)
    rw [pRank_top_subtype] at h
    exact h
  omega

theorem normal_of_five_dvd (h36 : A36ForSQTK) {X J K₂ : Subgroup G} (hX : SQTKGroup ↥X)
    (hJ : J ∈ cComp X) (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hK₂X : K₂ ≤ X)
    (hXK₂ : X ≤ Subgroup.normalizer (K₂ : Set G)) (hJK₂ : ¬ J ≤ K₂) {k : G} (hkK : k ∈ K₂)
    (hk5 : orderOf k = 5) {a : G} (haJ : a ∈ J) (ha5 : orderOf a = 5) :
    X ≤ Subgroup.normalizer (J : Set G) := by
  intro x hx
  by_contra hxJ
  have hJ₂ : conjSub x J ∈ cComp X := SBc13.mem_cComp_conjSub_of_mem hJ hx
  have hne : J ≠ conjSub x J := fun h =>
    hxJ (SBc13.mem_normalizer_of_conjSub_eq_self h.symm)
  have hJ₂K₂ : ¬ conjSub x J ≤ K₂ := by
    intro h
    apply hJK₂
    have h1 := conjSub_mono x⁻¹ h
    rw [conjSub_conjSub_inv] at h1
    rwa [SBc13.conjSub_eq_self_of_mem_normalizer (hXK₂ (X.inv_mem hx))] at h1
  have ha₂5 : orderOf (x * a * x⁻¹) = 5 := by
    have h : SemiconjBy x a (x * a * x⁻¹) := by
      unfold SemiconjBy
      group
    rw [← SemiconjBy.orderOf_eq x h]
    exact ha5
  exact false_of_two_components hX (h36 _ (SQTKHyp.of_sqtkGroup ↥X hX)) hJ hJ₂ hJq
    (isQuasisimple_conjSub hJq x) hne hK₂X hXK₂ hJK₂ hJ₂K₂ hkK hk5 haJ ha5
    (mul_mem_conjSub haJ) ha₂5

end SBc17

end CFSG.Quasithin
