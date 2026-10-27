module

public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoSwap
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoCore
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoFusion
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoSylow
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoModel
public import CFSG.RankThree.GF2n.Parrott.Proposition6Sylow

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.OddStandard.Solomon75
open CFSG.Sporadic.Co2Smith

private theorem swap_of_mem_centralizer_not_mem {G : Type} [Group G] [Finite G] {z : G}
    [hN : ((twoThreeCore (H z)).subgroupOf (H z)).Normal]
    {L1 L2 : Subgroup G}
    (hL1H : L1 ≤ H z) (hL2H : L2 ≤ H z)
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hinf2 : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (H z))
    (hquot2 : ∀ x : ↥(H z) ⧸ (twoThreeCore (H z)).subgroupOf (H z), x ^ 2 = 1)
    (hcard2 : Nat.card (↥(H z) ⧸ (twoThreeCore (H z)).subgroupOf (H z)) = 2)
    (hn1 : ¬ (L1.subgroupOf (H z)).Normal)
    {x : G} (hxH : x ∈ H z) (hxM : x ∉ L1 ⊔ L2) :
    (∀ y ∈ L1, x * y * x⁻¹ ∈ L2) ∧ (∀ y ∈ L2, x * y * x⁻¹ ∈ L1) := by
  classical
  have hMleH : L1 ⊔ L2 ≤ H z := by
    rw [hsup]
    exact Subgroup.map_subtype_le _
  have hblock := (p6_core_structure (z := z) hL1H hL2H hL1 hL2 hcomm hinf1 hinf2 hsup
    hquot2).2 ⟨x, hxH⟩
  rcases hblock with hpres | hswap
  · exfalso
    have hMidx' : ((twoThreeCore (H z)).subgroupOf (H z)).index = 2 := by
      rw [Subgroup.index_eq_card]
      exact hcard2
    have hMidx : ((L1 ⊔ L2).subgroupOf (H z)).index = 2 := by
      have hMsub : ((L1 ⊔ L2).subgroupOf (H z)) = (twoThreeCore (H z)).subgroupOf (H z) := by
        rw [hsup]
      exact hMsub.symm ▸ hMidx'
    have hcover : ∀ c ∈ H z, c ∈ L1 ⊔ L2 ∨ c * x⁻¹ ∈ L1 ⊔ L2 := by
      intro c hc
      by_cases hcM : c ∈ L1 ⊔ L2
      · exact Or.inl hcM
      · right
        have ha : (⟨c, hc⟩ : H z) ∉ (L1 ⊔ L2).subgroupOf (H z) := by
          intro h
          exact hcM (Subgroup.mem_subgroupOf.mp h)
        have hb : (⟨x, hxH⟩ : H z)⁻¹ ∉ (L1 ⊔ L2).subgroupOf (H z) := by
          intro h
          exact hxM (by simpa using (L1 ⊔ L2).inv_mem (Subgroup.mem_subgroupOf.mp h))
        have hmul : (⟨c, hc⟩ : H z) * (⟨x, hxH⟩ : H z)⁻¹ ∈
            (L1 ⊔ L2).subgroupOf (H z) :=
          (Subgroup.mul_mem_iff_of_index_two hMidx).mpr
            ⟨fun h => absurd h ha, fun h => absurd h hb⟩
        simpa using Subgroup.mem_subgroupOf.mp hmul
    have hceq : H z = (L1 ⊔ L2) ⊔ Subgroup.zpowers x := by
      refine le_antisymm ?_ (sup_le hMleH (Subgroup.zpowers_le.mpr hxH))
      intro c hc
      rcases hcover c hc with hcM | hcx
      · exact Subgroup.mem_sup_left hcM
      · have hc' : c = (c * x⁻¹) * x := by group
        rw [hc']
        exact Subgroup.mul_mem_sup hcx (Subgroup.mem_zpowers x)
    have hmaple : L1.map (MulAut.conj x).toMonoidHom ≤ L1 := by
      rintro a ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using
        Subgroup.mem_subgroupOf.mp (hpres.1 ⟨b, hL1H hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
    have hmapeq : L1.map (MulAut.conj x).toMonoidHom = L1 := by
      refine Subgroup.eq_of_le_of_card_ge hmaple ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hxN : x ∈ Subgroup.normalizer (L1 : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapeq
    have hL2N : L2 ≤ Subgroup.normalizer (L1 : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have hya : y * a = a * y := (hcomm a ha y hy).symm
        have hconj : y * a * y⁻¹ = a := by
          rw [hya]
          group
        rw [hconj]
        exact ha
      · intro ha
        have hb : y * a * y⁻¹ ∈ L1 := ha
        have h1 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
        have h2 : y⁻¹ * (y * a * y⁻¹) * y = y * a * y⁻¹ := by
          rw [← hcomm (y * a * y⁻¹) hb y⁻¹ (L2.inv_mem hy)]
          group
        rw [h1] at h2
        rw [h2]
        exact hb
    have hHN : H z ≤ Subgroup.normalizer (L1 : Set G) := by
      rw [hceq]
      exact sup_le (sup_le Subgroup.le_normalizer hL2N) (Subgroup.zpowers_le.mpr hxN)
    exact hn1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hL1H).mpr hHN)
  · refine ⟨?_, ?_⟩
    · intro y hy
      simpa using Subgroup.mem_subgroupOf.mp (hswap.1 ⟨y, hL1H hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
    · intro y hy
      simpa using Subgroup.mem_subgroupOf.mp (hswap.2 ⟨y, hL2H hy⟩ (Subgroup.mem_subgroupOf.mpr hy))

private theorem centralizer_quaternion_core_le_zpowers {G : Type} [Group G] [Finite G] {z : G}
    [hN : ((twoThreeCore (H z)).subgroupOf (H z)).Normal]
    {L1 L2 U : Subgroup G}
    (hL1H : L1 ≤ H z) (hL2H : L2 ≤ H z)
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hinf2 : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (H z))
    (hquot2 : ∀ x : ↥(H z) ⧸ (twoThreeCore (H z)).subgroupOf (H z), x ^ 2 = 1)
    (hcard2 : Nat.card (↥(H z) ⧸ (twoThreeCore (H z)).subgroupOf (H z)) = 2)
    (hn1 : ¬ (L1.subgroupOf (H z)).Normal)
    (hcentU : ∀ x ∈ L1 ⊔ L2, (∀ u ∈ U, x * u = u * x) → x ∈ Subgroup.zpowers z)
    (hexU : ∃ q ∈ L1, q ∈ U ∧ q ∉ Subgroup.zpowers z)
    (hz_inf : L1 ⊓ L2 = Subgroup.zpowers z) :
    ∀ x ∈ H z, (∀ u ∈ U, x * u = u * x) → x ∈ Subgroup.zpowers z := by
  classical
  intro x hxH hxU
  by_cases hxM : x ∈ L1 ⊔ L2
  · exact hcentU x hxM hxU
  · obtain ⟨q, hq1, hqU, hqZ⟩ := hexU
    have hswap := swap_of_mem_centralizer_not_mem (z := z) hL1H hL2H hL1 hL2 hcomm hinf1
      hinf2 hsup hquot2 hcard2 hn1 hxH hxM
    have hqL2 : q ∈ L2 := by
      have hqconj := hswap.1 q hq1
      have hqfix : x * q * x⁻¹ = q := by
        rw [hxU q hqU]
        group
      rwa [hqfix] at hqconj
    have hqinf : q ∈ L1 ⊓ L2 := ⟨hq1, hqL2⟩
    rw [hz_inf] at hqinf
    exact absurd hqinf hqZ

private theorem parrott_proposition6_indexTwo_of_not_top
    (hJ14 : ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSp 2 3 1 → ∀ x : X,
      orderOf x = 2 →
      (∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x) →
      ∀ (G : Type) [Group G] [Finite G], (∀ N : Subgroup G, N.index ≠ 2) →
        ∀ j : G, orderOf j = 2 →
          Nonempty (Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) →
            CFSG.Blueprint.LieModel G .PSp 2 3 1)
    (G : Type) [Group G] [Finite G] (z : G) (hz : orderOf z = 2)
    [hO23 : ((CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore (H z)).subgroupOf
      (H z)).Normal]
    (hconf : ∃ L1 L2 : Subgroup G,
        L1 ≤ Subgroup.centralizer ({z} : Set G) ∧ L2 ≤ Subgroup.centralizer ({z} : Set G) ∧
        Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        (∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x) ∧
        L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
        L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype ∧
        L1 ⊔ L2 = CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
          (Subgroup.centralizer ({z} : Set G)) ∧
        ¬ (L1.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        ¬ (L2.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        Nat.card (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
              (Subgroup.centralizer ({z} : Set G))).subgroupOf
              (Subgroup.centralizer ({z} : Set G))) = 2) :
    Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
      CFSG.Blueprint.LieModel G .PSp 2 3 1 := by
  classical
  obtain ⟨L1, L2, hL1H, hL2H, hL1, hL2, hcomm, hinf1, hinf2, hsup, hn1, hn2, hcard2⟩ := hconf
  by_cases hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤
  · exact Or.inl hne
  · right
    have hcore : Nat.card (twoThreeCore (H z)) = 288 :=
      card_core hL1 hL2 hcomm hinf1 hsup
    have hMleH : L1 ⊔ L2 ≤ H z := by
      rw [hsup]
      exact Subgroup.map_subtype_le _
    have hcard2' : Nat.card (↥(H z) ⧸
        (twoThreeCore (H z)).subgroupOf (H z)) = 2 := hcard2
    have hMsub_idx' : ((twoThreeCore (H z)).subgroupOf (H z)).index = 2 := by
      rw [Subgroup.index_eq_card]
      exact hcard2'
    have hMsub_idx : ((L1 ⊔ L2).subgroupOf (H z)).index = 2 := by
      have hMsub : ((L1 ⊔ L2).subgroupOf (H z)) = (twoThreeCore (H z)).subgroupOf (H z) := by
        rw [hsup]
        rfl
      exact hMsub.symm ▸ hMsub_idx'
    have hcardMsub : Nat.card ↥((L1 ⊔ L2).subgroupOf (H z)) = 288 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMleH).toEquiv, hsup]
      exact hcore
    have hcardC : Nat.card ↥(H z) = 576 := by
      have h := Subgroup.index_mul_card ((L1 ⊔ L2).subgroupOf (H z))
      rw [hMsub_idx, hcardMsub] at h
      omega
    have hquot2 : ∀ x : ↥(H z) ⧸ (twoThreeCore (H z)).subgroupOf (H z), x ^ 2 = 1 := by
      intro x
      have h := pow_card_eq_one' (x := x)
      rw [hcard2'] at h
      exact h
    have hz_inf : L1 ⊓ L2 = Subgroup.zpowers z :=
      inf_eq_zpowers_of_sup_eq_twoThreeCore hz hL1 hL2 hcomm hinf1 hsup
    obtain ⟨U, hU, hcardU, hinvU, hcommU, htransU, hpairU, hcentU, hexU⟩ :=
      exists_quaternion_core_of_sl23_pair hL1 hL2 hcomm hinf1 hz_inf
    have hUH : U ≤ H z := by
      intro x hx
      exact hMleH ((hU x).mp hx).1
    have hcls : ∀ a ∈ U, ∀ b ∈ U, orderOf a = 2 → orderOf b = 2 → a ≠ z → b ≠ z →
        ∃ k : G, k * a * k⁻¹ = b := by
      intro a ha b hb ha2 hb2 hane hbne
      obtain ⟨k, -, hk⟩ := htransU a ha b hb ha2 hb2 hane hbne
      exact ⟨k, hk⟩
    have hinv : ∀ x ∈ L1 ⊔ L2, orderOf x = 2 → x ∈ U := hinvU
    obtain ⟨g, hgC, hgM⟩ :=
      exists_conj_mem_centralizer_not_mem hz hUH hcommU hcls hpairU hinv hne
    set h : G := g * z * g⁻¹ with hhdef
    have hhH : h ∈ H z := hgC
    have hhM : h ∉ L1 ⊔ L2 := hgM
    have hhord : orderOf h = 2 := by
      rw [hhdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
    have hh2 : h * h = 1 := by
      have h := pow_orderOf_eq_one h
      rw [hhord] at h
      simpa [pow_two] using h
    have hswap := swap_of_mem_centralizer_not_mem (z := z) (hN := hO23) hL1H hL2H hL1 hL2
      hcomm hinf1 hinf2 hsup hquot2 hcard2 hn1 hhH hhM
    have hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2 := hswap.1
    have hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1 := hswap.2
    have hleC : L1 ⊔ L2 ⊔ Subgroup.zpowers h ≤ H z :=
      sup_le (sup_le hL1H hL2H) (Subgroup.zpowers_le.mpr hhH)
    have hcardSup : Nat.card ↥(L1 ⊔ L2 ⊔ Subgroup.zpowers h) = 576 :=
      card_sup_zpowers_of_sl23_swap hL1 hcomm hinf1 hs1 hs2 hh2 hhM
    have hCeq : H z = L1 ⊔ L2 ⊔ Subgroup.zpowers h := by
      have h := Subgroup.eq_of_le_of_card_ge hleC (by rw [hcardC, hcardSup])
      exact h.symm
    have hcen : ∀ x ∈ H z, (∀ u ∈ U, x * u = u * x) → x ∈ Subgroup.zpowers z :=
      centralizer_quaternion_core_le_zpowers (z := z) (hN := hO23) hL1H hL2H hL1 hL2 hcomm
        hinf1 hinf2 hsup hquot2 hcard2 hn1 hcentU hexU hz_inf
    have hMn : ∀ g ∈ H z, ∀ x ∈ L1 ⊔ L2, g * x * g⁻¹ ∈ L1 ⊔ L2 := by
      intro g hg x hx
      have hxH : x ∈ H z := hMleH hx
      have hx' : x ∈ twoThreeCore (H z) := hsup ▸ hx
      have hconj : (⟨g, hg⟩ : H z) * (⟨x, hxH⟩ : H z) *
          (⟨g, hg⟩ : H z)⁻¹ ∈ (twoThreeCore (H z)).subgroupOf (H z) :=
        (inferInstance : ((twoThreeCore (H z)).subgroupOf (H z)).Normal).conj_mem
          ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx') ⟨g, hg⟩
      have hmem : g * x * g⁻¹ ∈ twoThreeCore (H z) := Subgroup.mem_subgroupOf.mp hconj
      exact hsup.symm ▸ hmem
    have hzM : z ∈ L1 ⊔ L2 := by
      have hzinf : z ∈ L1 ⊓ L2 := by
        rw [hz_inf]
        exact Subgroup.mem_zpowers z
      exact Subgroup.mem_sup_left hzinf.1
    have hz4 : z ^ 4 = 1 := by
      have hz2 : z ^ 2 = 1 := by
        have h := pow_orderOf_eq_one z
        rwa [hz] at h
      calc z ^ 4 = (z ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hz2, one_pow]
    have hzU : z ∈ U := (hU z).mpr ⟨hzM, hz4⟩
    obtain ⟨T, hTC⟩ := exists_sylow_le_centralizer_of_quaternion_core (z := z) (h := h)
      (M := L1 ⊔ L2) (U := U) hz hcardC hMn hU hcardU hzU hUH hhH hhM hh2 hcen
    have hMall : ∀ N : Subgroup G, N.index = 2 → L1 ⊔ L2 ≤ N := by
      intro N hN
      exact sup_le (le_of_index_eq_two_of_nonempty_mulEquiv_sl23 hL1 hN)
        (le_of_index_eq_two_of_nonempty_mulEquiv_sl23 hL2 hN)
    have hconjzh : ∃ g : G, g * z * g⁻¹ = h := ⟨g, rfl⟩
    have hidx : ∀ N : Subgroup G, N.index ≠ 2 :=
      index_ne_two_of_sylow_le_sup_zpowers (M := L1 ⊔ L2) (z := z) (h := h) T
        (hCeq ▸ hTC) hMall hzM hconjzh
    obtain ⟨L1', L2', w, hL1', hcomm', hinf', hs1', hs2', hh', hn', hL1'C, hL2'C, hwC⟩ :=
      exists_sl23_swap_centralizer_x45P
    have hCXeq : Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) =
        L1' ⊔ L2' ⊔ Subgroup.zpowers w := by
      have hle : L1' ⊔ L2' ⊔ Subgroup.zpowers w ≤
          Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) :=
        sup_le (sup_le hL1'C hL2'C) (Subgroup.zpowers_le.mpr hwC)
      have hcard := card_sup_zpowers_of_sl23_swap hL1' hcomm' hinf' hs1' hs2' hh' hn'
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_centralizer_x45P])).symm
    obtain ⟨eC⟩ := nonempty_mulEquiv_of_sl23_swap hL1 hcomm hinf1 hs1 hs2 hh2 hhM
      hL1' hcomm' hinf' hs1' hs2' hh' hn'
    have eCentral : Nonempty (Subgroup.centralizer ({z} : Set G) ≃*
        Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) :=
      ⟨(MulEquiv.subgroupCongr hCeq).trans (eC.trans (MulEquiv.subgroupCongr hCXeq.symm))⟩
    exact hJ14 ↥QP45.originalSubgroup lieModel_QP45 x45P orderOf_x45P
      exists_sylow_x45P G hidx z hz eCentral

theorem parrott_proposition6_indexTwo
    (hJ14 : ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSp 2 3 1 → ∀ x : X,
      orderOf x = 2 →
      (∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x) →
      ∀ (G : Type) [Group G] [Finite G], (∀ N : Subgroup G, N.index ≠ 2) →
        ∀ j : G, orderOf j = 2 →
          Nonempty (Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) →
            CFSG.Blueprint.LieModel G .PSp 2 3 1) :
    ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
      [_hO23 : ((CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
        (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).Normal] →
      (∃ L1 L2 : Subgroup G,
        L1 ≤ Subgroup.centralizer ({z} : Set G) ∧ L2 ≤ Subgroup.centralizer ({z} : Set G) ∧
        Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        (∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x) ∧
        L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
        L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype ∧
        L1 ⊔ L2 = CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
          (Subgroup.centralizer ({z} : Set G)) ∧
        ¬ (L1.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        ¬ (L2.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        Nat.card (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
              (Subgroup.centralizer ({z} : Set G))).subgroupOf
              (Subgroup.centralizer ({z} : Set G))) = 2) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
        CFSG.Blueprint.LieModel G .PSp 2 3 1 := by
  intro G _ _ z hz hO23 hconf
  exact parrott_proposition6_indexTwo_of_not_top (hO23 := hO23) hJ14 G z hz hconf

end CFSG.RankThree.GF2n.Parrott
