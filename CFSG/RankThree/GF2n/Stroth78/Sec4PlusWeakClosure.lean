module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusNotCentral
import CFSG.RankThree.GF2n.Stroth78.Sec2Lbar

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem mem_Q_of_mem_H_of_commute (S : Setting z E F) {x : G} (hx : x ∈ H z)
    (hc : ∀ y ∈ Q z, x * y = y * x) : x ∈ Q z := by
  refine (S.hyp.centralizer_quotient x).mp ⟨hx, fun y hy => ?_⟩
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [hc y hy]
    group
  rw [h1]
  exact (centerIn (Qa z)).one_mem

theorem pPrimeCore_two_H_eq_bot (S : Setting z E F) : CFSG.pPrimeCore 2 ↥(H z) = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  let K₁ : Subgroup G := K.map (H z).subtype
  have hK₁H : K₁ ≤ H z := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hK₁n : ∀ y ∈ H z, ∀ x ∈ K₁, y * x * y⁻¹ ∈ K₁ := by
    rintro y hy _ ⟨x, hx, rfl⟩
    exact ⟨⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹, hKn.conj_mem x hx ⟨y, hy⟩, rfl⟩
  have hQ2 : IsPGroup 2 (Q z) := Q_isPGroup S
  have hQn : ∀ y ∈ H z, ∀ x ∈ Q z, y * x * y⁻¹ ∈ Q z := by
    intro y hy x hx
    have := (instNormalQH z).conj_mem ⟨x, Q_le_H S hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hinf : K₁ ⊓ Q z = ⊥ := by
    have hP2 : IsPGroup 2 ↥(K₁ ⊓ Q z) := hQ2.to_le inf_le_right
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP2
    have hdvd : Nat.card ↥(K₁ ⊓ Q z) ∣ Nat.card K :=
      (Subgroup.card_dvd_of_le (inf_le_left : K₁ ⊓ Q z ≤ K₁)).trans
        (by rw [Subgroup.card_map_of_injective (H z).subtype_injective])
    have hn0 : n = 0 := by
      by_contra hne
      have h2 : 2 ∣ Nat.card K := by
        refine dvd_trans ?_ hdvd
        rw [hn]
        exact dvd_pow_self 2 hne
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mp hKc) h2
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  have hcomm : ∀ x ∈ K₁, ∀ y ∈ Q z, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ K₁ ⊓ Q z := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := K₁.mul_mem hx (hK₁n y (Q_le_H S hy) x⁻¹ (K₁.inv_mem hx))
        convert this using 1
        group
      · exact (Q z).mul_mem (hQn x (hK₁H hx) y hy) ((Q z).inv_mem hy)
    rw [hinf, Subgroup.mem_bot] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
      _ = y * x := by rw [h1]; group
  have hle : K₁ ≤ Q z := fun x hx => mem_Q_of_mem_H_of_commute S (hK₁H hx) (hcomm x hx)
  have : K₁ = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl hle
  rw [eq_bot_iff]
  intro x hx
  have hx1 : ((x : ↥(H z)) : G) ∈ K₁ := ⟨x, hx, rfl⟩
  rw [this, Subgroup.mem_bot] at hx1
  exact Subgroup.mem_bot.mpr (Subtype.ext hx1)


private theorem map_centralizer_conj_singleton (g z : G) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  change g⁻¹ * x * g * z = z * (g⁻¹ * x * g) ↔ x * (g * z * g⁻¹) = (g * z * g⁻¹) * x
  constructor
  · intro hx
    calc x * (g * z * g⁻¹) = g * (g⁻¹ * x * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
      _ = g * z * g⁻¹ * x := by group
  · intro hx
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group

theorem eq_of_mem_ZQ_of_isConj_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZ : Nat.card ↥(ZQ z) = 4) {t : G} (htZ : t ∈ ZQ z)
    (htc : IsConj z t) : t = z := by
  by_contra hne
  obtain ⟨g, hg⟩ := isConj_iff.mp htc
  have hz2 : orderOf z = 2 := S.hyp.orderOf_z
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz2
    omega
  have ht2 : orderOf t = 2 := by
    rw [← hg]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz2
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht2
    omega
  let R : Subgroup G := Subgroup.zpowers t
  have hRle : R ≤ centerIn (Qa z) := (Subgroup.zpowers_le).mpr htZ
  have hRcard : Nat.card (centerIn (Qa z)) = 2 * Nat.card R := by
    show Nat.card (ZQ z) = 2 * Nat.card (Subgroup.zpowers t)
    rw [hZ, Nat.card_zpowers, ht2]
  have hcore : Subgroup.centralizer (R : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (R : Set G)) ⊔
        inSubgroup (pPrimeCore 2) (Subgroup.centralizer (R : Set G)) := by
    by_contra hnot
    exact h.assumption212 ⟨R, hRle, hRcard, hnot⟩
  have hCR : Subgroup.centralizer (R : Set G) = Subgroup.centralizer ({t} : Set G) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hx y (Subgroup.mem_zpowers y)
    · intro hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute t x := hx t (Set.mem_singleton t)
      exact (hc.zpow_left k).eq
  have hmap := map_centralizer_conj_singleton g z
  rw [hg] at hmap
  let f : ↥(H z) ≃* ↥(Subgroup.centralizer ({t} : Set G)) :=
    (MulEquiv.subgroupMap (MulAut.conj g) (H z)).trans (MulEquiv.subgroupCongr hmap)
  have hOcore : CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({t} : Set G)) = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso 2 f, pPrimeCore_two_H_eq_bot S]
    exact Subgroup.map_bot _
  have hO : inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
    simp only [inSubgroup, hOcore]
    exact Subgroup.map_bot _
  have hle : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    have h1 := hcore
    rw [hCR, hO, sup_bot_eq] at h1
    exact h1.trans inf_le_left
  have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = Nat.card ↥(H z) :=
    (Nat.card_congr f.toEquiv).symm
  have heq : Subgroup.centralizer ({t} : Set G) = H z :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have htH : t ∈ H z := Q_le_H S (htZ.1 : t ∈ Qa z)
  have htcent : t ∈ centerIn (H z) := by
    refine Subgroup.mem_inf.mpr ⟨htH, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer ({t} : Set G) := heq ▸ hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hy'
  have hnc := not_zq_le_centerIn_H S h
  let M : Subgroup G := ZQ z ⊓ centerIn (H z)
  have hMle : M ≤ ZQ z := inf_le_left
  have hMne : M ≠ ZQ z := fun hMeq => hnc (hMeq ▸ inf_le_right)
  have hzcent : z ∈ centerIn (H z) := by
    refine Subgroup.mem_inf.mpr ⟨z_mem_H z, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hzM : z ∈ M := Subgroup.mem_inf.mpr ⟨z_mem_ZQ S, hzcent⟩
  have hzle : Subgroup.zpowers z ≤ M := (Subgroup.zpowers_le).mpr hzM
  have hMcard : Nat.card M ∣ 4 := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hMle
  have hMlt : Nat.card M ≠ 4 := fun h4 => hMne (Subgroup.eq_of_le_of_card_ge hMle (by omega))
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have h2M : 2 ∣ Nat.card M := by
    rw [← hzcard]
    exact Subgroup.card_dvd_of_le hzle
  have hM2 : Nat.card M = 2 := by
    have hle4 : Nat.card M ≤ 4 := Nat.le_of_dvd (by norm_num) hMcard
    obtain ⟨k, hk⟩ := h2M
    have hpos : 0 < Nat.card M := Nat.card_pos
    interval_cases hM : Nat.card M <;> omega
  have hMz : M = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hzle (by rw [hM2, hzcard])).symm
  have htM : t ∈ M := Subgroup.mem_inf.mpr ⟨htZ, htcent⟩
  rw [hMz] at htM
  rcases eq_one_or_z_of_mem_zpowers S htM with h1 | h1
  · exact ht1 h1
  · exact hne h1


theorem odd_index_map_subtype_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZ : Nat.card ↥(ZQ z) = 4) (P : Sylow 2 ↥(H z)) :
    Odd ((P : Subgroup ↥(H z)).map (H z).subtype).index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup G := (P : Subgroup ↥(H z)).map (H z).subtype with hP'
  have hP'H : P' ≤ H z := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map (H z).subtype
  have hQP : Q z ≤ P' := by
    haveI : ((Q z).subgroupOf (H z)).Normal := instNormalQH z
    have hN2 : IsPGroup 2 ((Q z).subgroupOf (H z)) := (Q_isPGroup S).comap_subtype
    have hle := hN2.le_sylow_of_normal P
    intro x hx
    exact ⟨⟨x, Q_le_H S hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hN : Subgroup.normalizer (P' : Set G) ≤ H z := by
    intro u hu
    have hzP : z ∈ P' := hQP (z_mem_Q S)
    have hcz : ∀ p ∈ P', p * z = z * p := fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mp (hP'H hp)
    have hw : u * z * u⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.mp hu z).mp hzP
    have hwc : ∀ p ∈ P', p * (u * z * u⁻¹) = (u * z * u⁻¹) * p := by
      intro p hp
      have hp' : u⁻¹ * p * u ∈ P' := by
        have hu' := (Subgroup.normalizer (P' : Set G)).inv_mem hu
        have := (Subgroup.mem_normalizer_iff.mp hu' p).mp hp
        simpa using this
      have h1 := hcz _ hp'
      calc p * (u * z * u⁻¹) = u * ((u⁻¹ * p * u) * z) * u⁻¹ := by group
        _ = u * (z * (u⁻¹ * p * u)) * u⁻¹ := by rw [h1]
        _ = (u * z * u⁻¹) * p := by group
    have hwH : u * z * u⁻¹ ∈ H z := hP'H hw
    have hwQ : u * z * u⁻¹ ∈ Q z :=
      mem_Q_of_mem_H_of_commute S hwH (fun y hy => (hwc y (hQP hy)).symm)
    have hwZ : u * z * u⁻¹ ∈ ZQ z :=
      Subgroup.mem_inf.mpr ⟨hwQ, Subgroup.mem_centralizer_iff.mpr (fun y hy => hwc y (hQP hy))⟩
    have hconj : IsConj z (u * z * u⁻¹) := isConj_iff.mpr ⟨u, rfl⟩
    have hwz := eq_of_mem_ZQ_of_isConj_of_card_ZQ_eq_four S h hZ hwZ hconj
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * z = u * z * u⁻¹ * u := by group
      _ = z * u := by rw [hwz]
  obtain ⟨T, hPT⟩ := hP'2.exists_le_sylow
  have hTP' : (T : Subgroup G) ≤ P' := by
    by_contra hnle
    have hlt : P'.subgroupOf (T : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.mpr (fun htop => hnle ?_)
      intro x hx
      have : (⟨x, hx⟩ : ↥(T : Subgroup G)) ∈ P'.subgroupOf (T : Subgroup G) := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    haveI : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
    obtain ⟨x, hxN, hxP⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hxNG : (x : G) ∈ Subgroup.normalizer (P' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hgT : g ∈ (T : Subgroup G) := hPT hg
        have := (Subgroup.mem_normalizer_iff.mp hxN ⟨g, hgT⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
        exact Subgroup.mem_subgroupOf.mp this
      · intro hg
        have hgT : (x : G) * g * (x : G)⁻¹ ∈ (T : Subgroup G) := hPT hg
        have hgT' : g ∈ (T : Subgroup G) := by
          have := T.mul_mem (T.mul_mem (T.inv_mem x.2) hgT) x.2
          simpa [mul_assoc] using this
        have h2 : (x * ⟨g, hgT'⟩ * x⁻¹ : ↥(T : Subgroup G)) ∈ P'.subgroupOf (T : Subgroup G) :=
          Subgroup.mem_subgroupOf.mpr hg
        have := (Subgroup.mem_normalizer_iff.mp hxN ⟨g, hgT'⟩).mpr h2
        exact Subgroup.mem_subgroupOf.mp this
    have hxH : (x : G) ∈ H z := hN hxNG
    let L : Subgroup G := P' ⊔ Subgroup.zpowers (x : G)
    have hLT : L ≤ (T : Subgroup G) :=
      sup_le hPT ((Subgroup.zpowers_le).mpr x.2)
    have hL2 : IsPGroup 2 (L.comap (H z).subtype) := (T.isPGroup'.to_le hLT).comap_subtype
    have hPL : (P : Subgroup ↥(H z)) ≤ L.comap (H z).subtype := by
      intro y hy
      exact (le_sup_left : P' ≤ L) ⟨y, hy, rfl⟩
    have heq := P.is_maximal' hL2 hPL
    have hxL : (⟨(x : G), hxH⟩ : ↥(H z)) ∈ L.comap (H z).subtype :=
      (le_sup_right : Subgroup.zpowers (x : G) ≤ L) (Subgroup.mem_zpowers _)
    rw [heq] at hxL
    exact hxP (Subgroup.mem_subgroupOf.mpr ⟨_, hxL, rfl⟩)
  have hTeq : (T : Subgroup G) = P' := le_antisymm hTP' hPT
  rw [← hTeq]
  have hndvd := T.not_dvd_index
  exact Nat.odd_iff.mpr (by omega)

end CFSG.RankThree.GF2n.Stroth78
