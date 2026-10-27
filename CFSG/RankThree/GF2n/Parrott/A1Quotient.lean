module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma37Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

@[instance] theorem twoThreeCore_subgroupOf_normal (Y : Subgroup G) :
    ((twoThreeCore Y).subgroupOf Y).Normal := by
  rw [twoThreeCore, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  exact Subgroup.Normal.comap CFSG.pCore_normal _

private theorem pCore_two_eq_subgroupOf {C O : Subgroup G} (hON : (O.subgroupOf C).Normal)
    (hO : IsPGroup 2 O)
    (hOmax : ∀ W : Subgroup G, W ≤ C → (W.subgroupOf C).Normal → IsPGroup 2 W → W ≤ O) :
    CFSG.pCore 2 ↥C = O.subgroupOf C := by
  refine le_antisymm (fun x hx => ?_) (le_sSup ⟨hON, hO.comap_subtype⟩)
  have hN : (((CFSG.pCore 2 ↥C).map C.subtype).subgroupOf C).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact CFSG.pCore_normal
  exact Subgroup.mem_subgroupOf.mpr
    (hOmax _ (Subgroup.map_subtype_le _) hN (CFSG.pCore_isPGroup.map C.subtype) ⟨x, hx, rfl⟩)

theorem twoThreeCore_eq_of_card [Finite G] {C R O : Subgroup G} (hRC : R ≤ C) (hOR : O ≤ R)
    (hON : (O.subgroupOf C).Normal) (hRN : (R.subgroupOf C).Normal) (hO : IsPGroup 2 O)
    (hOmax : ∀ W : Subgroup G, W ≤ C → (W.subgroupOf C).Normal → IsPGroup 2 W → W ≤ O)
    {k m : ℕ} (hRO : Nat.card R = Nat.card O * 3 ^ k) (hCR : Nat.card C = Nat.card R * 2 ^ m) :
    twoThreeCore C = R := by
  have hP := pCore_two_eq_subgroupOf hON hO hOmax
  have hPR : CFSG.pCore 2 ↥C ≤ R.subgroupOf C := by
    rw [hP]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hOR (Subgroup.mem_subgroupOf.mp hx))
  have hcardR : Nat.card (R.subgroupOf C) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have hcardP : Nat.card (CFSG.pCore 2 ↥C) = Nat.card O := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOR.trans hRC)).toEquiv
  have hindex : (R.subgroupOf C).index = 2 ^ m := by
    have h := (R.subgroupOf C).index_mul_card
    rw [hcardR, hCR, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have himage :
      Nat.card ((R.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))) = 3 ^ k := by
    have h := Subgroup.relIndex_mul_card (CFSG.pCore 2 ↥C) (R.subgroupOf C)
    rw [inf_eq_left.mpr hPR, hcardP, hcardR, hRO, mul_comm (Nat.card O)] at h
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hR3 : (R.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) ≤
      CFSG.pCore 3 (↥C ⧸ CFSG.pCore 2 ↥C) :=
    le_sSup ⟨hRN.map _ (QuotientGroup.mk'_surjective _), IsPGroup.of_card himage⟩
  have key : ∀ c : ↥C, QuotientGroup.mk' (CFSG.pCore 2 ↥C) c ∈
      CFSG.pCore 3 (↥C ⧸ CFSG.pCore 2 ↥C) ↔ (c : G) ∈ R := by
    intro c
    refine ⟨fun hc => ?_, fun hc => hR3 ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩⟩
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨_, hc⟩ : CFSG.pCore 3 (↥C ⧸ CFSG.pCore 2 ↥C))
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥C) c ^ 3 ^ n = 1 := congrArg Subtype.val hn
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := hRN
    have h2 : c ^ 2 ^ m ∈ R.subgroupOf C := hindex ▸ Subgroup.pow_index_mem _ c
    have hc1 : (c : ↥C ⧸ R.subgroupOf C) = 1 :=
      (pow_eq_one_iff_of_coprime (Nat.Coprime.pow n m (by norm_num : Nat.Coprime 3 2))).mp
        ⟨by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hPR h1,
          by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact h2⟩
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff c).mp hc1)
  ext g
  rw [twoThreeCore, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (key c).mp hc
  · intro hg
    exact ⟨⟨g, hRC hg⟩, (key _).mpr hg, rfl⟩

theorem comap_pPrimeCore_quotient_of_coprime {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (N : Subgroup Y) [N.Normal] (hN : Nat.Coprime p (Nat.card N)) :
    (CFSG.pPrimeCore p (Y ⧸ N)).comap (QuotientGroup.mk' N) = CFSG.pPrimeCore p Y := by
  have hNle : N ≤ (CFSG.pPrimeCore p (Y ⧸ N)).comap (QuotientGroup.mk' N) := by
    have h := MonoidHom.ker_le_comap (QuotientGroup.mk' N) (CFSG.pPrimeCore p (Y ⧸ N))
    rwa [QuotientGroup.ker_mk'] at h
  apply le_antisymm
  · have h1 := Subgroup.relIndex_mul_card N
      ((CFSG.pPrimeCore p (Y ⧸ N)).comap (QuotientGroup.mk' N))
    have h2 := Subgroup.relIndex_ker ((CFSG.pPrimeCore p (Y ⧸ N)).comap (QuotientGroup.mk' N))
      (QuotientGroup.mk' N)
    rw [QuotientGroup.ker_mk',
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h2
    rw [inf_eq_left.mpr hNle, h2] at h1
    refine le_sSup ⟨Subgroup.Normal.comap CFSG.pPrimeCore_normal _, ?_⟩
    rw [← h1]
    exact Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card hN
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨CFSG.pPrimeCore_normal.map _ (QuotientGroup.mk'_surjective N),
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card⟩

private theorem pow_three_eq_one_of_mem_zpowers {s n : G} (hs : orderOf s = 3)
    (hn : n ∈ Subgroup.zpowers s) : n ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (hs ▸ orderOf_dvd_of_mem_zpowers hn)

private theorem card_zpowers_subgroupOf {Y : Subgroup G} {s : G} (hsY : s ∈ Y) :
    Nat.card ((Subgroup.zpowers s).subgroupOf Y) = orderOf s := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hsY)).toEquiv,
    Nat.card_zpowers]

section Central

variable {Y : Subgroup G} {s z : G} [((Subgroup.zpowers s).subgroupOf Y).Normal]

private theorem orderOf_mk_eq_two_aux (hs : orderOf s = 3) (hz : z ∈ Y) (hz2 : orderOf z = 2) :
    orderOf (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y) ⟨z, hz⟩) = 2 := by
  have hz1 : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← map_pow, show (⟨z, hz⟩ : ↥Y) ^ 2 = 1 from Subtype.ext hz1, map_one]
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have hz' : z = 1 := (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 2 3)).mp
      ⟨hz1, pow_three_eq_one_of_mem_zpowers hs h1⟩
    rw [hz', orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

private theorem centralizer_mk_eq_map_aux (hs : orderOf s = 3) (hz : z ∈ Y)
    (hzs : z * s = s * z) (hz2 : orderOf z = 2) :
    Subgroup.centralizer {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y) ⟨z, hz⟩} =
      ((Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y).map
        (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y)) := by
  have hz1 : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      QuotientGroup.mk'_eq_mk'] at hx
    obtain ⟨n, hn, hyn⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hn
    have hyn' : (y : G) * z * n = z * y := congrArg Subtype.val hyn
    have hzn : Commute z (n : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← hk]
      exact Commute.zpow_right hzs k
    have hn2 : (n : G) ^ 2 = 1 := by
      have h1 : ((y : G)⁻¹ * z * y) ^ 2 = 1 := by
        rw [sq, show (y : G)⁻¹ * z * y * ((y : G)⁻¹ * z * y) = (y : G)⁻¹ * (z * z) * y by group,
          ← sq, hz1, mul_one, inv_mul_cancel]
      rw [show (y : G)⁻¹ * z * y = z * n by rw [mul_assoc, ← hyn']; group, hzn.mul_pow, hz1,
        one_mul] at h1
      exact h1
    have hn1 : (n : G) = 1 := (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 2 3)).mp
      ⟨hn2, pow_three_eq_one_of_mem_zpowers hs hn⟩
    rw [hn1, mul_one] at hyn'
    exact ⟨y, Subgroup.mem_subgroupOf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyn', y.2⟩, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.1))

private theorem card_centralizer_mk_mul_three_aux (hs : orderOf s = 3) (hsY : s ∈ Y) (hz : z ∈ Y)
    (hzs : z * s = s * z) (hz2 : orderOf z = 2) :
    Nat.card (Subgroup.centralizer
        {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y) ⟨z, hz⟩}) * 3 =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Y) := by
  have hNA : (Subgroup.zpowers s).subgroupOf Y ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, n.2⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← hk, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.zpow_left hzs.symm k).eq
  have h1 := Subgroup.relIndex_mul_card ((Subgroup.zpowers s).subgroupOf Y)
    ((Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y)
  have h2 := Subgroup.relIndex_ker ((Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y)
    (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y))
  rw [QuotientGroup.ker_mk'] at h2
  rw [inf_eq_left.mpr hNA, h2, card_zpowers_subgroupOf hsY, hs,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
  rw [centralizer_mk_eq_map_aux hs hz hzs hz2, h1]

private theorem eq_centralizer_sup_pPrimeCore_aux [Finite G] (hs : orderOf s = 3) (hsY : s ∈ Y)
    (hz : z ∈ Y) (hzs : z * s = s * z) (hz2 : orderOf z = 2)
    (htop : Subgroup.centralizer
        {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y) ⟨z, hz⟩} ⊔
      CFSG.pPrimeCore 2 (↥Y ⧸ (Subgroup.zpowers s).subgroupOf Y) = ⊤) :
    Y = (Subgroup.centralizer ({z} : Set G) ⊓ Y) ⊔ (CFSG.pPrimeCore 2 ↥Y).map Y.subtype := by
  have hcop : Nat.Coprime 2 (Nat.card ((Subgroup.zpowers s).subgroupOf Y)) := by
    rw [card_zpowers_subgroupOf hsY, hs]
    norm_num
  have hO : (CFSG.pPrimeCore 2 ↥Y).map (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y)) =
      CFSG.pPrimeCore 2 (↥Y ⧸ (Subgroup.zpowers s).subgroupOf Y) := by
    rw [← comap_pPrimeCore_quotient_of_coprime _ hcop,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hNB : (Subgroup.zpowers s).subgroupOf Y ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y ⊔ CFSG.pPrimeCore 2 ↥Y :=
    le_sup_of_le_right (le_sSup ⟨inferInstance, hcop⟩)
  rw [centralizer_mk_eq_map_aux hs hz hzs hz2, ← hO, ← Subgroup.map_sup] at htop
  have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf Y))
    ((Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y ⊔ CFSG.pPrimeCore 2 ↥Y)
  rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hNB] at h1
  calc Y = (⊤ : Subgroup ↥Y).map Y.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = _ := by rw [h1, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

end Central

@[instance] theorem zpowers_subgroupOf_centralizer_self_normal (s : G) :
    ((Subgroup.zpowers s).subgroupOf (Subgroup.centralizer ({s} : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute (g : G) (n : G) := by
    rw [← hk]
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp g.2) k
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc.eq, mul_inv_cancel_right]

private theorem mem_centralizer_self (s : G) : s ∈ Subgroup.centralizer ({s} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem orderOf_mk_eq_two {s z : G} (hs : orderOf s = 3)
    (hz : z ∈ Subgroup.centralizer ({s} : Set G)) (hz2 : orderOf z = 2) :
    orderOf (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf
      (Subgroup.centralizer ({s} : Set G))) ⟨z, hz⟩) = 2 :=
  orderOf_mk_eq_two_aux hs hz hz2

theorem centralizer_mk_eq_map {s z : G} (hs : orderOf s = 3)
    (hz : z ∈ Subgroup.centralizer ({s} : Set G)) (hz2 : orderOf z = 2) :
    Subgroup.centralizer {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf
        (Subgroup.centralizer ({s} : Set G))) ⟨z, hz⟩} =
      ((Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf
        (Subgroup.centralizer ({s} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf
          (Subgroup.centralizer ({s} : Set G)))) :=
  centralizer_mk_eq_map_aux hs hz (Subgroup.mem_centralizer_singleton_iff.mp hz) hz2

theorem eq_centralizer_sup_pPrimeCore [Finite G] {s z : G} (hs : orderOf s = 3)
    (hz : z ∈ Subgroup.centralizer ({s} : Set G)) (hz2 : orderOf z = 2)
    (htop : Subgroup.centralizer {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf
        (Subgroup.centralizer ({s} : Set G))) ⟨z, hz⟩} ⊔
      CFSG.pPrimeCore 2 (↥(Subgroup.centralizer ({s} : Set G)) ⧸
        (Subgroup.zpowers s).subgroupOf (Subgroup.centralizer ({s} : Set G))) = ⊤) :
    Subgroup.centralizer ({s} : Set G) =
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) ⊔
        (CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({s} : Set G))).map
          (Subgroup.centralizer ({s} : Set G)).subtype :=
  eq_centralizer_sup_pPrimeCore_aux hs (mem_centralizer_self s) hz
    (Subgroup.mem_centralizer_singleton_iff.mp hz) hz2 htop

theorem card_centralizer_mk_mul_three {s z : G} (hs : orderOf s = 3)
    (hz : z ∈ Subgroup.centralizer ({s} : Set G)) (hz2 : orderOf z = 2) :
    Nat.card (Subgroup.centralizer {QuotientGroup.mk' ((Subgroup.zpowers s).subgroupOf
        (Subgroup.centralizer ({s} : Set G))) ⟨z, hz⟩}) * 3 =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) :=
  card_centralizer_mk_mul_three_aux hs (mem_centralizer_self s) hz
    (Subgroup.mem_centralizer_singleton_iff.mp hz) hz2

end CFSG.RankThree.GF2n.Parrott.Remarks
