module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.FiveSylow

public section

namespace CFSG.GroupTheory

open Subgroup

theorem normal_of_card_fifteen_of_normal_three_quotient
    {H : Type*} [Group H] [Finite H] (C N : Subgroup H) [N.Normal]
    (hNC : N ≤ C) (hC : Nat.card C = 15) (hN : Nat.card N = 3)
    (hq : Nat.card (H ⧸ N) ∣ 40) : C.Normal := by
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let D : Subgroup (H ⧸ N) := C.map π
  have hker : π.ker = N := by
    simp [π]
  have hrel : N.relIndex C = 5 := by
    have h := Subgroup.relIndex_mul_card N C
    rw [inf_eq_left.mpr hNC, hN, hC] at h
    omega
  have hcardD : Nat.card D = 5 := by
    have h := Subgroup.relIndex_ker (f := π) (K := C)
    rw [hker] at h
    exact h.symm.trans hrel
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hD5 : IsPGroup 5 D := IsPGroup.of_card (n := 1) (by simpa using hcardD)
  have hDindex : D.index ∣ 8 := by
    have h := D.card_mul_index
    rw [hcardD] at h
    have hdvd : 5 * D.index ∣ 5 * 8 := by
      rw [h]
      simpa using hq
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).1 hdvd
  have hnotdvd : ¬ 5 ∣ D.index := by
    intro h5
    have h58 : 5 ∣ 8 := h5.trans hDindex
    omega
  have h5q : 5 ∣ Nat.card (H ⧸ N) := by
    rw [← D.card_mul_index, hcardD]
    exact dvd_mul_right 5 D.index
  have hsub : Subsingleton (Sylow 5 (H ⧸ N)) :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.subsingleton_sylow_five hq h5q
  have hDnormal : D.Normal := by
    have := hsub
    have hP := Sylow.normal_of_subsingleton (hD5.toSylow hnotdvd)
    simpa [D] using hP
  have hle : π.ker ≤ C := by
    rw [hker]
    exact hNC
  have hpre : C = D.comap π := by
    change C = (C.map π).comap π
    exact (Subgroup.comap_map_eq_self hle).symm
  rw [hpre]
  exact hDnormal.comap π

theorem card_range_dvd_index_mul_card_map
    {G A : Type*} [Group G] [Group A] (f : G →* A) (J : Subgroup G) :
    Nat.card f.range ∣ J.index * Nat.card (J.map f) := by
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hidx : (J.map f.rangeRestrict).index ∣ J.index :=
    Subgroup.index_map_dvd (H := J) (f := f.rangeRestrict) hsurj
  have hcard : Nat.card f.range =
      (J.map f.rangeRestrict).index * Nat.card (J.map f.rangeRestrict) :=
    (Subgroup.index_mul_card _).symm
  have hcard_eq : Nat.card (J.map f.rangeRestrict) = Nat.card (J.map f) := by
    have hmap : (J.map f.rangeRestrict).map f.range.subtype = J.map f := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rw [← hmap, Subgroup.card_subtype]
  rw [hcard, hcard_eq]
  exact Nat.mul_dvd_mul hidx dvd_rfl

theorem range_le_normalizer_zpowers_of_order_fifteen
    {G A : Type*} [Group G] [Finite G] [Group A]
    (rho : G →* A) (J : Subgroup G) (delta : A)
    (hdelta_mem : delta ∈ rho.range) (hdelta : orderOf delta = 15)
    (hJindex : J.index ∣ 16)
    (hJimage : Nat.card (rho.comp J.subtype).range ∣ 60)
    (himage : Nat.card rho.range ∣ 360)
    (hthree : rho.range ≤ Subgroup.normalizer (Subgroup.zpowers (delta ^ 5) : Set A)) :
    rho.range ≤ Subgroup.normalizer (Subgroup.zpowers delta : Set A) := by
  let Hroot : Subgroup A := rho.range
  have hfin : Finite Hroot :=
    Finite.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have hrange_eq_map : J.map rho = (rho.comp J.subtype).range := by
    ext x
    simp [Subgroup.mem_map, MonoidHom.mem_range]
  have hdvd : Nat.card Hroot ∣ J.index * Nat.card (rho.comp J.subtype).range := by
    rw [← hrange_eq_map]
    exact card_range_dvd_index_mul_card_map rho J
  have h960 : Nat.card Hroot ∣ 960 := by
    have h := hdvd.trans (Nat.mul_dvd_mul hJindex hJimage)
    simpa using h
  have h120 : Nat.card Hroot ∣ 120 := by
    have h := Nat.dvd_gcd h960 himage
    rwa [show Nat.gcd 960 360 = 120 by norm_num] at h
  let deltaH : Hroot := ⟨delta, hdelta_mem⟩
  have hdeltaH : orderOf deltaH = 15 := by
    change orderOf (⟨delta, hdelta_mem⟩ : Hroot) = 15
    rw [Subgroup.orderOf_mk, hdelta]
  let C15 : Subgroup Hroot := Subgroup.zpowers deltaH
  have hC15card : Nat.card C15 = 15 := by
    change Nat.card (Subgroup.zpowers deltaH) = 15
    rw [Nat.card_zpowers, hdeltaH]
  let N3 : Subgroup Hroot := Subgroup.zpowers (deltaH ^ 5)
  have hN3card : Nat.card N3 = 3 := by
    change Nat.card (Subgroup.zpowers (deltaH ^ 5)) = 3
    rw [Nat.card_zpowers, orderOf_pow, hdeltaH]
    norm_num
  have hNC : N3 ≤ C15 := by
    change Subgroup.zpowers (deltaH ^ 5) ≤ Subgroup.zpowers deltaH
    rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers deltaH 5
  have hle : Subgroup.zpowers (delta ^ 5) ≤ Hroot := by
    rw [Subgroup.zpowers_le]
    exact Hroot.pow_mem hdelta_mem 5
  have hN3normal : N3.Normal := by
    have hsub : (Subgroup.zpowers (delta ^ 5)).subgroupOf Hroot = N3 := by
      ext x
      change (x : A) ∈ Subgroup.zpowers (delta ^ 5) ↔ x ∈ Subgroup.zpowers (deltaH ^ 5)
      rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        rw [← hk]
        simp [deltaH]
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have h := congrArg (Subtype.val : Hroot → A) hk
        simpa [deltaH] using h
    rw [← hsub]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hthree
  have hquot : Nat.card (Hroot ⧸ N3) ∣ 40 := by
    have hcardq : Nat.card Hroot = Nat.card (Hroot ⧸ N3) * Nat.card N3 :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N3
    have h := h120
    rw [hcardq, hN3card] at h
    rw [show (120 : ℕ) = 3 * 40 by norm_num] at h
    rw [mul_comm (Nat.card (Hroot ⧸ N3))] at h
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp h
  have hC15normal : C15.Normal :=
    @normal_of_card_fifteen_of_normal_three_quotient Hroot _ hfin C15 N3 hN3normal hNC
      hC15card hN3card hquot
  have hle_delta : Subgroup.zpowers delta ≤ Hroot := Subgroup.zpowers_le.mpr hdelta_mem
  have hsubeq : (Subgroup.zpowers delta).subgroupOf Hroot = C15 := by
    ext x
    change (x : A) ∈ Subgroup.zpowers delta ↔ x ∈ Subgroup.zpowers deltaH
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      change ((deltaH ^ k : Hroot) : A) = (x : A)
      rw [← hk]
      simp [deltaH]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h := congrArg (Subtype.val : Hroot → A) hk
      simpa [deltaH] using h
  change Hroot ≤ Subgroup.normalizer (Subgroup.zpowers delta : Set A)
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle_delta, hsubeq]
  exact hC15normal

end CFSG.GroupTheory
