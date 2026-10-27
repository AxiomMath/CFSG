module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped Pointwise

theorem s16c1_G47_unique_three {Hs : Type} [Group Hs] [Finite Hs] {P Dd Dd' : Subgroup Hs}
    (hP : IsPGroup 3 P) (hD : Dd ≤ P) (hD' : Dd' ≤ P) (hD3 : Nat.card Dd = 3)
    (hD3' : Nat.card Dd' = 3) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Hs) ≤ 1) : Dd = Dd' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.LocalAnalysis.RankThreeUC.eq_of_card_eq_prime_of_pRank_le_one hP ?_ hD hD' hD3 hD3'
  exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top).trans hr

theorem s16c1_G47_no_three {Hs : Type} [Group Hs] [Finite Hs] {Xs Ys N : Subgroup Hs}
    (hXY : Xs ≤ Ys) (hNY : N ≤ Ys) (hN : (N.subgroupOf Ys).Normal) (hXN : Xs ⊓ N = ⊥)
    (hX3 : 3 ∣ Nat.card Xs) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Hs) ≤ 1) :
    ¬ 3 ∣ Nat.card N := by
  intro hN3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨dx, hdx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Xs) 3 hX3
  obtain ⟨dn, hdn⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 hN3
  set d : Hs := (dx : Hs) with hddef
  set n : Hs := (dn : Hs) with hndef
  have hdmem : d ∈ Xs := by simpa [hddef] using dx.2
  have hdord : orderOf d = 3 := by rw [hddef, Subgroup.orderOf_coe, hdx]
  have hnmem : n ∈ N := by simpa [hndef] using dn.2
  have hnord : orderOf n = 3 := by rw [hndef, Subgroup.orderOf_coe, hdn]
  set dy : ↥Ys := ⟨d, hXY hdmem⟩ with hdydef
  set ny : ↥Ys := ⟨n, hNY hnmem⟩ with hnydef
  have hdyord : orderOf dy = 3 := by rw [hdydef, Subgroup.orderOf_mk, hdord]
  have hnyord : orderOf ny = 3 := by rw [hnydef, Subgroup.orderOf_mk, hnord]
  have hdyP : IsPGroup 3 (Subgroup.zpowers dy) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hdyord, pow_one])
  have hnyP : IsPGroup 3 (Subgroup.zpowers ny) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hnyord, pow_one])
  obtain ⟨P, hdy_le⟩ := IsPGroup.exists_le_sylow hdyP
  obtain ⟨Q, hny_le⟩ := IsPGroup.exists_le_sylow hnyP
  haveI : Finite (Sylow 3 ↥Ys) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hgPQ⟩ := MulAction.exists_smul_eq ↥Ys P Q
  have hnyQ : ny ∈ Q := hny_le (Subgroup.mem_zpowers ny)
  have hny_gP : ny ∈ MulAut.conj g • (P : Subgroup ↥Ys) := by
    rw [← Sylow.coe_subgroup_smul, hgPQ]
    exact hnyQ
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hny_gP
  obtain ⟨p, hpP, hp_eq⟩ := hny_gP
  have hmP : g⁻¹ * ny * g ∈ P := by
    have hp' : p = g⁻¹ * ny * g := by
      rw [← hp_eq, MulAut.smul_def, MulAut.conj_apply]
      group
    rwa [← hp']
  have hny_mem : ny ∈ N.subgroupOf Ys := by
    rw [Subgroup.mem_subgroupOf]
    exact hnmem
  have hmN : g⁻¹ * ny * g ∈ N.subgroupOf Ys := by
    have h := hN.conj_mem ny hny_mem g⁻¹
    simpa using h
  set m : Hs := ((g⁻¹ * ny * g : ↥Ys) : Hs) with hmdef
  have hmP' : m ∈ (P : Subgroup ↥Ys).map Ys.subtype :=
    ⟨g⁻¹ * ny * g, hmP, rfl⟩
  have hmN' : m ∈ N := by
    have h := hmN
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have hmord : orderOf m = 3 := by
    have hsem : SemiconjBy g (g⁻¹ * ny * g) ny := by
      show g * (g⁻¹ * ny * g) = ny * g
      group
    rw [hmdef, Subgroup.orderOf_coe, SemiconjBy.orderOf_eq g hsem, hnyord]
  have hP' : IsPGroup 3 ((P : Subgroup ↥Ys).map Ys.subtype) := P.isPGroup'.map Ys.subtype
  have hdP' : d ∈ (P : Subgroup ↥Ys).map Ys.subtype :=
    ⟨dy, hdy_le (Subgroup.mem_zpowers dy), rfl⟩
  have heq := s16c1_G47_unique_three hP' (Subgroup.zpowers_le.mpr hdP')
    (Subgroup.zpowers_le.mpr hmP')
    (by rw [Nat.card_zpowers, hdord]) (by rw [Nat.card_zpowers, hmord]) hr
  have hdN : d ∈ N := by
    have hdm : d ∈ Subgroup.zpowers m := by rw [← heq]; exact Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr hmN') hdm
  have hd1 : d = 1 := by
    have h : d ∈ Xs ⊓ N := ⟨hdmem, hdN⟩
    rwa [hXN, Subgroup.mem_bot] at h
  rw [hd1, orderOf_one] at hdord
  exact absurd hdord (by norm_num)

theorem s16c1_G47_frattini3 {Hs : Type} [Group Hs] [Finite Hs] {Ys Dd : Subgroup Hs}
    (hY : Ys.Normal) (hD : Dd ≤ Ys) (hD3 : Nat.card Dd = 3)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Hs) ≤ 1) :
    ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ normalizer (Dd : Set Hs), h = y * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Ys.Normal := hY
  set Dds : Subgroup ↥Ys := Dd.subgroupOf Ys with hDdsdef
  have hDds_card : Nat.card Dds = 3 := by
    rw [hDdsdef]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv).trans hD3
  have hDdsP : IsPGroup 3 Dds := IsPGroup.of_card (by rw [hDds_card, pow_one])
  obtain ⟨P, hDds_le⟩ := IsPGroup.exists_le_sylow hDdsP
  haveI : Finite (Sylow 3 ↥Ys) := Sylow.finite_of_finiteIndex P
  set P' : Subgroup Hs := (P : Subgroup ↥Ys).map Ys.subtype with hP'def
  have hP' : IsPGroup 3 P' := by
    rw [hP'def]
    exact P.isPGroup'.map Ys.subtype
  have hDd_le_P' : Dd ≤ P' := by
    intro x hx
    rw [hP'def]
    exact ⟨⟨x, hD hx⟩, hDds_le (by rw [hDdsdef, Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have htop : normalizer P' ⊔ Ys = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (p := 3) (N := Ys) P
    rwa [← hP'def] at h
  have hnorm_le : normalizer P' ≤ normalizer (Dd : Set Hs) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hb' : P'.map (MulAut.conj b).toMonoidHom = P' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
    have hle : Dd.map (MulAut.conj b).toMonoidHom ≤ P' := by
      rintro x ⟨y, hy, rfl⟩
      have hmem : MulAut.conj b y ∈ P'.map (MulAut.conj b).toMonoidHom :=
        ⟨y, hDd_le_P' hy, rfl⟩
      rwa [hb'] at hmem
    have hcard : Nat.card (Dd.map (MulAut.conj b).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
        (MulAut.conj b).injective, hD3]
    exact s16c1_G47_unique_three hP' hle hDd_le_P' hcard hD3 hr
  intro h
  have hmem : h ∈ Ys ⊔ normalizer P' := by
    rw [sup_comm, htop]
    exact Subgroup.mem_top h
  obtain ⟨y, hy, b, hb, hyb⟩ := (Subgroup.mem_sup_of_normal_left).1 hmem
  exact ⟨y, hy, b, hnorm_le hb, hyb.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
