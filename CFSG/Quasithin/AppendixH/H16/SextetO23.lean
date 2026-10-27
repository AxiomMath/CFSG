module

public import CFSG.Quasithin.AppendixH.H16.SextetN
public import CFSG.Quasithin.AppendixH.H16.S6Normal
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Open

theorem sxKS_le_pCoreOf : sxKS ≤ pCoreOf 2 sxGen := by
  have hKS : sxKS ≤ sxGen := sxKS_le_sxGen
  have hK_normal : (sxKS.subgroupOf sxGen).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKS).2 sxGen_le_normalizer_KS
  have hK_p : IsPGroup 2 (sxKS.subgroupOf sxGen) :=
    isPGroup_KS.of_equiv (Subgroup.subgroupOfEquivOfLe hKS).symm
  have hle : sxKS.subgroupOf sxGen ≤ CFSG.pCore 2 ↥sxGen :=
    le_sSup (show (sxKS.subgroupOf sxGen) ∈
      {K : Subgroup ↥sxGen | K.Normal ∧ IsPGroup 2 K} from ⟨hK_normal, hK_p⟩)
  have hmap : (sxKS.subgroupOf sxGen).map sxGen.subtype = sxKS :=
    Subgroup.map_subgroupOf_eq_of_le hKS
  rw [pCoreOf, ← hmap]
  exact Subgroup.map_mono hle

theorem pCoreOf_two_sxGen_le_sxN :
    pCoreOf 2 sxGen ≤ sxN := by
  have hN : ((CFSG.pCore 2 ↥sxGen).map sxAct).Normal :=
    (inferInstance : (CFSG.pCore 2 ↥sxGen).Normal).map sxAct sxAct_surjective
  have hbot : (CFSG.pCore 2 ↥sxGen).map sxAct = ⊥ := by
    haveI := hN
    apply S6_normal_two_group
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥sxGen) ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have hk' : (y : ↥sxGen) ^ (2 ^ k) = 1 := by
      simpa using congrArg (Subtype.val) hk
    rw [← map_pow, hk', map_one]
  have hle : CFSG.pCore 2 ↥sxGen ≤ sxAct.ker :=
    (Subgroup.map_eq_bot_iff _).mp hbot
  show (CFSG.pCore 2 ↥sxGen).map sxGen.subtype ≤ sxN
  rw [sxN]
  exact Subgroup.map_mono hle

theorem pCoreOf_two_sxGen :
    pCoreOf 2 sxGen = sxKS := by
  refine le_antisymm ?_ sxKS_le_pCoreOf
  intro x hx
  have hxN : x ∈ sxN := pCoreOf_two_sxGen_le_sxN hx
  have hx3 : x ^ 3 ∈ sxKS := sxN_pow_three_mem x hxN
  have hxP : x ∈ (CFSG.pCore 2 ↥sxGen).map sxGen.subtype := hx
  rw [Subgroup.mem_map] at hxP
  obtain ⟨y, hy, hyx⟩ := hxP
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥sxGen) ⟨y, hy⟩
  have hxk : x ^ (2 ^ k) = 1 := by
    have hk' : (y : S24) ^ (2 ^ k) = 1 := by
      have h2 : ((⟨y, hy⟩ : ↥(CFSG.pCore 2 ↥sxGen)) : ↥sxGen) ^ (2 ^ k) = 1 := by
        simpa using congrArg (Subtype.val) hk
      simpa using congrArg (Subtype.val) h2
    rw [← hyx]
    exact hk'
  let K : Subgroup ↥sxN := sxKS.subgroupOf sxN
  haveI hK : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer sxKS_le_sxN).2
      (sxN_le_sxGen.trans sxGen_le_normalizer_KS)
  let q : ↥sxN ⧸ K := QuotientGroup.mk (s := K) ⟨x, hxN⟩
  have hq3 : q ^ 3 = 1 := by
    change (QuotientGroup.mk (s := K) ⟨x, hxN⟩) ^ 3 = 1
    rw [← QuotientGroup.mk_pow K ⟨x, hxN⟩ 3, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hx3
  have hqk : q ^ (2 ^ k) = 1 := by
    change (QuotientGroup.mk (s := K) ⟨x, hxN⟩) ^ (2 ^ k) = 1
    rw [← QuotientGroup.mk_pow K ⟨x, hxN⟩ (2 ^ k), QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    simp [hxk]
  have hq1 : q = 1 := by
    have hd3 : orderOf q ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hq3
    have hd2 : orderOf q ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hqk
    have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hone : orderOf q = 1 := by
      have h := Nat.dvd_gcd hd3 hd2
      rw [hg] at h
      exact Nat.dvd_one.mp h
    exact orderOf_eq_one_iff.mp hone
  have hmem : (⟨x, hxN⟩ : ↥sxN) ∈ K := by
    rw [← QuotientGroup.eq_one_iff]
    change q = 1
    exact hq1
  exact Subgroup.mem_subgroupOf.mp hmem

theorem isO23_sxGen :
    IsO23 sxGen sxN := by
  refine ⟨sxN_le_sxGen, sxN_conj_mem, pCoreOf_two_sxGen_le_sxN, ?_, ?_⟩
  · intro n hn
    exact ⟨1, by rw [pow_one, pCoreOf_two_sxGen]; exact sxN_pow_three_mem n hn⟩
  · intro N' hN'le hconj hpCore h3pow
    have hN''norm : (N'.subgroupOf sxGen).Normal :=
      (Subgroup.normal_subgroupOf_iff hN'le).2 (fun h k hh hk => hconj k hk h hh)
    have hmapnorm : ((N'.subgroupOf sxGen).map sxAct).Normal :=
      hN''norm.map sxAct sxAct_surjective
    have hbot : (N'.subgroupOf sxGen).map sxAct = ⊥ := by
      haveI := hmapnorm
      apply S6_normal_three_group
      intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨n, hn, rfl⟩ := hz
      have hnN' : (n : S24) ∈ N' := Subgroup.mem_subgroupOf.mp hn
      obtain ⟨k, hk⟩ := h3pow (n : S24) hnN'
      refine ⟨k, ?_⟩
      rw [← map_pow]
      apply sxAct_of_mem_sxKS
      have hkS : (n : S24) ^ (3 ^ k) ∈ sxKS := by
        rw [pCoreOf_two_sxGen] at hk
        exact hk
      simpa using hkS
    have hle : N'.subgroupOf sxGen ≤ sxAct.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [sxN, ← Subgroup.map_subgroupOf_eq_of_le hN'le]
    exact Subgroup.map_mono hle

end CFSG.ASVolI.H16
