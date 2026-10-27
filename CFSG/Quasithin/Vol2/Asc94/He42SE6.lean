module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42s6_J_le_centralizer (S : HeSetup G) (hB : S.BaseFacts) {z : G}
    (hzZ : z ∈ S.Z) :
    S.J ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G) := by
  have hzA : z ∈ S.A := hB.Z_le_A hzZ
  have hzA' : z ∈ S.A' := hB.Z_le_A' hzZ
  have hA : S.A ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    · intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hB.A_comm z hzA a ha
    · intro b hb
      exact hB.A_comm b (hB.Z_le_A (hB.B_le_Z hb)) a ha
  have hA' : S.A' ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    · intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hB.A'_comm z hzA' a ha
    · intro b hb
      exact hB.A'_comm b (hB.Z_le_A' (hB.B_le_Z hb)) a ha
  exact sup_le hA hA'

private theorem he42s6_mem_of_relIndex_three {J K : Subgroup G} (hJK : J ≤ K)
    (hKN : K ≤ Subgroup.normalizer (J : Set G)) (hidx : J.relIndex K = 3)
    {n : G} (hn : n ∈ K) {m : ℕ} (hnm : n ^ 2 ^ m = 1) : n ∈ J := by
  haveI : (J.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2 hKN
  have hidx' : (J.subgroupOf K).index = 3 := hidx
  have hk3 : (⟨n, hn⟩ : K) ^ 3 ∈ J.subgroupOf K := by
    have h := Subgroup.pow_index_mem (J.subgroupOf K) (⟨n, hn⟩ : K)
    rwa [hidx'] at h
  have hk2 : (⟨n, hn⟩ : K) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hnm)
  have hq3 : ((⟨n, hn⟩ : K) : K ⧸ J.subgroupOf K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow (J.subgroupOf K), QuotientGroup.eq_one_iff]
    exact hk3
  have hq2 : ((⟨n, hn⟩ : K) : K ⧸ J.subgroupOf K) ^ 2 ^ m = 1 := by
    rw [← QuotientGroup.mk_pow (J.subgroupOf K), hk2, QuotientGroup.mk_one]
  have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  have hgcd := pow_gcd_eq_one.2 ⟨hq3, hq2⟩
  rw [hcop, pow_one, QuotientGroup.eq_one_iff] at hgcd
  exact Subgroup.mem_subgroupOf.1 hgcd

private theorem he42s6_P_le_J {P J : Subgroup G} (hJP : J ≤ P)
    (hP : IsPGroup 2 ↥P) (hfix : ∀ n ∈ P, n ∈ Subgroup.normalizer (J : Set G) → n ∈ J) :
    P ≤ J := by
  by_contra hPJ
  obtain ⟨p, hpP, hpJ⟩ := SetLike.not_le_iff_exists.1 hPJ
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : ∀ H : Subgroup ↥P, H < ⊤ → H < Subgroup.normalizer (H : Set ↥P) :=
    Group.normalizerCondition_of_isNilpotent
  have hlt : J.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hpJ ?_
    have hmem : (⟨p, hpP⟩ : ↥P) ∈ J.subgroupOf P := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  obtain ⟨n, hnN, hnJ⟩ := SetLike.exists_of_lt (hnc _ hlt)
  have hnJ' : (n : G) ∉ J := fun h => hnJ (Subgroup.mem_subgroupOf.2 h)
  have hnorm : (n : G) ∈ Subgroup.normalizer (J : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hxP : x ∈ P := hJP hx
    have h1 : (⟨x, hxP⟩ : ↥P) ∈ J.subgroupOf P := Subgroup.mem_subgroupOf.2 hx
    have h2 := (Subgroup.mem_normalizer_iff.1 hnN ⟨x, hxP⟩).1 h1
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa using h3
  exact hnJ' (hfix (n : G) n.2 hnorm)

private theorem he42s6_fix (S : HeSetup G) (hB : S.BaseFacts) {P : Subgroup G}
    (hPB : P ≤ Subgroup.centralizer (S.B : Set G)) (hP : IsPGroup 2 ↥P) :
    ∀ n ∈ P, n ∈ Subgroup.normalizer (S.J : Set G) → n ∈ S.J := by
  intro n hnP hnN
  have hnN' : n ∈ S.N := by
    rw [S.hN]
    exact hnN
  have hnK : n ∈ S.K := Subgroup.mem_inf.2 ⟨hnN', hPB hnP⟩
  obtain ⟨m, hm⟩ := hP ⟨n, hnP⟩
  have hnm : n ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  have hidx : S.J.relIndex S.K = 3 := by
    have h1 : S.J.relIndex S.K * Nat.card ↥(S.J ⊓ S.K) = Nat.card ↥S.K :=
      Subgroup.relIndex_mul_card S.J S.K
    rw [inf_eq_left.2 hB.J_le_K, hB.card_J, hB.card_K] at h1
    omega
  have hKN : S.K ≤ Subgroup.normalizer (S.J : Set G) := by
    intro k hk
    have h := hB.K_le_N hk
    rw [S.hN] at h
    exact h
  exact he42s6_mem_of_relIndex_three hB.J_le_K hKN hidx hnK hnm

theorem HeSetup.le_J_of_isPGroup (S : HeSetup G) (hB : S.BaseFacts) {z : G} (hzZ : z ∈ S.Z)
    (hP : IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G)))
    {c : G} (hcz : c * z = z * c) (hcB : ∀ b ∈ S.B, c * b = b * c) : c ∈ S.J := by
  have hPJ : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G) ≤ S.J :=
    he42s6_P_le_J (he42s6_J_le_centralizer S hB hzZ) hP (he42s6_fix S hB inf_le_right hP)
  refine hPJ (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_,
    Subgroup.mem_centralizer_iff.2 ?_⟩)
  · intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hcz.symm
  · intro b hb
    exact (hcB b hb).symm

end CFSG.Quasithin.A94.He42
