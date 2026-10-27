module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.lemma_9_5
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 9.6 from BG Section 9

This file contains the support package and proof of Theorem 9.6 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section9_generatorRank_le_natCard
    (G : Type*) [Group G] [Finite G] :
    generatorRank G ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec G
  calc
    generatorRank G = Group.rank G := generatorRank_eq_group_rank G
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card G := by simpa using Finset.card_le_univ S
    _ = Nat.card G := by simp [Nat.card_eq_fintype_card]

private theorem CFSG.section9_primeRank_le_natCard
    {p : ℕ} (G : Type*) [Group G] [Finite G] :
    primeRank p G ≤ Nat.card G := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hApA, _hAcomm, hnA⟩
    exact hnA.trans <| (section9_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

omit [IsMinCE G] in
private theorem CFSG.section9_primeRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} [Fact q.Prime] {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ primeRank q K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    letI : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <| (section9_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩

private theorem CFSG.section9_exists_pSubgroup_three_le_generatorRank_of_three_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ B : Subgroup R,
      IsPGroup p.val B ∧ IsMulCommutative B ∧ 3 ≤ generatorRank B := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 2 < sSup S := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section9_primeRank_le_natCard (p := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 2 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 2 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B}
  have hqrank' : 2 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
    exact hnB.trans <| (section9_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨B, hBq, hBcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, B, hBq, hBcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

private theorem CFSG.section9_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ B : Subgroup R,
      IsPGroup p.val B ∧ IsMulCommutative B ∧ 2 ≤ generatorRank B := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 1 < sSup S := by
    exact lt_of_lt_of_le (by decide : 1 < 2) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section9_primeRank_le_natCard (p := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 1 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 1 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B}
  have hqrank' : 1 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
    exact hnB.trans <| (section9_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨B, hBq, hBcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, B, hBq, hBcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

private theorem CFSG.section9_not_isCyclic_of_two_le_generatorRank
    {H : Type*} [Group H] [Finite H] (hHrank : 2 ≤ generatorRank H) :
    ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  omega

omit [IsMinCE G] in
private theorem CFSG.section9_prime_dvd_card_of_pSubgroup_two_le_generatorRank
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hBp : IsPGroup p B) (hBgen : 2 ≤ generatorRank B) :
    p ∣ Nat.card G := by
  have hBnoncyc : ¬ IsCyclic B := section9_not_isCyclic_of_two_le_generatorRank hBgen
  have hBnontrivial : Nontrivial B := by
    by_contra hnt
    letI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    exact hBnoncyc (isCyclic_of_subsingleton (α := B))
  obtain ⟨n, hn_pos, hBcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := B) (hG := hBp)).mp hBnontrivial
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hp_dvd_B : p ∣ Nat.card B := by
    rw [hBcard, pow_succ']
    exact dvd_mul_right p (p ^ m)
  exact hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)

omit [IsMinCE G] in
private theorem CFSG.section9_subgroup_nontrivial_of_two_le_groupRank
    {K : Subgroup G} (hKrank : 2 ≤ groupRank K) :
    ∃ k : G, k ∈ K ∧ k ≠ 1 := by
  obtain ⟨_p, B, _hBp, _hBcomm, hBgen⟩ :=
    section9_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank (R := K) hKrank
  have hBnoncyc : ¬ IsCyclic B := section9_not_isCyclic_of_two_le_generatorRank hBgen
  have hBnontrivial : Nontrivial B := by
    by_contra hnt
    letI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    exact hBnoncyc (isCyclic_of_subsingleton (α := B))
  obtain ⟨b, hb_ne⟩ := exists_ne (1 : B)
  have hbK_ne : (b : K) ≠ 1 := by
    intro hb
    exact hb_ne (Subtype.ext hb)
  refine ⟨(b : K), (b : K).2, ?_⟩
  intro hbG
  exact hbK_ne (Subtype.ext hbG)

private theorem CFSG.section9_centralizer_ne_top_of_nontrivial_subgroup
    {K : Subgroup G} (hKnontrivial : ∃ k : G, k ∈ K ∧ k ≠ 1) :
    Subgroup.centralizer (K : Set G) ≠ ⊤ := by
  rcases hKnontrivial with ⟨k, hkK, hk_ne⟩
  intro htop
  have hk_center : k ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hxcent : x ∈ Subgroup.centralizer (K : Set G) := by
      rw [htop]
      exact Subgroup.mem_top x
    exact ((Subgroup.mem_centralizer_iff.mp hxcent) k hkK).symm
  have hk_one : k = 1 := by
    simpa [center_eq_bot_of_min_ce (G := G)] using hk_center
  exact hk_ne hk_one

omit [IsMinCE G] in
private theorem CFSG.section9_generatorRank_map_subtype_eq
    {K : Subgroup G} (A : Subgroup K) :
    generatorRank (A.map K.subtype) = generatorRank A := by
  rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
  let e : A ≃* A.map K.subtype :=
    Subgroup.equivMapOfInjective (f := K.subtype) A K.subtype_injective
  exact (Group.rank_congr e).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_map_subtype_le
    {K : Subgroup G} (A : Subgroup K) :
    A.map K.subtype ≤ K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
  exact a.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_subgroupOf_map_subtype_eq
    {K : Subgroup G} (A : Subgroup K) :
    (A.map K.subtype).subgroupOf K = A := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ A.map K.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := Subtype.ext hyx
    simpa [hy_eq] using hy
  · intro hx
    change (x : G) ∈ A.map K.subtype
    exact Subgroup.mem_map_of_mem K.subtype hx

private theorem CFSG.section9_unique_of_three_le_groupRank
    {K : Subgroup G} (hKproper : K ≠ ⊤) (hKrank : 3 ≤ groupRank K) :
    K ∈ section9UniqueSubgroups G := by
  classical
  obtain ⟨p0, B0, hB0p, hB0comm, hB0gen⟩ :=
    section9_exists_pSubgroup_three_le_generatorRank_of_three_le_groupRank (R := K) hKrank
  let p : ℕ := p0.val
  have hp : Nat.Prime p := p0.property
  letI : Fact p.Prime := ⟨hp⟩
  let B : Subgroup G := B0.map K.subtype
  have hB_le_K : B ≤ K := section9_map_subtype_le (K := K) B0
  have hBp : IsPGroup p B := by
    dsimp [B]
    exact IsPGroup.map hB0p K.subtype
  have hBcomm : IsMulCommutative B := by
    dsimp [B]
    letI : IsMulCommutative B0 := hB0comm
    simpa using (Subgroup.map_isMulCommutative (f := K.subtype) (H := B0))
  have hBgen_eq : generatorRank B = generatorRank B0 := by
    simpa [B] using section9_generatorRank_map_subtype_eq (K := K) B0
  have hBgen : 3 ≤ generatorRank B := by
    simpa [hBgen_eq] using hB0gen
  have hBnoncyc : ¬ IsCyclic B :=
    section9_not_isCyclic_of_two_le_generatorRank (le_trans (by decide : 2 ≤ 3) hBgen)
  have hpG : p ∣ Nat.card G :=
    section9_prime_dvd_card_of_pSubgroup_two_le_generatorRank
      (G := G) hBp (le_trans (by decide : 2 ≤ 3) hBgen)
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  obtain ⟨P, hBP⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hBp
  have hPrank : 3 ≤ groupRank (P : Subgroup G) :=
    groupRank_at_least_three_of_generatorRank_subgroup
      (q := p) hp hBP hBp hBcomm hBgen
  obtain ⟨A0, hA0scn⟩ :=
    lemma_5_1_a (p := p) hpodd (R := ↥(P : Subgroup G)) P.isPGroup' hPrank
  let A : Subgroup G := A0.map (P : Subgroup G).subtype
  have hA_le_P : A ≤ (P : Subgroup G) :=
    section9_map_subtype_le (K := (P : Subgroup G)) A0
  have hA_subgroupOf : A.subgroupOf (P : Subgroup G) = A0 := by
    simpa [A] using
      section9_subgroupOf_map_subtype_eq (K := (P : Subgroup G)) A0
  have hAscn : A ∈ scnPrimeSubgroups 3 p G := by
    refine ⟨P, hA_le_P, ?_⟩
    simpa [hA_subgroupOf] using hA0scn
  have hAunique : A ∈ section9UniqueSubgroups G := lemma_9_5 hAscn
  have hA0comm : IsMulCommutative A0 :=
    (scnSubgroup_normal_commutative
      (p := p) (R := ↥(P : Subgroup G)) P.isPGroup' hA0scn).2
  have hAp : IsPGroup p A := by
    dsimp [A]
    exact IsPGroup.map (P.isPGroup'.to_subgroup A0) (P : Subgroup G).subtype
  have hAcomm : IsMulCommutative A := by
    dsimp [A]
    letI : IsMulCommutative A0 := hA0comm
    simpa using
      (Subgroup.map_isMulCommutative (f := (P : Subgroup G).subtype) (H := A0))
  have hA0gen : 3 ≤ generatorRank A0 :=
    scnSubgroup_generatorRank_at_least_three
      (p := p) hpodd (R := ↥(P : Subgroup G)) P.isPGroup' hA0scn
  have hAgen_eq : generatorRank A = generatorRank A0 := by
    simpa [A] using
      section9_generatorRank_map_subtype_eq (K := (P : Subgroup G)) A0
  have hAgen : 3 ≤ generatorRank A := by
    simpa [hAgen_eq] using hA0gen
  have hB_le_centralizer : B ≤ Subgroup.centralizer (B : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).2 hBcomm
  have hcentralizerRank : 3 ≤ primeRank p (Subgroup.centralizer (B : Set G)) :=
    section9_primeRank_at_least_three_of_generatorRank_subgroup
      (q := p) hB_le_centralizer hBp hBcomm hBgen
  have hBunique : B ∈ section9UniqueSubgroups G :=
    corollary_9_3 (p := p) (A := A) (B := B)
      hAp hAcomm hBp hBnoncyc hAunique hAgen hcentralizerRank
  exact section9_unique_of_le hB_le_K hKproper hBunique

/-- Theorem 9.6, the Uniqueness Theorem. -/
public theorem CFSG.theorem_9_6
    {K : Subgroup G} (hKproper : K ≠ ⊤) (hKrank : 2 ≤ groupRank K)
    (hlarge : 3 ≤ groupRank K ∨
      3 ≤ groupRank (Subgroup.centralizer (K : Set G))) :
    K ∈ section9UniqueSubgroups G := by
  classical
  rcases hlarge with hKlarge | hcentralizerLarge
  · exact section9_unique_of_three_le_groupRank hKproper hKlarge
  · let C : Subgroup G := Subgroup.centralizer (K : Set G)
    have hKnontrivial : ∃ k : G, k ∈ K ∧ k ≠ 1 :=
      section9_subgroup_nontrivial_of_two_le_groupRank hKrank
    have hCproper : C ≠ ⊤ := by
      simpa [C] using
        section9_centralizer_ne_top_of_nontrivial_subgroup
          (K := K) hKnontrivial
    have hCunique : C ∈ section9UniqueSubgroups G :=
      section9_unique_of_three_le_groupRank
        (K := C) hCproper (by simpa [C] using hcentralizerLarge)
    have hK_le_centralizer_C : K ≤ Subgroup.centralizer (C : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hc' : c ∈ Subgroup.centralizer (K : Set G) := by
        simpa [C] using hc
      exact ((Subgroup.mem_centralizer_iff.mp hc') k hk).symm
    exact corollary_9_2 (L := C) (K := K) hCunique hK_le_centralizer_C hKrank

end Section9
