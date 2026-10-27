module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_4_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.4(c) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_rank_two_elementary_le_maximal_of_not_sigma
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M) (hAM : A ≤ M)
    (hA : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G) :
    A ∈ maximalElementaryAbelianSubgroups p.val G := by
  classical
  by_contra hA_not_max
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hA with ⟨hAcard, hAelem⟩
  have hAunique : A ∈ section9UniqueSubgroups G :=
    theorem_9_6_in_particular (G := G)
      ⟨p.val, p.property, ⟨hAcard, hAelem⟩, hA_not_max⟩
  have hAp : IsPGroup p.val A := by
    letI : IsElementaryAbelian p.val A := hAelem
    exact IsElementaryAbelian.isPGroup p.val A
  let A_M : Subgroup M := A.subgroupOf M
  have hA_M_p : IsPGroup p.val A_M :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  obtain ⟨P, hA_M_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hA_M_p
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hA_le_PG : A ≤ PG := by
    intro a ha
    let aM : M := ⟨a, hAM ha⟩
    have haM : aM ∈ A_M := ha
    exact Subgroup.mem_map.mpr ⟨aM, hA_M_le_P haM, rfl⟩
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rw [hAcard, pow_two]
    exact dvd_mul_right p.val p.val
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hAcard_one : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hAbot
    have hp_dvd_one : p.val ∣ 1 := by
      simpa [hAcard_one] using hp_dvd_A
    exact p.property.not_dvd_one hp_dvd_one
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    exact hAne <| le_bot_iff.mp <| hA_le_PG.trans (le_of_eq hPGbot)
  have hA_le_normPG : A ≤ Subgroup.normalizer (PG : Set G) :=
    hA_le_PG.trans Subgroup.le_normalizer
  have hnormPG_le_M : Subgroup.normalizer (PG : Set G) ≤ M :=
    section10_normalizer_le_maximal_of_unique_seed hM hAunique hAM
      hA_le_normPG hPG_le_M hPGne
  have hpM : p ∈ subgroupPrimeSet M := by
    exact hp_dvd_A.trans (Subgroup.card_dvd_of_le hAM)
  have hpσ_mem : p ∈ section10SigmaPrimes M := by
    refine ⟨hpM, P, ?_⟩
    simpa [PG] using hnormPG_le_M
  exact hpσ hpσ_mem

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_isElementaryAbelian_map_pre
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} [IsElementaryAbelian p A]
    {G' : Type*} [Group G'] (f : G →* G') :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : G') = f y := by simpa using hyx.symm
  calc
    (x : G') ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

omit [IsMinCE G] in
private theorem CFSG.section10_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank_pre
    {p : ℕ} {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ primeRank p R) :
    ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ 2 ≤ generatorRank A := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hrank' : 1 < sSup T := by
    exact lt_of_lt_of_le (by decide : 1 < 2) (by simpa [primeRank, T] using hrank)
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard_pre A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by
      simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

private theorem CFSG.section10_exists_rank_two_elementary_le_of_primeRank_eq_two
    {M : Subgroup G} {p : Nat.Primes} (hprank : primeRank p.val M = 2) :
    ∃ A : Subgroup G, A ≤ M ∧ A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have htwo : 2 ≤ primeRank p.val M := by omega
  obtain ⟨B, hBp, hBcomm, hBgen⟩ :=
    section10_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank_pre
      (p := p.val) (R := M) htwo
  have hBnoncyc : ¬ IsCyclic B := by
    intro hcyc
    have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hcyc
    omega
  have hp_dvd_B : p.val ∣ Nat.card B := by
    rcases hBp.card_eq_or_dvd with hBcard | hdiv
    · haveI : Subsingleton B := (Nat.card_eq_one_iff_unique.mp hBcard).1
      exact False.elim (hBnoncyc (isCyclic_of_subsingleton (α := B)))
    · exact hdiv
  have hp_dvd_G : p.val ∣ Nat.card G :=
    (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)).trans
      (Subgroup.card_subgroup_dvd_card M)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Fact (IsPGroup p.val B) := ⟨hBp⟩
  obtain ⟨E, _hEnorm, hEcard, hEelem⟩ :=
    lemma_4_5_a (R := B) (p := p.val) hpodd hBnoncyc
  let EM : Subgroup M := E.map B.subtype
  let A : Subgroup G := EM.map M.subtype
  have hEMcard : Nat.card EM = Nat.card E := by
    simpa [EM] using
      (Subgroup.card_map_of_injective (K := E) (f := B.subtype) B.subtype_injective)
  have hAcard_map : Nat.card A = Nat.card EM := by
    simpa [A] using
      (Subgroup.card_map_of_injective (K := EM) (f := M.subtype) M.subtype_injective)
  have hAcard : Nat.card A = p.val ^ 2 := by
    rw [hAcard_map, hEMcard, hEcard]
  have hEMelem : IsElementaryAbelian p.val EM := by
    letI : IsElementaryAbelian p.val E := hEelem
    simpa [EM] using
      section10_isElementaryAbelian_map_pre (G := B) (A := E) (G' := M) B.subtype
  have hAelem : IsElementaryAbelian p.val A := by
    letI : IsElementaryAbelian p.val EM := hEMelem
    simpa [A] using
      section10_isElementaryAbelian_map_pre (G := M) (A := EM) (G' := G) M.subtype
  have hA_le_M : A ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  exact ⟨A, hA_le_M, ⟨hAcard, hAelem⟩⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_rankTwoMaximal_subgroupOf_of_le_pre
    {p : Nat.Primes} {A S : Subgroup G} (hAS : A ≤ S)
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    A.subgroupOf S ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmax'⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAsub_card : Nat.card (A.subgroupOf S) = p.val ^ 2 := by
    simpa [hAcard] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hAS).toEquiv
  have hAsub_elem : IsElementaryAbelian p.val (A.subgroupOf S) :=
    IsElementaryAbelian.subgroupOf (G := G) (p := p.val) hAS
  have hAsub_max : A.subgroupOf S ∈ maximalElementaryAbelianSubgroups p.val S := by
    refine ⟨hAsub_elem, ?_⟩
    intro B hAB hBelem
    let Bmap : Subgroup G := B.map S.subtype
    have hA_le_Bmap : A ≤ Bmap := by
      intro a ha
      let aS : A.subgroupOf S := ⟨⟨a, hAS ha⟩, ha⟩
      exact Subgroup.mem_map.mpr ⟨aS, hAB aS.2, rfl⟩
    have hBmap_elem : IsElementaryAbelian p.val Bmap := by
      letI : IsElementaryAbelian p.val B := hBelem
      simpa [Bmap] using
        section10_isElementaryAbelian_map_pre (G := S) (p := p.val) (A := B) (G' := G)
          S.subtype
    have hEq : A = Bmap := hAmax' Bmap hA_le_Bmap hBmap_elem
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxA : ((x : S) : G) ∈ A := hx
      rw [hEq] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨y, hyB, hyx⟩
      have : y = x := Subtype.ext hyx
      simpa [this] using hyB
    · intro hx
      have hxMap : ((x : S) : G) ∈ Bmap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← hEq] at hxMap
      exact hxMap
  exact ⟨⟨hAsub_card, hAsub_elem⟩, hAsub_max⟩

private theorem CFSG.section10_not_rank_two_maximal_of_ideal
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) {A : Subgroup G}
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    False := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hpβG with ⟨hprankG, hnotNarrow⟩
  rcases hArankTwo with ⟨_hAcard, hAelem⟩
  have hprimeRank_le : 3 ≤ primeRank p.val G := Nat.succ_le_of_lt hprankG
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
  have hAS_rank :
      A.subgroupOf (S : Subgroup G) ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S :=
    section10_rankTwoMaximal_subgroupOf_of_le_pre (G := G) hAS
      ⟨_hAcard, hAelem⟩ hAmax
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rw [_hAcard, pow_two]
    exact dvd_mul_right p.val p.val
  have hp_dvd_G : p.val ∣ Nat.card G :=
    hp_dvd_A.trans (Subgroup.card_subgroup_dvd_card A)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hSrank : 3 ≤ groupRank (S : Subgroup G) :=
    hprimeRank_le.trans (section10_primeRank_le_groupRank_sylow_pre (G := G) S)
  have hNarrowS : IsNarrowPGroup p.val S :=
    (theorem_5_3 (p := p.val) hpodd (R := S) S.isPGroup' hSrank).2
      ⟨A.subgroupOf (S : Subgroup G), hAS_rank.1, hAS_rank.2⟩
  exact (hnotNarrow S) hNarrowS

/-- Lemma 10.4(c). -/
public theorem CFSG.lemma_10_4_c
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M) (hprank : primeRank p.val M = 2) :
    ¬ section10IdealPrime p G ∧
      ∀ {A : Subgroup G}, A ≤ M →
        A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G →
          A ∈ maximalElementaryAbelianSubgroups p.val G := by
  constructor
  · intro hpβ
    obtain ⟨A, hAM, hArankTwo⟩ :=
      section10_exists_rank_two_elementary_le_of_primeRank_eq_two
        (G := G) (M := M) (p := p) hprank
    have hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G :=
      section10_rank_two_elementary_le_maximal_of_not_sigma hM hpσ hAM hArankTwo
    exact section10_not_rank_two_maximal_of_ideal hpβ hArankTwo hAmax
  · intro A hAM hArankTwo
    exact section10_rank_two_elementary_le_maximal_of_not_sigma hM hpσ hAM hArankTwo

end Section10
