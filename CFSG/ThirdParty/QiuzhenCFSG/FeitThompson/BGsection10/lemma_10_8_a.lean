module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.corollary_10_7_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_6_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section10_beta_subset_alpha
    (M : Subgroup G) :
    section10BetaPrimes M ⊆ section10AlphaPrimes M := by
  intro p hpβ
  exact hpβ.1

private theorem CFSG.section10_beta_subset_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10BetaPrimes M ⊆ section10SigmaPrimes M := by
  intro p hpβ
  exact section10_alpha_subset_sigma hM hpβ.1


public theorem CFSG.section10_mbetaSubgroup_le_msigmaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10MbetaSubgroup M ≤ section10MsigmaSubgroup M := by
  simpa [section10MbetaSubgroup, section10MsigmaSubgroup] using
    section10_piCore_mono (H := M) (section10_beta_subset_sigma hM)

private theorem CFSG.section10_prime_not_dvd_maximal_index_of_mem_beta
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpβ : p ∈ section10BetaPrimes M) :
    ¬ p.val ∣ M.index :=
  section10_prime_not_dvd_maximal_index_of_mem_alpha hM hpβ.1

private theorem CFSG.section10_mbeta_isHall_of_mbetaSubgroup_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hKHall : IsHallSubgroup (section10BetaPrimes M) (section10MbetaSubgroup M)) :
    IsHallSubgroup (section10BetaPrimes M) (section10Mbeta M) := by
  classical
  let π : Set Nat.Primes := section10BetaPrimes M
  let K : Subgroup M := section10MbetaSubgroup M
  refine isHallSubgroup_of (G := G) (π := π) (H := section10Mbeta M) ?_ ?_
  · intro p hp_dvd
    have hcard_eq : Nat.card (section10Mbeta M) = Nat.card K := by
      simpa [section10Mbeta, K] using
        (Subgroup.card_map_of_injective (K := K) (f := M.subtype) M.subtype_injective)
    exact hKHall.p_in_pi_of_p_dvd_card p (by simpa [hcard_eq] using hp_dvd)
  · intro p hpβ hp_dvd_index
    have hidx : (section10Mbeta M).index = K.index * M.index := by
      simpa [section10Mbeta, K] using
        (Subgroup.index_map_subtype (H := M) (K := K))
    have hp_dvd_prod : p.val ∣ K.index * M.index := by
      simpa [hidx] using hp_dvd_index
    rcases p.property.dvd_or_dvd hp_dvd_prod with hpK | hpM
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpK) (by simpa [π] using hpβ)
    · exact section10_prime_not_dvd_maximal_index_of_mem_beta hM
        (by simpa [π] using hpβ) hpM

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section10_generatorRank_le_primeRank_of_isPGroup_local
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hRcomm : IsMulCommutative R) :
    generatorRank R ≤ primeRank p R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <| (section10_generatorRank_le_natCard_pre A).trans
      (Subgroup.card_le_card_group A)
  have htop_p : IsPGroup p (⊤ : Subgroup R) := by
    simpa using hRp.to_subgroup (⊤ : Subgroup R)
  have htop_comm : IsMulCommutative (⊤ : Subgroup R) := by
    let : IsMulCommutative R := hRcomm
    infer_instance
  have hgen_le_top : generatorRank R ≤ generatorRank (⊤ : Subgroup R) := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact le_of_eq (Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R)).symm
  have hmem : generatorRank R ∈ T := ⟨⊤, htop_p, htop_comm, hgen_le_top⟩
  simpa [primeRank, T] using (le_csSup hTbdd hmem)

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section10_groupRank_le_primeRank_of_isPGroup_local
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) :
    groupRank R ≤ primeRank p R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard_pre (q := q) R)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    let : Fact q.Prime := ⟨hq⟩
    have hqrank_le : primeRank q R ≤ primeRank p R := by
      by_cases hT :
          {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A}.Nonempty
      · have hTbdd : BddAbove
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} := by
          refine ⟨Nat.card R, ?_⟩
          intro n hn
          rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
          exact hnA.trans <| (section10_generatorRank_le_natCard_pre A).trans
            (Subgroup.card_le_card_group A)
        have hsT_mem : sSup
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} ∈
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} :=
          Nat.sSup_mem hT hTbdd
        rcases hsT_mem with ⟨A, hAq, hAcomm, hsT_le⟩
        have hAp : IsPGroup p A := hRp.to_subgroup A
        have hgen_le_p : generatorRank A ≤ primeRank p R :=
          (section10_generatorRank_le_primeRank_of_isPGroup_local
              (R := A) (p := p) hAp hAcomm).trans
            (by simpa using section8_primeRank_le_of_subgroup (G := R) A p)
        rw [primeRank]
        exact hsT_le.trans hgen_le_p
      · have hTempty :
          {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
        rw [primeRank, hTempty]
        simp
    rw [groupRank]
    exact hsSup_le.trans hqrank_le
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section10_groupRank_le_two_of_primeRank_le_two_of_isPGroup_local
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hrank : primeRank p R ≤ 2) :
    groupRank R ≤ 2 :=
  (section10_groupRank_le_primeRank_of_isPGroup_local (R := R) (p := p) hRp).trans hrank

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_narrow_of_not_mem_alpha
    {M : Subgroup G} {p : Nat.Primes} (hpα : p ∉ section10AlphaPrimes M)
    (P : Sylow p.val M) :
    IsNarrowPGroup p.val (P : Subgroup M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hprankM_le : primeRank p.val M ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ primeRank p.val M := by omega
    have hpM : p ∈ subgroupPrimeSet M := by
      simpa [subgroupPrimeSet] using
        section10_prime_dvd_card_of_three_le_primeRank_pre
          (p := p.val) (R := M) hthree
    exact hpα ⟨hpM, by omega⟩
  have hprankP_le : primeRank p.val (P : Subgroup M) ≤ 2 :=
    (section8_primeRank_le_of_subgroup (G := M) (P : Subgroup M) p.val).trans hprankM_le
  have hgrankP_le : groupRank (P : Subgroup M) ≤ 2 :=
    section10_groupRank_le_two_of_primeRank_le_two_of_isPGroup_local
      (R := (P : Subgroup M)) (p := p.val) P.isPGroup' hprankP_le
  exact ⟨P.isPGroup', Or.inl hgrankP_le⟩

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section10_isNarrowPGroup_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S] {p : ℕ}
    (e : R ≃* S) :
    IsNarrowPGroup p S → IsNarrowPGroup p R := by
  intro hS
  refine ⟨hS.1.of_equiv e.symm, ?_⟩
  rcases hS.2 with hsmall | hsplit
  · exact Or.inl ((section10_groupRank_le_of_equiv_pre e.symm).trans hsmall)
  · rcases hsplit with ⟨S₀, S₁, hS₀card, hS₁cyc, hdisjS, hcentS⟩
    let R₀ : Subgroup R := S₀.map e.symm.toMonoidHom
    let R₁ : Subgroup R := S₁.map e.symm.toMonoidHom
    have hR₀card : Nat.card R₀ = p := by
      calc
        Nat.card R₀ = Nat.card S₀ := by
          simpa [R₀] using
            (Subgroup.card_map_of_injective
              (K := S₀) (f := e.symm.toMonoidHom) e.symm.injective)
        _ = p := hS₀card
    have hR₁cyc : IsCyclic R₁ := by
      let eR₁ : S₁ ≃* R₁ :=
        Subgroup.equivMapOfInjective (f := e.symm.toMonoidHom) S₁ e.symm.injective
      exact eR₁.isCyclic.1 hS₁cyc
    have hdisjR : Disjoint R₀ R₁ := by
      rw [Subgroup.disjoint_def]
      intro x hxR₀ hxR₁
      have hexS₀ : e x ∈ S₀ := by
        rcases Subgroup.mem_map.mp hxR₀ with ⟨y, hyS₀, hyx⟩
        have hy_eq : y = e x := by
          simpa using congrArg e hyx
        simpa [hy_eq] using hyS₀
      have hexS₁ : e x ∈ S₁ := by
        rcases Subgroup.mem_map.mp hxR₁ with ⟨y, hyS₁, hyx⟩
        have hy_eq : y = e x := by
          simpa using congrArg e hyx
        simpa [hy_eq] using hyS₁
      have hex_bot : e x ∈ (⊥ : Subgroup S) :=
        Subgroup.disjoint_def.mp hdisjS hexS₀ hexS₁
      have hx_one : x = 1 := by
        apply e.injective
        simpa using (Subgroup.mem_bot.mp hex_bot)
      simp [hx_one]
    have hmap_sup : (S₀ ⊔ S₁).map e.symm.toMonoidHom = R₀ ⊔ R₁ := by
      simp [R₀, R₁, Subgroup.map_sup]
    have hcentR : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁ := by
      ext x
      constructor
      · intro hxC
        have hexC : e x ∈ Subgroup.centralizer (S₀ : Set S) := by
          rw [Subgroup.mem_centralizer_iff] at hxC ⊢
          intro y hyS₀
          let r : R := e.symm y
          have hrR₀ : r ∈ R₀ := Subgroup.mem_map.mpr ⟨y, hyS₀, rfl⟩
          have hcomm := hxC r hrR₀
          simpa [r] using congrArg e hcomm
        have hex_sup : e x ∈ S₀ ⊔ S₁ := by
          simpa [hcentS] using hexC
        have hxmap : x ∈ (S₀ ⊔ S₁).map e.symm.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨e x, hex_sup, by simp⟩
        rw [hmap_sup] at hxmap
        exact hxmap
      · intro hxSup
        have hxmap : x ∈ (S₀ ⊔ S₁).map e.symm.toMonoidHom := by
          rw [hmap_sup]
          exact hxSup
        rcases Subgroup.mem_map.mp hxmap with ⟨y, hySup, hyx⟩
        have hey : y = e x := by
          simpa using congrArg e hyx
        have hexC : e x ∈ Subgroup.centralizer (S₀ : Set S) := by
          simpa [hey, hcentS] using hySup
        rw [Subgroup.mem_centralizer_iff] at hexC ⊢
        intro r hrR₀
        have herS₀ : e r ∈ S₀ := by
          rcases Subgroup.mem_map.mp hrR₀ with ⟨z, hzS₀, hzr⟩
          have hz_eq : z = e r := by
            simpa using congrArg e hzr
          simpa [hz_eq] using hzS₀
        have hcomm := hexC (e r) herS₀
        simpa using congrArg e.symm hcomm
    exact Or.inr ⟨R₀, R₁, hR₀card, hR₁cyc, hdisjR, hcentR⟩

private theorem CFSG.section10_sylow_narrow_of_mem_alpha_not_mem_beta
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) (hpβ : p ∉ section10BetaPrimes M)
    (P : Sylow p.val M) :
    IsNarrowPGroup p.val (P : Subgroup M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hnotIdeal : ¬ section10IdealPrime p G := by
    intro hpIdeal
    exact hpβ ⟨hpα, hpIdeal⟩
  have hrankG : 2 < primeRank p.val G :=
    hpα.2.trans_le (section8_primeRank_le_of_subgroup (G := G) M p.val)
  obtain ⟨S₀, hS₀narrow⟩ :
      ∃ S : Sylow p.val G, IsNarrowPGroup p.val (S : Subgroup G) := by
    by_contra hnone
    have hall : ∀ S : Sylow p.val G, ¬ IsNarrowPGroup p.val (S : Subgroup G) := by
      intro S hSnarrow
      exact hnone ⟨S, hSnarrow⟩
    exact hnotIdeal ⟨hrankG, hall⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype)
  obtain ⟨S, hPGS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp
  have hS_eq_PG : (S : Subgroup G) = PG := by
    simpa [PG] using
      section10_sigma_ambient_sylow_eq_of_le_sylow
        (section10_alpha_subset_sigma hM hpα) P S hPGS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  let S₀map : Subgroup G := (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom
  have hS₀map_eq : S₀map = (S : Subgroup G) := by
    change (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup G)
    have hg' := congrArg (fun T : Sylow p.val G => (T : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hg'
    exact hg'
  let eS₀Smap : (S₀ : Subgroup G) ≃* S₀map :=
    Subgroup.equivMapOfInjective
      (f := (MulAut.conj g).toMonoidHom) (S₀ : Subgroup G)
      (EquivLike.injective (MulAut.conj g))
  let eS₀S : (S₀ : Subgroup G) ≃* (S : Subgroup G) :=
    eS₀Smap.trans (MulEquiv.subgroupCongr hS₀map_eq)
  have hSnarrow : IsNarrowPGroup p.val (S : Subgroup G) :=
    section10_isNarrowPGroup_of_equiv eS₀S.symm hS₀narrow
  have hPGnarrow : IsNarrowPGroup p.val PG := by
    rw [← hS_eq_PG]
    exact hSnarrow
  let ePPG : (P : Subgroup M) ≃* PG :=
    Subgroup.equivMapOfInjective
      (f := M.subtype) (P : Subgroup M) M.subtype_injective
  exact section10_isNarrowPGroup_of_equiv ePPG hPGnarrow

public theorem CFSG.section10_sylow_narrow_of_not_mem_beta
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpβ : p ∉ section10BetaPrimes M) (P : Sylow p.val M) :
    IsNarrowPGroup p.val (P : Subgroup M) := by
  by_cases hpα : p ∈ section10AlphaPrimes M
  · exact section10_sylow_narrow_of_mem_alpha_not_mem_beta hM hpα hpβ P
  · exact section10_sylow_narrow_of_not_mem_alpha hpα P

public theorem CFSG.section10_normalPComplements_of_not_mem_beta
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpM : p ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M) :
    HasNormalPComplement p.val (derivedSubgroup M) ∧
      HasNormalPComplement p.val (section10MsigmaSubgroup M) ∧
      IsLargestPrimeDivisor p.val (Nat.card (M ⧸ pPrimeCore p.val M)) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have : Group.IsSolvable M := hMsolv
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hp_dvd_M : p.val ∣ Nat.card M := by
    simpa [subgroupPrimeSet] using hpM
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  have hPnarrow : IsNarrowPGroup p.val (P : Subgroup M) :=
    section10_sylow_narrow_of_not_mem_beta hM hpβ P
  have hplen :
      3 ≤ groupRank (P : Subgroup M) → HasPLengthOne p.val M := by
    intro _hPrank
    exact theorem_10_6 (G := G) (H := M) (p := p) hM.1
  have hcompD : HasNormalPComplement p.val (derivedSubgroup M) :=
    theorem_5_6_c (G := M) (p := p.val) hModd hp_dvd_M (S := P) hPnarrow hplen
  have hcompσ : HasNormalPComplement p.val (section10MsigmaSubgroup M) :=
    hasNormalPComplement_of_le (G := M) (p := p.val)
      (section10_msigmaSubgroup_le_derivedSubgroup hM) hcompD
  have hlargest : IsLargestPrimeDivisor p.val (Nat.card (M ⧸ pPrimeCore p.val M)) := by
    by_cases hPrank_le : groupRank (P : Subgroup M) ≤ 2
    · have hprimeRank_le : primeRank p.val M ≤ 2 :=
        (section10_primeRank_le_groupRank_sylow_pre (G := M) P).trans hPrank_le
      exact theorem_4_18_a (G := M) (p := p.val) hMsolv hModd hp_dvd_M hprimeRank_le
    · have hPrank : 3 ≤ groupRank (P : Subgroup M) := by omega
      exact theorem_5_6_a_high_rank_largest_prime
        (G := M) (p := p.val) hModd hp_dvd_M (S := P) hPnarrow hPrank (hplen hPrank)
  exact ⟨hcompD, hcompσ, hlargest⟩

private theorem CFSG.section10_exists_hall_betaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    ∃ B : Subgroup M, IsHallSubgroup (section10BetaPrimes M) B := by
  classical
  let : MulDistribMulAction PUnit.{1} M := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hcop : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card M) := by simp
  obtain ⟨B, hBHall, _hBinv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := M) (A := PUnit.{1}) hMsolv hcop (section10BetaPrimes M)
  exact ⟨B, hBHall⟩

private theorem CFSG.section10_betaHallSubgroup_le_malphaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {B : Subgroup M}
    (hBHall : IsHallSubgroup (section10BetaPrimes M) B) :
    B ≤ section10MalphaSubgroup M := by
  classical
  let A : Subgroup M := section10MalphaSubgroup M
  let q : M →* M ⧸ A := QuotientGroup.mk' A
  have hBmap_bot : B.map q = ⊥ := by
    by_contra hne
    have hcard_ne_one : Nat.card (B.map q) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := B.map q)).mp hcard)
    obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
    let p : Nat.Primes := ⟨r, hrprime⟩
    have hpB : p ∈ section10BetaPrimes M :=
      hBHall.p_in_pi_of_p_dvd_card p
        (hrdvd.trans (card_map_dvd_card (f := q) (H := B)))
    have hpα : p ∈ section10AlphaPrimes M :=
      section10_beta_subset_alpha (G := G) M hpB
    have hp_dvd_quot : p.val ∣ Nat.card (M ⧸ A) :=
      hrdvd.trans (Subgroup.card_subgroup_dvd_card (B.map q))
    exact ((section10_malphaSubgroup_isHall hM).p_in_pi_of_p_dvd_index p
      (by simp [A, Subgroup.index_eq_card, hp_dvd_quot])) hpα
  have hB_le_ker : B ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := B) (f := q)).mp hBmap_bot
  have hker_eq : q.ker = A := by
    simp [q]
  rwa [hker_eq] at hB_le_ker

private theorem CFSG.section10_betaHallSubgroup_le_derivedSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {B : Subgroup M}
    (hBHall : IsHallSubgroup (section10BetaPrimes M) B) :
    B ≤ derivedSubgroup M :=
  (section10_betaHallSubgroup_le_malphaSubgroup hM hBHall).trans <|
    (section10_malphaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)

public theorem CFSG.section10_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {B : Subgroup H} (hcomp : HasNormalPComplement p H)
    (hpB : ¬ p ∣ Nat.card B) :
    B ≤ pPrimeCore p H := by
  classical
  let q : H →* H ⧸ pPrimeCore p H := QuotientGroup.mk' (pPrimeCore p H)
  have hquotp : IsPGroup p (H ⧸ pPrimeCore p H) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hcomp
  have hBmap_bot : B.map q = ⊥ := by
    by_contra hne
    have hcard_ne_one : Nat.card (B.map q) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := B.map q)).mp hcard)
    have hBmap_p : IsPGroup p (B.map q) :=
      hquotp.to_subgroup (B.map q)
    obtain ⟨n, hcard⟩ := hBmap_p.exists_card_eq
    have hp_dvd_map : p ∣ Nat.card (B.map q) := by
      cases n with
      | zero =>
          exfalso
          exact hcard_ne_one (by simpa [hcard])
      | succ n =>
          refine ⟨p ^ n, ?_⟩
          calc
            Nat.card (B.map q) = p ^ (n + 1) := hcard
            _ = p ^ n * p := by rw [pow_succ]
            _ = p * p ^ n := Nat.mul_comm _ _
    exact hpB (hp_dvd_map.trans (card_map_dvd_card (f := q) (H := B)))
  have hB_le_ker : B ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := B) (f := q)).mp hBmap_bot
  have hker_eq : q.ker = pPrimeCore p H := by
    simp [q]
  rwa [hker_eq] at hB_le_ker

private theorem CFSG.section10_betaHallSubgroup_subgroupOf_derived_le_pPrimeCore
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpM : p ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M)
    {B : Subgroup M} (hBHall : IsHallSubgroup (section10BetaPrimes M) B) :
    B.subgroupOf (derivedSubgroup M) ≤ pPrimeCore p.val (derivedSubgroup M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hBD : B ≤ derivedSubgroup M :=
    section10_betaHallSubgroup_le_derivedSubgroup hM hBHall
  have hcompD : HasNormalPComplement p.val (derivedSubgroup M) :=
    (section10_normalPComplements_of_not_mem_beta hM hpM hpβ).1
  have hp_not_dvd_BD : ¬ p.val ∣ Nat.card (B.subgroupOf (derivedSubgroup M)) := by
    intro hp_dvd
    have hcard_eq :
        Nat.card (B.subgroupOf (derivedSubgroup M)) = Nat.card B := by
      simpa using
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := B) (K := derivedSubgroup M) hBD).toEquiv
    have hp_dvd_B : p.val ∣ Nat.card B := by
      rwa [hcard_eq] at hp_dvd
    exact hpβ (hBHall.p_in_pi_of_p_dvd_card p hp_dvd_B)
  exact section10_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
    (H := derivedSubgroup M) (p := p.val) hcompD hp_not_dvd_BD

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section10_iInf_pPrimeCore_characteristic
    {H : Type*} [Group H] (S : Set Nat.Primes) :
    (⨅ p : {p : Nat.Primes // p ∈ S}, pPrimeCore p.val H).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  rw [Subgroup.mem_iInf] at hy ⊢
  intro p
  have hy_p : (y : H) ∈ pPrimeCore p.val H := hy p
  have hmap :
      φ y ∈ (pPrimeCore p.val H).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hy_p, rfl⟩
  have hfixed :
      (pPrimeCore p.val H).map φ.toMonoidHom = pPrimeCore p.val H :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (pPrimeCore p.val H).Characteristic) φ
  rw [hfixed] at hmap
  exact hmap

omit [IsMinCE G] in
private theorem CFSG.section10_betaCoreIntersection_isPiSubgroup
    {M : Subgroup G} :
    IsPiSubgroup (G := derivedSubgroup M) (section10BetaPrimes M)
      (⨅ p : {p : Nat.Primes // p ∈ subgroupPrimeSet M ∧
          p ∉ section10BetaPrimes M}, pPrimeCore p.val (derivedSubgroup M)) := by
  classical
  let D : Subgroup M := derivedSubgroup M
  let I : Type := {p : Nat.Primes // p ∈ subgroupPrimeSet M ∧
    p ∉ section10BetaPrimes M}
  let C : Subgroup D := ⨅ p : I, pPrimeCore p.val D
  intro q hqC
  have hqD : q.val ∣ Nat.card D :=
    hqC.trans (Subgroup.card_subgroup_dvd_card C)
  have hqM : q.val ∣ Nat.card M :=
    hqD.trans (Subgroup.card_subgroup_dvd_card D)
  have hqMmem : q ∈ subgroupPrimeSet M := by
    simpa [subgroupPrimeSet] using hqM
  by_contra hqβ
  let iq : I := ⟨q, hqMmem, hqβ⟩
  have hC_le_core : C ≤ pPrimeCore q.val D := by
    simpa [C, I, iq] using
      (iInf_le (fun p : I => pPrimeCore p.val D) iq)
  have hq_core : q.val ∣ Nat.card (pPrimeCore q.val D) :=
    hqC.trans (Subgroup.card_dvd_of_le hC_le_core)
  have : Fact q.val.Prime := ⟨q.property⟩
  exact ((q.property.coprime_iff_not_dvd).1
    (pPrimeCore_coprime_card (G := D) (p := q.val))) hq_core

private theorem CFSG.section10_betaHallSubgroup_le_mbetaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {B : Subgroup M} (hBHall : IsHallSubgroup (section10BetaPrimes M) B) :
    B ≤ section10MbetaSubgroup M := by
  classical
  let D : Subgroup M := derivedSubgroup M
  let I : Type := {p : Nat.Primes // p ∈ subgroupPrimeSet M ∧
    p ∉ section10BetaPrimes M}
  let C : Subgroup D := ⨅ p : I, pPrimeCore p.val D
  have hBD : B ≤ D :=
    section10_betaHallSubgroup_le_derivedSubgroup hM hBHall
  have hBsub_le_C : B.subgroupOf D ≤ C := by
    intro x hx
    rw [Subgroup.mem_iInf]
    intro p
    exact section10_betaHallSubgroup_subgroupOf_derived_le_pPrimeCore hM
      p.property.1 p.property.2 hBHall hx
  have hCchar : C.Characteristic := by
    simpa [C, I] using
      section10_iInf_pPrimeCore_characteristic
        (H := D) {p : Nat.Primes | p ∈ subgroupPrimeSet M ∧
          p ∉ section10BetaPrimes M}
  have hCπ : IsPiSubgroup (G := D) (section10BetaPrimes M) C := by
    change IsPiSubgroup (G := derivedSubgroup M) (section10BetaPrimes M)
      (⨅ p : {p : Nat.Primes // p ∈ subgroupPrimeSet M ∧
          p ∉ section10BetaPrimes M}, pPrimeCore p.val (derivedSubgroup M))
    exact section10_betaCoreIntersection_isPiSubgroup (G := G) (M := M)
  have hCmapπ : IsPiSubgroup (G := M) (section10BetaPrimes M) (C.map D.subtype) :=
    by
      intro p hp_dvd
      exact hCπ p (hp_dvd.trans (Subgroup.card_map_dvd (H := C) D.subtype))
  have : D.Normal := by
    dsimp [D]
    infer_instance
  let : C.Characteristic := hCchar
  have hCmap_normal : (C.map D.subtype).Normal := by
    infer_instance
  let : (C.map D.subtype).Normal := hCmap_normal
  have hCmap_le_K : C.map D.subtype ≤ section10MbetaSubgroup M := by
    simpa [section10MbetaSubgroup] using
      le_piCore_of_normal_isPiSubgroup (G := M) (section10BetaPrimes M)
        (C.map D.subtype) hCmapπ
  intro b hbB
  have hbD : b ∈ D := hBD hbB
  let bD : D := ⟨b, hbD⟩
  have hbD_B : bD ∈ B.subgroupOf D := by
    exact hbB
  have hbD_C : bD ∈ C := hBsub_le_C hbD_B
  have hb_map : (b : M) ∈ C.map D.subtype :=
    Subgroup.mem_map.mpr ⟨bD, hbD_C, rfl⟩
  exact hCmap_le_K hb_map

public theorem CFSG.section10_mbetaSubgroup_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10BetaPrimes M) (section10MbetaSubgroup M) := by
  classical
  let π : Set Nat.Primes := section10BetaPrimes M
  let K : Subgroup M := section10MbetaSubgroup M
  obtain ⟨B, hBHall⟩ := section10_exists_hall_betaSubgroup hM
  have hB_le_K : B ≤ K :=
    section10_betaHallSubgroup_le_mbetaSubgroup hM hBHall
  refine isHallSubgroup_of (G := M) (π := π) (H := K) ?_ ?_
  · intro p hp_dvd
    simpa [K, π, section10MbetaSubgroup] using
      (piCore_isPiSubgroup (G := M) π p hp_dvd)
  · intro p hpβ hp_dvd_index
    have hidx_dvd : K.index ∣ B.index := Subgroup.index_dvd_of_le hB_le_K
    exact (hBHall.p_in_pi_of_p_dvd_index p (hp_dvd_index.trans hidx_dvd))
      (by simpa [π] using hpβ)

/-- Lemma 10.8(a). -/
public theorem CFSG.lemma_10_8_a
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10BetaPrimes M) (section10Mbeta M) ∧
      IsHallSubgroup (section10BetaPrimes M) (section10MbetaSubgroup M) := by
  have hKHall : IsHallSubgroup (section10BetaPrimes M) (section10MbetaSubgroup M) :=
    section10_mbetaSubgroup_isHall hM
  exact ⟨section10_mbeta_isHall_of_mbetaSubgroup_isHall hM hKHall, hKHall⟩
