module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_2_e
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.3 from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_malpha_le_maximal
    {M : Subgroup G} :
    section10Malpha M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_centralizerIn_malpha_le_centralizerIn_maximal
    {M X : Subgroup G} :
    subgroupCentralizerIn (section10Malpha M) X ≤ subgroupCentralizerIn M X := by
  intro x hx
  exact ⟨section10_malpha_le_maximal hx.1, hx.2⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_subgroupCentralizerIn_maximal_proper
    {M X : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    subgroupCentralizerIn M X ≠ ⊤ := by
  intro htop
  have hC_le_M : subgroupCentralizerIn M X ≤ M := inf_le_left
  have htop_le_M : (⊤ : Subgroup G) ≤ M := by
    simpa [htop] using hC_le_M
  exact hM.1 (eq_top_iff.2 htop_le_M)

omit [IsMinCE G] in
public theorem CFSG.section10_groupRank_le_of_le
    {A B : Subgroup G} (hAB : A ≤ B) :
    groupRank A ≤ groupRank B := by
  let A' : Subgroup B := A.subgroupOf B
  let e : A' ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := B) hAB
  exact
    (section10_groupRank_le_of_equiv_pre (R := A') (S := A) e).trans
      (section8_groupRank_le_of_subgroup A')

private theorem CFSG.section10_lemma_10_3_rank_ge_three
    {M X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hlarge : 3 ≤ groupRank (subgroupCentralizerIn (section10Malpha M) X)) :
    subgroupCentralizerIn M X ∈ section9UniqueSubgroups G := by
  have hrank_le :
      groupRank (subgroupCentralizerIn (section10Malpha M) X) ≤
        groupRank (subgroupCentralizerIn M X) :=
    section10_groupRank_le_of_le section10_centralizerIn_malpha_le_centralizerIn_maximal
  have hCM_large : 3 ≤ groupRank (subgroupCentralizerIn M X) := hlarge.trans hrank_le
  exact theorem_9_6
    (K := subgroupCentralizerIn M X)
    (section10_subgroupCentralizerIn_maximal_proper hM)
    (by omega) (Or.inl hCM_large)

omit [IsMinCE G] in
private theorem CFSG.section10_exists_prime_rank_two_in_centralizer_of_rank_two
    {M X : Subgroup G}
    (hcentRank : 1 < groupRank (subgroupCentralizerIn (section10Malpha M) X))
    (hcentRank_le_two :
      groupRank (subgroupCentralizerIn (section10Malpha M) X) ≤ 2) :
    ∃ p : Nat.Primes, ∃ A : Subgroup (subgroupCentralizerIn (section10Malpha M) X),
      IsPGroup p.val A ∧ IsMulCommutative A ∧ 2 ≤ generatorRank A := by
  have htwo : 2 ≤ groupRank (subgroupCentralizerIn (section10Malpha M) X) := by
    omega
  exact section10_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank_pre htwo

omit [IsMinCE G] in
public theorem CFSG.section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank_pre
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R] {B : Subgroup R}
    (hBp : IsPGroup p B) (hBgen : 2 ≤ generatorRank B) :
    p ∣ Nat.card R := by
  have hBnoncyc : ¬ IsCyclic B := by
    intro hcyc
    have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hcyc
    omega
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

private theorem CFSG.section10_prime_mem_alpha_of_rank_two_centralizer_witness
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    {A : Subgroup (subgroupCentralizerIn (section10Malpha M) X)}
    (hAp : IsPGroup p.val A) (hAgen : 2 ≤ generatorRank A) :
    p ∈ section10AlphaPrimes M := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpC :
      p.val ∣ Nat.card (subgroupCentralizerIn (section10Malpha M) X) :=
    section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank_pre hAp hAgen
  have hC_le_malpha :
      subgroupCentralizerIn (section10Malpha M) X ≤ section10Malpha M := inf_le_left
  have hpMalpha : p.val ∣ Nat.card (section10Malpha M) :=
    hpC.trans (Subgroup.card_dvd_of_le hC_le_malpha)
  exact (section10_malpha_isHall hM).p_in_pi_of_p_dvd_card p hpMalpha

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_malpha_eq_piCoreIn (M : Subgroup G) :
    section10Malpha M = piCoreIn (section10AlphaPrimes M) M := by
  rfl

omit [IsMinCE G] in
private theorem CFSG.section10_le_normalizer_malpha_of_le_maximal
    {M X : Subgroup G} (hXle : X ≤ M) :
    X ≤ Subgroup.normalizer (section10Malpha M : Set G) := by
  rw [section10_malpha_eq_piCoreIn]
  exact section8_le_normalizer_piCoreIn_of_le_normalizer
    (G := G) (π := section10AlphaPrimes M) (H := M) (P := X)
    (hXle.trans Subgroup.le_normalizer)

private theorem CFSG.section10_coprime_card_of_isPiSubgroup_compl_malpha
    {M X : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hXpi : IsPiSubgroup (section10AlphaPrimes M)ᶜ X) :
    Nat.Coprime (Nat.card X) (Nat.card (section10Malpha M)) := by
  have hXπgroup : IsPiGroup (section10AlphaPrimes M)ᶜ X :=
    IsPiSubgroup.isPiGroup (H := X) hXpi
  have hMαπ : IsPiSubgroup (G := G) (section10AlphaPrimes M) (section10Malpha M) :=
    (section10_malpha_isHall hM).p_in_pi_of_p_dvd_card
  have hMαπgroup : IsPiGroup (section10AlphaPrimes M) (section10Malpha M) :=
    IsPiSubgroup.isPiGroup (H := section10Malpha M) hMαπ
  rw [IsPiGroup_iff] at hXπgroup hMαπgroup
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqX hqMα
  let q' : Nat.Primes := ⟨q, hqprime⟩
  exact (hXπgroup q' hqX) (hMαπgroup q' hqMα)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_centralizer_witness_image_isInvariant
    {M X : Subgroup G} [Subgroup.Normalizes X (section10Malpha M)]
    (A : Subgroup (subgroupCentralizerIn (section10Malpha M) X)) :
    let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
    let ι : C →* section10Malpha M := Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
    IsInvariant X (section10Malpha M) (A.map ι) := by
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
  let ι : C →* section10Malpha M := Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
  change IsInvariant X (section10Malpha M) (A.map ι)
  have hforward :
      ∀ x : X, ∀ y : section10Malpha M, y ∈ A.map ι → x • y ∈ A.map ι := by
    intro x y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, haA, rfl⟩
    have hfixed : x • (ι a) = ι a := by
      apply Subtype.ext
      have hιa : ((ι a : section10Malpha M) : G) = ((a : C) : G) := by
        rfl
      have hcomm :
          (x : G) * ((a : C) : G) = ((a : C) : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp (a : C).property.2) (x : G) x.property
      calc
        ((x • (ι a) : section10Malpha M) : G) =
            (x : G) * ((ι a : section10Malpha M) : G) * (x : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = (x : G) * ((a : C) : G) * (x : G)⁻¹ := by rw [hιa]
        _ = ((a : C) : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = ((ι a : section10Malpha M) : G) := by rw [hιa]; simp [mul_assoc]
    exact Subgroup.mem_map.mpr ⟨a, haA, hfixed.symm⟩
  refine ⟨?_⟩
  intro x y
  constructor
  · exact hforward x y
  · intro hy
    have hback := hforward x⁻¹ (x • y) hy
    simpa [← mul_smul] using hback

private theorem CFSG.section10_exists_invariant_sylow_malpha_containing_witness
    {M X : Subgroup G} [Subgroup.Normalizes X (section10Malpha M)]
    (hM : M ∈ section9MaximalSubgroups G)
    (hXpi : IsPiSubgroup (section10AlphaPrimes M)ᶜ X) {p : Nat.Primes}
    (A : Subgroup (subgroupCentralizerIn (section10Malpha M) X))
    (hAp : IsPGroup p.val A) :
    ∃ P : Sylow p.val (section10Malpha M),
      IsInvariant X (section10Malpha M) (P : Subgroup (section10Malpha M)) ∧
        A.map (Subgroup.inclusion
          (show subgroupCentralizerIn (section10Malpha M) X ≤ section10Malpha M by
            exact inf_le_left)) ≤ (P : Subgroup (section10Malpha M)) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
  let ι : C →* section10Malpha M :=
    Subgroup.inclusion (show C ≤ section10Malpha M by exact inf_le_left)
  let Aα : Subgroup (section10Malpha M) := A.map ι
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hAαp : IsPGroup p.val Aα := by
    simpa [Aα] using IsPGroup.map (p := p.val) (H := A) hAp ι
  have hAαπ : IsPiSubgroup (G := section10Malpha M) ({p} : Set Nat.Primes) Aα :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := section10Malpha M)
      (H := Aα) (q := p) hAαp
  have hAαinv : IsInvariant X (section10Malpha M) Aα := by
    simpa [Aα, C, ι] using
      section10_centralizer_witness_image_isInvariant (G := G) (M := M) (X := X) A
  have hMαproper : section10Malpha M ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [htop] using (section10_malpha_le_maximal (G := G) (M := M))
    exact hM.1 (eq_top_iff.2 htop_le_M)
  have hMαsolv : IsSolvable (section10Malpha M) :=
    IsMinCE.proper_subgroups_solvable (section10Malpha M) (lt_top_iff_ne_top.2 hMαproper)
  have hcop_X_malpha :
      Nat.Coprime (Nat.card X) (Nat.card (section10Malpha M)) :=
    section10_coprime_card_of_isPiSubgroup_compl_malpha
      (G := G) (M := M) (X := X) hM hXpi
  obtain ⟨H, hHHall, hHinv, hAαH⟩ :=
    proposition_1_5_b (G := section10Malpha M) (A := X)
      hMαsolv hcop_X_malpha ({p} : Set Nat.Primes) Aα hAαπ hAαinv
  have hHπ : IsPiSubgroup (G := section10Malpha M) ({p} : Set Nat.Primes) H :=
    hHHall.p_in_pi_of_p_dvd_card
  have hHp : IsPGroup p.val H :=
    section8_isPGroup_of_isPiSubgroup_singleton (G := section10Malpha M)
      (H := H) (q := p) hHπ
  have hp_not_dvd_index : ¬ p.val ∣ H.index := by
    intro hpidx
    exact (hHHall.p_in_pi_of_p_dvd_index p hpidx) (by simp)
  let P : Sylow p.val (section10Malpha M) := hHp.toSylow hp_not_dvd_index
  refine ⟨P, ?_, ?_⟩
  · simpa [P] using hHinv
  · simpa [P, Aα, C, ι] using hAαH

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_isElementaryAbelian_map_early
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

private theorem CFSG.section10_exists_rank_two_elementary_in_centralizer_witness
    {M X : Subgroup G} {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M)
    {A : Subgroup (subgroupCentralizerIn (section10Malpha M) X)}
    (hAp : IsPGroup p.val A) (hAgen : 2 ≤ generatorRank A) :
    ∃ E : Subgroup (subgroupCentralizerIn (section10Malpha M) X),
      E ≤ A ∧ Nat.card E = p.val ^ 2 ∧ IsElementaryAbelian p.val E := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hA_noncyc : ¬ IsCyclic A := by
    intro hcyc
    have hle : generatorRank A ≤ 1 := generatorRank_le_one_of_isCyclic (G := A) hcyc
    omega
  have hp_dvd_G : p.val ∣ Nat.card G := by
    exact hpα.1.trans (Subgroup.card_subgroup_dvd_card M)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Fact (IsPGroup p.val A) := ⟨hAp⟩
  obtain ⟨E0, _hE0norm, hE0card, hE0elem⟩ :=
    lemma_4_5_a (R := A) (p := p.val) hpodd hA_noncyc
  let E : Subgroup (subgroupCentralizerIn (section10Malpha M) X) := E0.map A.subtype
  have hE_le_A : E ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hEcard : Nat.card E = p.val ^ 2 := by
    calc
      Nat.card E = Nat.card E0 := by
        exact Subgroup.card_map_of_injective
          (K := E0) (f := A.subtype) A.subtype_injective
      _ = p.val ^ 2 := hE0card
  have hEelem : IsElementaryAbelian p.val E := by
    letI : IsElementaryAbelian p.val E0 := hE0elem
    simpa [E] using
      section10_isElementaryAbelian_map_early
        (G := A) (p := p.val) (A := E0)
        (G' := subgroupCentralizerIn (section10Malpha M) X) A.subtype
  exact ⟨E, hE_le_A, hEcard, hEelem⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_exists_maximal_elementaryAbelianSubgroup_containing_pre
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R] {E : Subgroup R}
    (hEelem : IsElementaryAbelian p E) :
    ∃ B : Subgroup R, E ≤ B ∧ B ∈ maximalElementaryAbelianSubgroups p R := by
  classical
  let s : Set (Subgroup R) := {A | E ≤ A ∧ IsElementaryAbelian p A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨E, le_rfl, hEelem⟩
  obtain ⟨B, hBmax⟩ := hsfin.exists_maximal hsne
  refine ⟨B, hBmax.1.1, ?_⟩
  refine ⟨hBmax.1.2, ?_⟩
  intro C hBC hCelem
  exact le_antisymm hBC (hBmax.2 ⟨hBmax.1.1.trans hBC, hCelem⟩ hBC)

omit [IsMinCE G] in
public theorem CFSG.section10_groupRank_at_least_two_of_elementaryAbelian_subgroup_card_p_sq_early
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {A K : Subgroup R} (hAK : A ≤ K)
    (hAcard : Nat.card A = p ^ 2) (hAelem : IsElementaryAbelian p A) :
    2 ≤ groupRank K := by
  haveI : IsElementaryAbelian p A := hAelem
  have hAgen : 2 ≤ generatorRank A := by
    letI : CommGroup A := IsMulCommutative.instCommGroup
    have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
      simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
    rw [hAcard] at hcard_dvd
    have hle_rank : 2 ≤ Group.rank A := by
      exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp
        hcard_dvd
    simpa [generatorRank_eq_group_rank] using hle_rank
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hAcomm : IsMulCommutative A := inferInstance
  exact hAgen.trans
    (section10_generatorRank_le_groupRank_of_subgroup_pre
      (G := R) (q := p) (Fact.out : Nat.Prime p) hAK hAp hAcomm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq_early
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hgt : p ^ 2 < Nat.card A) :
    3 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  have hnot_le_two : ¬ Group.rank A ≤ 2 := by
    intro hle_two
    have hcard_le : Nat.card A ≤ p ^ Group.rank A :=
      Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hcard_dvd
    have hpow_le : p ^ Group.rank A ≤ p ^ 2 :=
      Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hle_two
    exact (not_lt_of_ge (hcard_le.trans hpow_le)) hgt
  have hle_rank : 3 ≤ Group.rank A := by omega
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [IsMinCE G] in
private theorem CFSG.section10_groupRank_at_least_three_of_elementaryAbelian_subgroup_card_gt_p_sq_early
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {A K : Subgroup R} (hAK : A ≤ K)
    (hAcard : p ^ 2 < Nat.card A) (hAelem : IsElementaryAbelian p A) :
    3 ≤ groupRank K := by
  haveI : IsElementaryAbelian p A := hAelem
  have hAgen : 3 ≤ generatorRank A :=
    section10_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq_early
      (p := p) (A := A) hAcard
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hAcomm : IsMulCommutative A := inferInstance
  exact hAgen.trans
    (section10_generatorRank_le_groupRank_of_subgroup_pre
      (G := R) (q := p) (Fact.out : Nat.Prime p) hAK hAp hAcomm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_of_prime_card_isCyclic_early
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hcard : Nat.card H = p) :
    IsElementaryAbelian p H := by
  letI : CommGroup H := IsCyclic.commGroup
  refine
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  exact orderOf_dvd_iff_pow_eq_one.mp <| by
    simpa [hcard] using (orderOf_dvd_natCard x)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_sup_of_le_centralizer_early
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H]
    {E C : Subgroup H}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set H)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  let s : Set H := (E : Set H) ∪ (C : Set H)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : H) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : H)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          have hclosure_comm : IsMulCommutative ↥(Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
          show y * z = z * y
          simpa using congrArg Subtype.val
            (hclosure_comm.is_comm.comm
              (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

private theorem CFSG.section10_centralizer_rank_le_two_of_not_unique_image
    {R : Type*} [Group R] [Finite R] {K : Subgroup G}
    (hKproper : K ≠ ⊤) (hKrank : 2 ≤ groupRank K)
    (hKnot : K ∉ section9UniqueSubgroups G)
    {B : Subgroup R} (f : R →* G) (hf : Function.Injective f)
    (hBmap : B.map f = K) :
    groupRank (Subgroup.centralizer (B : Set R)) ≤ 2 := by
  classical
  by_contra hle
  have hCrank : 3 ≤ groupRank (Subgroup.centralizer (B : Set R)) := by omega
  let C_R : Subgroup R := Subgroup.centralizer (B : Set R)
  let C_G : Subgroup G := C_R.map f
  let e : C_R ≃* C_G := Subgroup.equivMapOfInjective C_R f hf
  have hC_G_rank : 3 ≤ groupRank C_G := by
    exact hCrank.trans
      (section10_groupRank_le_of_equiv_pre (R := C_G) (S := C_R) e.symm)
  have hC_G_le : C_G ≤ Subgroup.centralizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rcases Subgroup.mem_map.mp hy with ⟨r, hrC, rfl⟩
    have hk' : k ∈ B.map f := by simpa [hBmap] using hk
    rcases Subgroup.mem_map.mp hk' with ⟨b, hbB, rfl⟩
    simpa using congrArg f ((Subgroup.mem_centralizer_iff.mp hrC) b hbB)
  have hcentralizer_large : 3 ≤ groupRank (Subgroup.centralizer (K : Set G)) :=
    hC_G_rank.trans (section10_groupRank_le_of_le hC_G_le)
  exact hKnot (theorem_9_6 (K := K) hKproper hKrank (Or.inr hcentralizer_large))

omit [IsMinCE G] in
private theorem CFSG.section10_orderOf_mem_of_centralizer_rank_le_two_early
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {B : Subgroup R} (hBcard : Nat.card B = p ^ 2)
    (hBelem : IsElementaryAbelian p B)
    (hCrank : groupRank (Subgroup.centralizer (B : Set R)) ≤ 2)
    {g : R} (hgcent : g ∈ Subgroup.centralizer (B : Set R))
    (hgord : orderOf g = p) :
    g ∈ B := by
  classical
  by_contra hgB
  let Z : Subgroup R := Subgroup.zpowers g
  have hZcard : Nat.card Z = p := by
    simp [Z, hgord]
  have hZelem : IsElementaryAbelian p Z := by
    have hZcyc : IsCyclic Z := Subgroup.isCyclic_zpowers g
    letI : IsCyclic Z := hZcyc
    exact section10_isElementaryAbelian_of_prime_card_isCyclic_early (p := p) hZcard
  have hZ_le_cent : Z ≤ Subgroup.centralizer (B : Set R) := by
    exact (Subgroup.zpowers_le).2 hgcent
  let S : Subgroup R := B ⊔ Z
  have hSelem : IsElementaryAbelian p S := by
    letI : IsElementaryAbelian p B := hBelem
    letI : IsElementaryAbelian p Z := hZelem
    simpa [S] using
      section10_isElementaryAbelian_sup_of_le_centralizer_early
        (p := p) (E := B) (C := Z) hZ_le_cent
  have hB_lt_S : B < S := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hBS
    have hgS : g ∈ S := by
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
    exact hgB (by simpa [hBS] using hgS)
  have hS_card_gt : p ^ 2 < Nat.card S := by
    simpa [hBcard] using natCard_lt_of_subgroup_lt hB_lt_S
  have hS_le_C : S ≤ Subgroup.centralizer (B : Set R) := by
    have hB_le_cent : B ≤ Subgroup.centralizer (B : Set R) := by
      letI : IsElementaryAbelian p B := hBelem
      exact Subgroup.le_centralizer (H := B)
    exact sup_le hB_le_cent hZ_le_cent
  have hC_large : 3 ≤ groupRank (Subgroup.centralizer (B : Set R)) :=
    section10_groupRank_at_least_three_of_elementaryAbelian_subgroup_card_gt_p_sq_early
      (p := p) (A := S) (K := Subgroup.centralizer (B : Set R)) hS_le_C hS_card_gt hSelem
  exact (not_le_of_gt hC_large) hCrank

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_pSubgroup_le_normal_hall_of_mem_early
    {π : Set Nat.Primes} {R : Type*} [Group R] [Finite R]
    {H P : Subgroup R} [H.Normal] {p : ℕ} [Fact p.Prime]
    (hPp : IsPGroup p P) (hHall : IsHallSubgroup π H)
    (hpπ : (⟨p, Fact.out⟩ : Nat.Primes) ∈ π) :
    P ≤ H := by
  classical
  let q : R →* R ⧸ H := QuotientGroup.mk' H
  let Pbar : Subgroup (R ⧸ H) := P.map q
  have hPbarp : IsPGroup p Pbar := by
    simpa [Pbar] using IsPGroup.map (p := p) (H := P) hPp q
  have hPbar_card : Nat.card Pbar = 1 := by
    rcases hPbarp.card_eq_or_dvd with hcard | hpdiv
    · exact hcard
    · have hpidx : p ∣ H.index := by
        have hdivq : Nat.card Pbar ∣ Nat.card (R ⧸ H) :=
          Subgroup.card_subgroup_dvd_card Pbar
        exact hpdiv.trans (by simpa [Subgroup.index_eq_card] using hdivq)
      exact False.elim ((hHall.p_in_pi_of_p_dvd_index ⟨p, Fact.out⟩ hpidx) hpπ)
  have hPbar_bot : Pbar = ⊥ := (Subgroup.card_eq_one (H := Pbar)).1 hPbar_card
  have hP_le_ker : P ≤ q.ker := (Subgroup.map_eq_bot_iff (H := P)).1 hPbar_bot
  intro x hx
  have hxker : x ∈ q.ker := hP_le_ker hx
  simpa [q] using hxker

public theorem CFSG.section10_malpha_sylow_groupRank_ge_three_of_mem_alpha_early
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M)
    (P : Sylow p.val (section10Malpha M)) :
    3 ≤ groupRank (P : Subgroup (section10Malpha M)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hprankM : 3 ≤ primeRank p.val M := Nat.succ_le_of_lt hpα.2
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank_pre
      (p := p.val) (R := M) hprankM
  have hA_le_K : A ≤ section10MalphaSubgroup M := by
    letI : (section10MalphaSubgroup M).Normal := inferInstance
    exact section10_pSubgroup_le_normal_hall_of_mem_early
      (R := M) (π := section10AlphaPrimes M) (H := section10MalphaSubgroup M)
      (P := A) hAp (section10_malphaSubgroup_isHall hM) hpα
  let AG : Subgroup G := A.map M.subtype
  have hAG_le_malpha : AG ≤ section10Malpha M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, hA_le_K haA, rfl⟩
  let Aα : Subgroup (section10Malpha M) := AG.subgroupOf (section10Malpha M)
  have hAGp : IsPGroup p.val AG := by
    simpa [AG] using IsPGroup.map (p := p.val) (H := A) hAp M.subtype
  have hAαp : IsPGroup p.val Aα := by
    exact hAGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Malpha M) hAG_le_malpha).symm
  have hAGcomm : IsMulCommutative AG := by
    letI : IsMulCommutative A := hAcomm
    simpa [AG] using Subgroup.map_isMulCommutative (f := M.subtype) (H := A)
  have hAαcomm : IsMulCommutative Aα := by
    letI : IsMulCommutative AG := hAGcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := AG) (K := section10Malpha M)
  have hAG_gen_eq : generatorRank AG = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.equivMapOfInjective (f := M.subtype) A M.subtype_injective).symm
  have hAα_gen_eq : generatorRank Aα = generatorRank AG := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Malpha M) hAG_le_malpha)
  have hAαgen : 3 ≤ generatorRank Aα := by
    simpa [hAα_gen_eq, hAG_gen_eq] using hAgen
  have hprimeRank_malpha : 3 ≤ primeRank p.val (section10Malpha M) := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card (section10Malpha M), ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
    · exact ⟨Aα, hAαp, hAαcomm, hAαgen⟩
  exact hprimeRank_malpha.trans
    (section10_primeRank_le_groupRank_sylow_pre (G := section10Malpha M) P)

private theorem CFSG.section10_lemma_10_3_rank_two_core
    {M X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hXle : X ≤ M)
    (hXpi : IsPiSubgroup (section10AlphaPrimes M)ᶜ X)
    (hcentRank : 1 < groupRank (subgroupCentralizerIn (section10Malpha M) X))
    (hcentRank_le_two :
      groupRank (subgroupCentralizerIn (section10Malpha M) X) ≤ 2) :
    subgroupCentralizerIn M X ∈ section9UniqueSubgroups G := by
  classical
  obtain ⟨p, A, hAp, _hAcomm, hAgen⟩ :=
    section10_exists_prime_rank_two_in_centralizer_of_rank_two
      (M := M) (X := X) hcentRank hcentRank_le_two
  have hpα : p ∈ section10AlphaPrimes M :=
    section10_prime_mem_alpha_of_rank_two_centralizer_witness
      (G := G) (M := M) (X := X) (p := p) hM hAp hAgen
  haveI : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨E, hE_le_A, hEcard, hEelem⟩ :=
    section10_exists_rank_two_elementary_in_centralizer_witness
      (G := G) (M := M) (X := X) (p := p) hpα hAp hAgen
  obtain ⟨B, hE_le_B, hBmax⟩ :=
    section10_exists_maximal_elementaryAbelianSubgroup_containing_pre
      (p := p.val) (R := subgroupCentralizerIn (section10Malpha M) X) hEelem
  have hBelem : IsElementaryAbelian p.val B := hBmax.1
  have hBp : IsPGroup p.val B := by
    letI : IsElementaryAbelian p.val B := hBelem
    exact IsElementaryAbelian.isPGroup p.val B
  have hX_norm_malpha :
      X ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    section10_le_normalizer_malpha_of_le_maximal (G := G) hXle
  have hcop_X_malpha :
      Nat.Coprime (Nat.card X) (Nat.card (section10Malpha M)) :=
    section10_coprime_card_of_isPiSubgroup_compl_malpha
      (G := G) (M := M) (X := X) hM hXpi
  letI : Fact (X ≤ Subgroup.normalizer (section10Malpha M : Set G)) := ⟨hX_norm_malpha⟩
  haveI : Subgroup.Normalizes X (section10Malpha M) := inferInstance
  obtain ⟨P, hPinv, hA_le_P⟩ :=
    section10_exists_invariant_sylow_malpha_containing_witness
      (G := G) (M := M) (X := X) hM hXpi B hBp
  have hCM_rank_two : 2 ≤ groupRank (subgroupCentralizerIn M X) := by
    have htwo : 2 ≤ groupRank (subgroupCentralizerIn (section10Malpha M) X) := by
      omega
    exact htwo.trans
      (section10_groupRank_le_of_le section10_centralizerIn_malpha_le_centralizerIn_maximal)
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) X
  let BG : Subgroup G := B.map C.subtype
  have hBG_le_CM : BG ≤ subgroupCentralizerIn M X := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨b, _hb, rfl⟩
    exact section10_centralizerIn_malpha_le_centralizerIn_maximal b.property
  by_cases hBGunique : BG ∈ section9UniqueSubgroups G
  · exact section9_unique_of_le hBG_le_CM
      (section10_subgroupCentralizerIn_maximal_proper hM) hBGunique
  · have hBG_le_M : BG ≤ M := hBG_le_CM.trans inf_le_left
    have hBGproper : BG ≠ ⊤ := by
      intro htop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [htop] using hBG_le_M
      exact hM.1 (eq_top_iff.2 htop_le_M)
    let EG : Subgroup G := E.map C.subtype
    have hEG_le_BG : EG ≤ BG := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨e, heE, rfl⟩
      exact Subgroup.mem_map.mpr ⟨e, hE_le_B heE, rfl⟩
    have hEGcard : Nat.card EG = p.val ^ 2 := by
      calc
        Nat.card EG = Nat.card E := by
          exact Subgroup.card_map_of_injective
            (K := E) (f := C.subtype) C.subtype_injective
        _ = p.val ^ 2 := hEcard
    have hEGelem : IsElementaryAbelian p.val EG := by
      letI : IsElementaryAbelian p.val E := hEelem
      simpa [EG] using
        section10_isElementaryAbelian_map_early
          (G := C) (p := p.val) (A := E) (G' := G) C.subtype
    have hBGrank : 2 ≤ groupRank BG :=
      section10_groupRank_at_least_two_of_elementaryAbelian_subgroup_card_p_sq_early
        (p := p.val) (A := EG) (K := BG) hEG_le_BG hEGcard hEGelem
    have hBG_rank_le_two : groupRank BG ≤ 2 := by
      by_contra hle
      have hlarge : 3 ≤ groupRank BG := by omega
      exact hBGunique (theorem_9_6 (K := BG) hBGproper hBGrank (Or.inl hlarge))
    have hBGelem : IsElementaryAbelian p.val BG := by
      letI : IsElementaryAbelian p.val B := hBelem
      simpa [BG] using
        section10_isElementaryAbelian_map_early
          (G := C) (p := p.val) (A := B) (G' := G) C.subtype
    have hBGcard_eq : Nat.card BG = Nat.card B := by
      exact Subgroup.card_map_of_injective (K := B) (f := C.subtype) C.subtype_injective
    have hBcard : Nat.card B = p.val ^ 2 := by
      have hBcard_le : Nat.card B ≤ p.val ^ 2 := by
        by_contra hle
        have hgtB : p.val ^ 2 < Nat.card B := by omega
        have hgtBG : p.val ^ 2 < Nat.card BG := by
          simpa [hBGcard_eq] using hgtB
        have hBGlarge : 3 ≤ groupRank BG :=
          section10_groupRank_at_least_three_of_elementaryAbelian_subgroup_card_gt_p_sq_early
            (p := p.val) (A := BG) (K := BG) le_rfl hgtBG hBGelem
        exact (not_le_of_gt hBGlarge) hBG_rank_le_two
      have hEcard_le_B : Nat.card E ≤ Nat.card B := Subgroup.card_le_of_le hE_le_B
      omega
    have hC_le_malpha : C ≤ section10Malpha M := inf_le_left
    let ι : C →* section10Malpha M := Subgroup.inclusion hC_le_malpha
    let Bα : Subgroup (section10Malpha M) := B.map ι
    have hBα_le_P : Bα ≤ (P : Subgroup (section10Malpha M)) := by
      simpa [Bα, ι, C, hC_le_malpha] using hA_le_P
    let BP : Subgroup (P : Subgroup (section10Malpha M)) :=
      Bα.subgroupOf (P : Subgroup (section10Malpha M))
    have hBαcard : Nat.card Bα = p.val ^ 2 := by
      calc
        Nat.card Bα = Nat.card B := by
          exact Subgroup.card_map_of_injective
            (K := B) (f := ι) (Subgroup.inclusion_injective hC_le_malpha)
        _ = p.val ^ 2 := hBcard
    have hBPcard : Nat.card BP = p.val ^ 2 := by
      calc
        Nat.card BP = Nat.card Bα := by
          simpa [BP] using
            natCard_subgroupOf_eq Bα (P : Subgroup (section10Malpha M)) hBα_le_P
        _ = p.val ^ 2 := hBαcard
    have hBαelem : IsElementaryAbelian p.val Bα := by
      letI : IsElementaryAbelian p.val B := hBelem
      simpa [Bα, ι] using
        section10_isElementaryAbelian_map_early
          (G := C) (p := p.val) (A := B) (G' := section10Malpha M) ι
    have hBPelement : IsElementaryAbelian p.val BP := by
      letI : IsElementaryAbelian p.val Bα := hBαelem
      simpa [BP] using
        IsElementaryAbelian.subgroupOf
          (G := section10Malpha M) (p := p.val) (H := Bα)
          (K := (P : Subgroup (section10Malpha M))) hBα_le_P
    let ψ : (P : Subgroup (section10Malpha M)) →* G :=
      (section10Malpha M).subtype.comp (P : Subgroup (section10Malpha M)).subtype
    have hψinj : Function.Injective ψ := by
      intro a b h
      change (((a : (P : Subgroup (section10Malpha M))) :
          section10Malpha M) : G) =
        (((b : (P : Subgroup (section10Malpha M))) :
          section10Malpha M) : G) at h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hBPmap_BG : BP.map ψ = BG := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨bp, hbp, rfl⟩
        have hbpBα : ((bp : (P : Subgroup (section10Malpha M))) :
            section10Malpha M) ∈ Bα := Subgroup.mem_subgroupOf.mp hbp
        rcases Subgroup.mem_map.mp hbpBα with ⟨b, hbB, hb_eq⟩
        exact Subgroup.mem_map.mpr ⟨b, hbB, by
          simpa [ψ, ι] using
            congrArg (fun z : section10Malpha M => (z : G)) hb_eq⟩
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨b, hbB, rfl⟩
        let bα : section10Malpha M := ι b
        have hbαBα : bα ∈ Bα := Subgroup.mem_map.mpr ⟨b, hbB, rfl⟩
        have hbαP : bα ∈ (P : Subgroup (section10Malpha M)) := hBα_le_P hbαBα
        let bp : (P : Subgroup (section10Malpha M)) := ⟨bα, hbαP⟩
        have hbpBP : bp ∈ BP := by
          exact hbαBα
        exact Subgroup.mem_map.mpr ⟨bp, hbpBP, by
          simp [ψ, bp, bα, ι]⟩
    have hCP_rank_le_two :
        groupRank (Subgroup.centralizer
          (BP : Set (P : Subgroup (section10Malpha M)))) ≤ 2 :=
      section10_centralizer_rank_le_two_of_not_unique_image
        (G := G) (R := (P : Subgroup (section10Malpha M))) (K := BG)
        hBGproper hBGrank hBGunique ψ hψinj hBPmap_BG
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hpα.1.trans (Subgroup.card_subgroup_dvd_card M)
    have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
    have hcop_X_P :
        Nat.Coprime (Nat.card X) (Nat.card (P : Subgroup (section10Malpha M))) :=
      hcop_X_malpha.of_dvd_right
        (Subgroup.card_subgroup_dvd_card (P : Subgroup (section10Malpha M)))
    have hBPp : IsPGroup p.val BP := by
      letI : IsElementaryAbelian p.val BP := hBPelement
      exact IsElementaryAbelian.isPGroup p.val BP
    letI : IsInvariant X (section10Malpha M) (P : Subgroup (section10Malpha M)) := hPinv
    have htrivP :
        ActsTrivially (A := X) (G := (P : Subgroup (section10Malpha M))) := by
      letI : Fact (IsPGroup p.val (P : Subgroup (section10Malpha M))) := ⟨P.isPGroup'⟩
      refine corollary_1_12
        (G := (P : Subgroup (section10Malpha M))) (A := X) (p := p.val)
        hpodd BP ?_ hcop_X_P ?_
      · exact ⟨⟨hBPp⟩, hBPelement⟩
      · intro g hgcent hgord x
        have hgBP : g ∈ BP :=
          section10_orderOf_mem_of_centralizer_rank_le_two_early
            (p := p.val) (R := (P : Subgroup (section10Malpha M)))
            (B := BP) hBPcard hBPelement hCP_rank_le_two hgcent hgord
        apply Subtype.ext
        have hgBα : ((g : (P : Subgroup (section10Malpha M))) :
            section10Malpha M) ∈ Bα := Subgroup.mem_subgroupOf.mp hgBP
        rcases Subgroup.mem_map.mp hgBα with ⟨b, _hbB, hb_eq⟩
        apply Subtype.ext
        have hcomm :
            (x : G) * ((b : C) : G) = ((b : C) : G) * (x : G) :=
          (Subgroup.mem_centralizer_iff.mp (b : C).property.2) (x : G) x.property
        let gα : section10Malpha M := g
        calc
          (((x • g : (P : Subgroup (section10Malpha M))) :
              section10Malpha M) : G) =
              ((x • gα : section10Malpha M) : G) := by
            rfl
          _ = (x : G) * (gα : G) * (x : G)⁻¹ := by
            exact
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
                (A := X) (K := section10Malpha M) (a := x) (k := gα)
          _ = (x : G) * ((ι b : section10Malpha M) : G) * (x : G)⁻¹ := by
            simpa [gα] using
              congrArg
                (fun z : section10Malpha M => (x : G) * (z : G) * (x : G)⁻¹)
                hb_eq.symm
          _ = (x : G) * ((b : C) : G) * (x : G)⁻¹ := by
            rfl
          _ = ((b : C) : G) * (x : G) * (x : G)⁻¹ := by
            rw [hcomm]
          _ = ((b : C) : G) := by simp [mul_assoc]
          _ = (((g : (P : Subgroup (section10Malpha M))) :
                section10Malpha M) : G) := by
            simpa [ι] using
              congrArg (fun z : section10Malpha M => (z : G)) hb_eq
    let PG : Subgroup G := (P : Subgroup (section10Malpha M)).map (section10Malpha M).subtype
    have hPG_le_CM : PG ≤ subgroupCentralizerIn M X := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨g, hgP, rfl⟩
      refine ⟨section10_malpha_le_maximal (G := G) (M := M) g.property, ?_⟩
      change ((g : section10Malpha M) : G) ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      let xX : X := ⟨x, hx⟩
      let gP : (P : Subgroup (section10Malpha M)) := ⟨g, hgP⟩
      let gα : section10Malpha M := g
      have hfix := htrivP xX gP
      have hfixG :
          (x : G) * ((g : section10Malpha M) : G) * (x : G)⁻¹ =
            ((g : section10Malpha M) : G) := by
        have hsmulG :
            (((xX • gP : (P : Subgroup (section10Malpha M))) :
                section10Malpha M) : G) =
              (x : G) * ((g : section10Malpha M) : G) * (x : G)⁻¹ := by
          calc
            (((xX • gP : (P : Subgroup (section10Malpha M))) :
                section10Malpha M) : G) =
                ((xX • gα : section10Malpha M) : G) := by
              rfl
            _ = (xX : G) * (gα : G) * (xX : G)⁻¹ := by
              exact
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
                  (A := X) (K := section10Malpha M) (a := xX) (k := gα)
            _ = (x : G) * ((g : section10Malpha M) : G) * (x : G)⁻¹ := by
              rfl
        have hfixedG :
            (((xX • gP : (P : Subgroup (section10Malpha M))) :
                section10Malpha M) : G) =
              ((g : section10Malpha M) : G) := by
          exact congrArg
            (fun z : (P : Subgroup (section10Malpha M)) =>
              (((z : (P : Subgroup (section10Malpha M))) : section10Malpha M) : G))
            hfix
        exact hsmulG.symm.trans hfixedG
      have hmul := congrArg (fun t : G => t * (x : G)) hfixG
      simpa [mul_assoc] using hmul
    have hP_rank : 3 ≤ groupRank (P : Subgroup (section10Malpha M)) :=
      section10_malpha_sylow_groupRank_ge_three_of_mem_alpha_early hM hpα P
    have hPG_rank : 3 ≤ groupRank PG := by
      let ePG : (P : Subgroup (section10Malpha M)) ≃* PG :=
        Subgroup.equivMapOfInjective
          (P : Subgroup (section10Malpha M)) (section10Malpha M).subtype
          (section10Malpha M).subtype_injective
      exact hP_rank.trans
        (section10_groupRank_le_of_equiv_pre
          (R := PG) (S := (P : Subgroup (section10Malpha M))) ePG.symm)
    have hCM_large : 3 ≤ groupRank (subgroupCentralizerIn M X) :=
      hPG_rank.trans (section10_groupRank_le_of_le hPG_le_CM)
    exact theorem_9_6
      (K := subgroupCentralizerIn M X)
      (section10_subgroupCentralizerIn_maximal_proper hM)
      hCM_rank_two (Or.inl hCM_large)

/-- Lemma 10.3. -/
public theorem CFSG.lemma_10_3
    {M X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hXle : X ≤ M)
    (hXpi : IsPiSubgroup (section10AlphaPrimes M)ᶜ X)
    (hcentRank : 1 < groupRank (subgroupCentralizerIn (section10Malpha M) X)) :
    subgroupCentralizerIn M X ∈ section9UniqueSubgroups G := by
  by_cases hlarge : 3 ≤ groupRank (subgroupCentralizerIn (section10Malpha M) X)
  · exact section10_lemma_10_3_rank_ge_three hM hlarge
  · exact section10_lemma_10_3_rank_two_core hM hXle hXpi hcentRank (by omega)

end Section10
