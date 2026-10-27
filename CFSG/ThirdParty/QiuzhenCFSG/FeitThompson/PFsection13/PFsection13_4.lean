module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_4
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.4) -/


/- Extract a nonzero row/column from the signed alternative in PF `(13.3)(c)`.
In the exceptional negative branch, the row indexed by `2` is the negative of
the column indexed by `1`. -/
private theorem theorem_13_4_signed_eta_line_model_of_signAlternative
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    (τ1 : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (μsum : ℕ → Section1.ClassFunction M)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (h1p : 1 < p)
    (halt : theorem_13_3_signAlternativeData p q
      (fun j => τ1 (μsum j)) η) :
    ∃ b j : ℕ, 0 < j ∧ j < p ∧
      τ1 (μsum j) = ((-1 : ℂ) ^ b) •
        (Finset.range q).sum (fun i => η i 1) := by
  rcases halt with hpos | hneg
  · refine ⟨0, 1, by norm_num, h1p, ?_⟩
    simpa using hpos 1 (by norm_num) h1p
  · rcases hneg with ⟨hp3, hneg⟩
    have h2p : 2 < p := by omega
    rcases hneg 2 (by norm_num) h2p with ⟨j', hset, hrow⟩
    have hj'_mem : j' ∈ ({1, 2} : Finset ℕ) := by
      rw [← hset]
      simp
    have hj' : j' = 1 := by
      have hj'_cases : j' = 1 ∨ j' = 2 := by simpa using hj'_mem
      rcases hj'_cases with h | h
      · exact h
      · have h1mem : 1 ∈ ({2, j'} : Finset ℕ) := by
          rw [hset]
          simp
        simp [h] at h1mem
    refine ⟨1, 2, by norm_num, h2p, ?_⟩
    simpa [hj'] using hrow

/- Ordinary induction carries support on a subgroup's punctured preimage to
support on the ambient conjugate closure of that punctured subgroup. -/
private theorem theorem_13_4_inducedCFLinear_supportedOn_conjugateClosure
    {G : Type u}
    [Group G]
    [Finite G]
    (M H : Subgroup G)
    (φ : Section1.ClassFunction M)
    (hφ : Section1.supportedOn φ
      (subgroupSetPreimage M (Section7.puncturedSubgroupSet H))) :
    Section1.supportedOn (Section1.inducedCFLinear M φ)
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet H) Set.univ) := by
  classical
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  rw [Section1.inducedCFLinear_apply]
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ y : G,
        if hyM : y * g * y⁻¹ ∈ M then
          φ ⟨y * g * y⁻¹, hyM⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y _hy
    by_cases hyM : y * g * y⁻¹ ∈ M
    · have hy_not_pre :
          (⟨y * g * y⁻¹, hyM⟩ : M) ∉
            subgroupSetPreimage M (Section7.puncturedSubgroupSet H) := by
        intro hy_pre
        have hyH : y * g * y⁻¹ ∈ Section7.puncturedSubgroupSet H := by
          simpa [subgroupSetPreimage] using hy_pre
        apply hg
        refine ⟨y * g * y⁻¹, hyH, y⁻¹, Set.mem_univ _, ?_⟩
        simp [mul_assoc]
      have hzero := hφ ⟨y * g * y⁻¹, hyM⟩ hy_not_pre
      simp [hyM, hzero]
    · simp [hyM]
  rw [hsum]
  simp

private theorem theorem_13_4_supportedOn_subgroup_of_inducedFromLinear
    {G : Type u}
    [Group G]
    [Finite G]
    (M H : Subgroup G)
    (χ : Section1.ClassFunction M)
    (hHnormal : (H.subgroupOf M).Normal)
    (hχ : inducedFromLinearCharacterForSection13 M H χ) :
    Section1.supportedOn χ (H.subgroupOf M : Set M) := by
  classical
  rcases hχ with ⟨_hHM, θ, _hθirr, _hθdeg, hχeq⟩
  rw [hχeq]
  letI : (H.subgroupOf M).Normal := hHnormal
  exact Section10.inducedCF_supportedOn_subgroup (H.subgroupOf M) θ

private theorem theorem_13_4_difference_supportedOn_punctured
    {G : Type u}
    [Group G]
    (M H : Subgroup G)
    {φ ψ : Section1.ClassFunction M}
    (hφ : Section1.supportedOn φ (H.subgroupOf M : Set M))
    (hψ : Section1.supportedOn ψ (H.subgroupOf M : Set M))
    (hdeg : Section1.degree φ = Section1.degree ψ) :
    Section1.supportedOn (φ - ψ)
      (subgroupSetPreimage M (Section7.puncturedSubgroupSet H)) := by
  rw [Section1.supportedOn_iff] at hφ hψ ⊢
  intro x hx
  by_cases hxH : (x : G) ∈ H
  · have hxoneG : (x : G) = 1 := by
      by_contra hxne
      have hxneM : x ≠ 1 := by
        intro hxone
        exact hxne (by simpa using congrArg (fun y : M => (y : G)) hxone)
      exact hx (by
        simp [subgroupSetPreimage, Section7.puncturedSubgroupSet, hxH, hxneM])
    have hxone : x = 1 := Subtype.ext (by simpa using hxoneG)
    subst x
    change φ 1 - ψ 1 = 0
    simpa [Section1.degree_apply] using sub_eq_zero.mpr hdeg
  · have hxHsub : x ∉ (H.subgroupOf M : Set M) := by
      intro hxsub
      exact hxH (by simpa using (Subgroup.mem_subgroupOf.1 hxsub))
    simp [hφ x hxHsub, hψ x hxHsub]

private theorem theorem_13_4_conjugateCharacter_supportedOn
    {L : Type u}
    [Group L]
    (φ : Section1.ClassFunction L)
    (A : Set L)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn (Section1.conjugateCharacter φ) A := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro x hx
  simp [Section1.conjugateCharacter, hφ x hx]

/- Transport a degree-zero family difference through a coherent extension,
use PF `(13.2)(e)` to identify the source map with ordinary induction, and
deduce its ambient conjugate support. -/
private theorem theorem_13_4_coherent_difference_supportedOn_conjugateClosure
    {G : Type u}
    [Group G]
    [Finite G]
    (M MF U H : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ τ1 : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (φ ψ : Section1.ClassFunction M)
    (hcoh : Section6.coherentExtension S τ τ1)
    (hbook : agreesWithInductionOnBookAZero M MF U ⊥ ⊥ τ)
    (hφmem : φ ∈ S)
    (hψmem : ψ ∈ S)
    (hφclass : Section1.IsClassFunction φ)
    (hψclass : Section1.IsClassFunction ψ)
    (hdeg : Section1.degree φ = Section1.degree ψ)
    (hlocal : Section1.supportedOn (φ - ψ)
      (subgroupSetPreimage M (Section7.puncturedSubgroupSet H)))
    (hHle : H ≤ section8FittingSubgroup M) :
    Section1.supportedOn (τ1 (φ - ψ))
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet H) Set.univ) := by
  rcases hbook with
    ⟨_Ms, A0book, H_A0, hA0, _hMsChoice, _hTI, _hMsSharp,
      hFittingSharp, _hASet, _hdade, hind⟩
  have hCFOn : Section2.CFOn M A0book (φ - ψ) := by
    refine ⟨?_, ?_⟩
    · intro x g
      simp [hφclass x g, hψclass x g]
    intro x hxA0
    rw [Section1.supportedOn_iff] at hlocal
    apply hlocal x
    intro hxH
    apply hxA0
    apply hFittingSharp x
    have hxH' : (x : G) ∈ Section7.puncturedSubgroupSet H := by
      simpa [subgroupSetPreimage] using hxH
    exact ⟨hHle hxH'.1, hxH'.2⟩
  have hinduced : τ (φ - ψ) = Section1.inducedCFLinear M (φ - ψ) :=
    hind (φ - ψ) hCFOn
  have hspan : Section5.integerSpan S (φ - ψ) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem S hφmem)
      (Section5.integerSpan_of_mem S hψmem)
  have hspanOn : Section5.integerSpanOn S Section5.puncturedSet (φ - ψ) := by
    refine ⟨hspan, ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree φ - Section1.degree ψ = 0
    exact sub_eq_zero.mpr hdeg
  have hagree : τ1 (φ - ψ) = τ (φ - ψ) :=
    hcoh.2.2 (φ - ψ) hspanOn
  rw [hagree, hinduced]
  exact theorem_13_4_inducedCFLinear_supportedOn_conjugateClosure
    M H (φ - ψ) hlocal

private theorem theorem_13_4_centralizer_le_normalizer_of_ti
    {G : Type u}
    [Group G]
    {X : Set G}
    {x : G}
    (hTI : section16TISubset X)
    (hx : x ∈ X)
    (hxne : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer X := by
  intro c hc
  have hxConj : x ∈ section16ConjugateSet X c := by
    refine ⟨x, hx, ?_⟩
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hfix : c * x * c⁻¹ = x := by
      rw [hcomm]
      simp [mul_assoc]
    exact hfix.symm
  rcases hTI c with hsame | hdisj
  · change ∀ y : G, y ∈ X ↔ c * y * c⁻¹ ∈ X
    intro y
    constructor
    · intro hy
      rw [← hsame]
      exact ⟨y, hy, rfl⟩
    · intro hy
      have hmem : c * y * c⁻¹ ∈ section16ConjugateSet X c := by
        simpa [hsame] using hy
      rcases hmem with ⟨z, hz, hzy⟩
      have hyz : y = z := by
        simpa [mul_assoc] using
          congrArg (fun w : G => c⁻¹ * w * c) hzy
      simpa [hyz] using hz
  · have hxone : x ∈ ({1} : Set G) := hdisj ⟨hx, hxConj⟩
    exact False.elim (hxne (by simpa using hxone))

private theorem theorem_13_4_conjBy_le_centralizer_of_centralizes
    {G : Type u}
    [Group G]
    (R K : Subgroup G)
    (hcent : R ≤ Subgroup.centralizer (K : Set G))
    {x y g : G}
    (hy : y ∈ K)
    (hxy : x = g * y * g⁻¹) :
    R.conjBy g ≤ Subgroup.centralizer ({x} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff, hxy]
  rw [Subgroup.conjBy, Subgroup.mem_map] at hz
  rcases hz with ⟨r, hr, hz⟩
  rw [← hz]
  have hcomm : r * y = y * r :=
    (Subgroup.mem_centralizer_iff.mp (hcent hr) y hy).symm
  calc
    (g * r * g⁻¹) * (g * y * g⁻¹) = g * (r * y) * g⁻¹ := by group
    _ = g * (y * r) * g⁻¹ := by rw [hcomm]
    _ = (g * y * g⁻¹) * (g * r * g⁻¹) := by group

private theorem theorem_13_4_prime_dvd_hall_index_of_prime_power_subgroup
    {G : Type u}
    [Group G]
    [Finite G]
    {S W R : Subgroup G}
    {p q : ℕ}
    (hWleS : W ≤ S)
    (hWcard : Nat.card W = q)
    (hRleS : R ≤ S)
    (hRcard : Nat.card R = q ^ p)
    (hqPrime : Nat.Prime q)
    (hpPrime : Nat.Prime p) :
    q ∣ (W.subgroupOf S).index := by
  have hRsub_card : Nat.card (R.subgroupOf S) = q ^ p := by
    rw [natCard_subgroupOf_eq R S hRleS, hRcard]
  have hRsub_dvd_S : q ^ p ∣ Nat.card S := by
    have hdiv : Nat.card (R.subgroupOf S) ∣ Nat.card S :=
      Subgroup.card_subgroup_dvd_card (R.subgroupOf S)
    rwa [hRsub_card] at hdiv
  have hq2_dvd_qp : q ^ 2 ∣ q ^ p :=
    Nat.pow_dvd_pow q hpPrime.two_le
  have hq2_dvd_S : q ^ 2 ∣ Nat.card S := hq2_dvd_qp.trans hRsub_dvd_S
  have hWsub_card : Nat.card (W.subgroupOf S) = q := by
    rw [natCard_subgroupOf_eq W S hWleS, hWcard]
  have hS_card : Nat.card S = (W.subgroupOf S).index * q := by
    calc
      Nat.card S = (W.subgroupOf S).index * Nat.card (W.subgroupOf S) :=
        (Subgroup.index_mul_card (H := W.subgroupOf S)).symm
      _ = (W.subgroupOf S).index * q := by rw [hWsub_card]
  have hq2_dvd_idx_mul : q ^ 2 ∣ (W.subgroupOf S).index * q := by
    rwa [hS_card] at hq2_dvd_S
  have hq_mul_dvd : q * q ∣ q * (W.subgroupOf S).index := by
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      hq2_dvd_idx_mul
  exact Nat.dvd_of_mul_dvd_mul_left hqPrime.pos hq_mul_dvd

private theorem theorem_13_4_disjoint_conjugateClosures_of_left
    {G : Type u}
    [Group G]
    (X Y : Set G)
    (hdisj : Disjoint X
      (section16ConjugatesOfSetBySet Y Set.univ)) :
    Disjoint (section16ConjugatesOfSetBySet X Set.univ)
      (section16ConjugatesOfSetBySet Y Set.univ) := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro z hzX hzY
  rcases hzX with ⟨x, hxX, g, _hg, hzXeq⟩
  rcases hzY with ⟨y, hyY, k, _hk, hzYeq⟩
  have hxY : x ∈ section16ConjugatesOfSetBySet Y Set.univ := by
    refine ⟨y, hyY, g⁻¹ * k, Set.mem_univ _, ?_⟩
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (k * y * k⁻¹) * g := by rw [← hzXeq, hzYeq]
      _ = (g⁻¹ * k) * y * (g⁻¹ * k)⁻¹ := by group
  exact hdisj hxX hxY


private theorem theorem_13_4_disjoint_conjugateClosures_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Disjoint
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (P ⊔ C)) Set.univ)
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (Q ⊔ D)) Set.univ) := by
  apply theorem_13_4_disjoint_conjugateClosures_of_left
  rw [Set.disjoint_left]
  intro x hxH hxK
  rcases hxK with ⟨y, hyK, g, _hg, hxEq⟩
  have hsourceOrig := hsource
  have hsourceT :
      hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
        Tfam Sfam τT τS q p v u d c :=
    section13_hypothesis_13_1_sourceData_swap hsourceOrig
  rcases theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c hsourceT with
    ⟨_hQMF, _hTypeT, _hTypeLargeT, _hVcomm, _hFrobT, hQelem, hQcard,
      _hvBound, _hcohT, _hbookT, _hAZeroT, _hnormT⟩
  letI : IsMulCommutative Q := IsElementaryAbelian.toIsMulCommutative q
  rcases hsource with
    ⟨_hcase, hTypePS, _hTypePT, hpCard, hqCard, _hC, hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hTypePS with
    ⟨_hPMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUle, _hUnil,
      _hW1norm, _hDercomp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1leS, hW1HallSub⟩
  have hDleCentQ : D ≤ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    have hz' : z ∈ subgroupCentralizerIn V Q := by
      rw [← hD]
      exact hz
    exact hz'.2
  have hQleCentD : Q ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.mpr hDleCentQ
  have hQleCentK : Q ≤ Subgroup.centralizer ((Q ⊔ D : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hk with hkQ | hkD
    · exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer (H := Q) hz) k hkQ
    · exact Subgroup.mem_centralizer_iff.mp (hQleCentD hz) k hkD
  have hQgCent : Q.conjBy g ≤ Subgroup.centralizer ({x} : Set G) :=
    theorem_13_4_conjBy_le_centralizer_of_centralizes
      Q (Q ⊔ D) hQleCentK hyK.1 hxEq
  have hTINorm : section16TISubsetWithNormalizer
      (Section7.puncturedSubgroupSet (P ⊔ C)) Smax :=
    section13_theorem_13_2_H_punctured_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D (P ⊔ C) Sfam Tfam τS τT
      p q u v c d hsourceOrig rfl
  have hCentS : Subgroup.centralizer ({x} : Set G) ≤ Smax :=
    (theorem_13_4_centralizer_le_normalizer_of_ti
      hTINorm.1 hxH hxH.2).trans (le_of_eq hTINorm.2)
  have hQgS : Q.conjBy g ≤ Smax := hQgCent.trans hCentS
  have hqPrime : Nat.Prime q := by
    have hcond : Section8.typeIIToIVSourceCondition Smax U W1 :=
      section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
    rcases hcond with ⟨_hUne, hW1primeOrder, _hTI⟩
    rcases hW1primeOrder with ⟨r, hr⟩
    rw [hqCard, hr]
    exact r.property
  have hpPrime : Nat.Prime p := by
    have hcond : Section8.typeIIToIVSourceCondition Tmax V W2 :=
      section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
        q p v u d c hsourceT
    rcases hcond with ⟨_hVne, hW2primeOrder, _hTI⟩
    rcases hW2primeOrder with ⟨r, hr⟩
    rw [hpCard, hr]
    exact r.property
  have hQgcard : Nat.card (Q.conjBy g) = q ^ p := by
    rw [section11_card_conjBy (G := G) Q g, hQcard]
  have hqDvdIndex : q ∣ (W1.subgroupOf Smax).index :=
    theorem_13_4_prime_dvd_hall_index_of_prime_power_subgroup
      (S := Smax) (W := W1) (R := Q.conjBy g)
      (p := p) (q := q) hW1leS hqCard.symm hQgS hQgcard
      hqPrime hpPrime
  have hqMem : (⟨q, hqPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet W1 := by
    change q ∣ Nat.card W1
    rw [← hqCard]
  have hqNotIndex : ¬ q ∣ (W1.subgroupOf Smax).index := by
    intro hqIndex
    exact (hW1HallSub.p_in_pi_of_p_dvd_index ⟨q, hqPrime⟩ hqIndex) hqMem
  exact hqNotIndex hqDvdIndex


private theorem theorem_13_4_scalarProduct_eq_zero_of_pair_differences
    {G : Type u}
    [Group G]
    [Finite G]
    (a b c d : Section1.ClassFunction G)
    (ha : Section3.IsSignedIrreducibleCharacter a)
    (hb : Section3.IsSignedIrreducibleCharacter b)
    (hc : Section3.IsSignedIrreducibleCharacter c)
    (hd : Section3.IsSignedIrreducibleCharacter d)
    (hab : Section1.scalarProduct G a b = 0)
    (hcd : Section1.scalarProduct G c d = 0)
    (hab1 : a 1 = b 1)
    (hcd1 : c 1 = d 1)
    (hdiff : Section1.scalarProduct G (a - b) (c - d) = 0) :
    Section1.scalarProduct G a c = 0 := by
  by_contra hac
  have hba : Section1.scalarProduct G b a = 0 := by
    have hswap := Section1.scalarProduct_star_swap b a
    rw [hab] at hswap
    simpa using hswap.symm
  have hselfA : Section1.scalarProduct G a a = 1 :=
    Section12.scalarProduct_self_of_isSignedIrreducibleCharacter ha
  have hzero_of_eq_neg : ∀ z w : ℂ, z = w → z = -w → z = 0 := by
    intro z w hzw hneg
    subst z
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hneg)
  rcases Section5.signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero_pf59
      ha hc hac with hcEq | hcEq
  · have had : Section1.scalarProduct G a d = 0 := by
      simpa [hcEq] using hcd
    have hexpand := hdiff
    rw [Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      hcEq, hselfA, had, hba] at hexpand
    have hbd : Section1.scalarProduct G b d = -1 := by
      linear_combination hexpand
    have hdEq : d = -b :=
      Section5.eq_neg_of_scalarProduct_eq_neg_one_signed_pf59 hb hd hbd
    have hopp : a 1 = -(b 1) := by
      simpa [hcEq, hdEq] using hcd1
    have ha1zero : a 1 = 0 := hzero_of_eq_neg (a 1) (b 1) hab1 hopp
    exact Section12.degree_ne_zero_of_signedIrreducible ha (by
      simpa [Section1.degree_apply] using ha1zero)
  · have had : Section1.scalarProduct G a d = 0 := by
      have h := hcd
      rw [hcEq, show -a = (-1 : ℂ) • a by ext z; simp,
        Section1.scalarProduct_smul_left] at h
      simpa using h
    have hbc : Section1.scalarProduct G b (-a) = 0 := by
      rw [show -a = (-1 : ℂ) • a by ext z; simp,
        Section1.scalarProduct_smul_right]
      simp [hba]
    have hacNeg : Section1.scalarProduct G a (-a) = -1 := by
      rw [show -a = (-1 : ℂ) • a by ext z; simp,
        Section1.scalarProduct_smul_right, hselfA]
      norm_num
    have hexpand := hdiff
    rw [Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      hcEq, hacNeg, had, hbc] at hexpand
    have hbd : Section1.scalarProduct G b d = 1 := by
      linear_combination hexpand
    have hdEq : d = b :=
      Section5.signed_irreducible_eq_of_scalarProduct_eq_one_pf59 hb hd hbd
    have hopp : a 1 = -(b 1) := by
      have hneg : -(a 1) = b 1 := by
        simpa [hcEq, hdEq] using hcd1
      calc
        a 1 = -(-(a 1)) := by simp
        _ = -(b 1) := by rw [hneg]
    have ha1zero : a 1 = 0 := hzero_of_eq_neg (a 1) (b 1) hab1 hopp
    exact Section12.degree_ne_zero_of_signedIrreducible ha (by
      simpa [Section1.degree_apply] using ha1zero)

private theorem theorem_13_4_scalarProduct_sum_range_left
    {G : Type u}
    [Group G]
    [Finite G]
    (n : ℕ)
    (φ : ℕ → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G ((Finset.range n).sum φ) ψ =
      (Finset.range n).sum (fun i => Section1.scalarProduct G (φ i) ψ) := by
  induction n with
  | zero => simp [Section1.scalarProduct]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Section1.scalarProduct_add_left, ih]

private theorem theorem_13_4_scalarProduct_sum_range_right
    {G : Type u}
    [Group G]
    [Finite G]
    (n : ℕ)
    (φ : Section1.ClassFunction G)
    (ψ : ℕ → Section1.ClassFunction G) :
    Section1.scalarProduct G φ ((Finset.range n).sum ψ) =
      (Finset.range n).sum (fun i => Section1.scalarProduct G φ (ψ i)) := by
  induction n with
  | zero => simp [Section1.scalarProduct]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Section5.scalarProduct_add_right, ih]

private theorem theorem_13_4_eta_scalarProduct
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q i j k l : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (hi : i < q)
    (hj : j < p)
    (hk : k < q)
    (hl : l < p) :
    Section1.scalarProduct G (η i j) (η k l) =
      if i = k ∧ j = l then 1 else 0 := by
  rcases hnotation with
    ⟨hω, hσ, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero, _hνzero, _hμind, _hνind, _hμsum, _hνsum,
      _hbaseS, _hbaseT, _hμdeg, _hνdeg⟩
  rcases hω with ⟨_h31, hqPos, hpPos, ωFin, hOmega, hωeq⟩
  rw [hη i j hi hj, hη k l hk hl,
    hωeq i j hi hj, hωeq k l hk hl]
  calc
    Section1.scalarProduct G
        (σ (ωFin ⟨i, hi⟩ ⟨j, hj⟩))
        (σ (ωFin ⟨k, hk⟩ ⟨l, hl⟩)) =
      Section1.scalarProduct W
        (ωFin ⟨i, hi⟩ ⟨j, hj⟩)
        (ωFin ⟨k, hk⟩ ⟨l, hl⟩) :=
          hσ.1 _ _ (hOmega.is_class _ _) (hOmega.is_class _ _)
    _ = if ((⟨i, hi⟩, ⟨j, hj⟩) : Fin q × Fin p) =
          (⟨k, hk⟩, ⟨l, hl⟩) then 1 else 0 :=
      hOmega.orthonormal (⟨i, hi⟩, ⟨j, hj⟩)
        (⟨k, hk⟩, ⟨l, hl⟩)
    _ = if i = k ∧ j = l then 1 else 0 := by
      simp [Prod.ext_iff, Fin.ext_iff]

private theorem theorem_13_4_eta_column_row_scalarProduct_eq_one
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (h1p : 1 < p)
    (h1q : 1 < q) :
    Section1.scalarProduct G
      ((Finset.range q).sum (fun i => η i 1))
      ((Finset.range p).sum (fun j => η 1 j)) = 1 := by
  rw [theorem_13_4_scalarProduct_sum_range_left]
  calc
    (Finset.range q).sum (fun i =>
        Section1.scalarProduct G (η i 1)
          ((Finset.range p).sum (fun j => η 1 j))) =
      (Finset.range q).sum (fun i =>
        (Finset.range p).sum (fun j =>
          Section1.scalarProduct G (η i 1) (η 1 j))) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [theorem_13_4_scalarProduct_sum_range_right]
    _ = (Finset.range q).sum (fun i => if i = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiq : i < q := Finset.mem_range.mp hi
      calc
        (Finset.range p).sum (fun j =>
            Section1.scalarProduct G (η i 1) (η 1 j)) =
          (Finset.range p).sum (fun j =>
            if i = 1 ∧ 1 = j then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact theorem_13_4_eta_scalarProduct
                Smax Tmax W W1 W2 ω η μ ν μsum νsum δ δ' σ
                p q i 1 1 j hnotation hiq h1p h1q
                (Finset.mem_range.mp hj)
        _ = if i = 1 then 1 else 0 := by
          by_cases hi1 : i = 1
          · subst i
            simp [h1p]
          · simp [hi1]
    _ = 1 := by simp [h1q]

private theorem theorem_13_4_one_not_mem_conjugateClosure_punctured
    {G : Type u}
    [Group G]
    (H : Subgroup G) :
    (1 : G) ∉ section16ConjugatesOfSetBySet
      (Section7.puncturedSubgroupSet H) Set.univ := by
  intro hmem
  rcases hmem with ⟨x, hx, g, _hg, hEq⟩
  have hxone : x = 1 := by
    simpa [mul_assoc] using congrArg (fun z : G => g⁻¹ * z * g) hEq.symm
  exact hx.2 hxone

private theorem theorem_13_4_dual_linear_induction_contradiction_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (lamS : Section1.ClassFunction Smax)
    (lamT : Section1.ClassFunction Tmax)
    (hlamS_mem : lamS ∈ Sfam)
    (hlamT_mem : lamT ∈ Tfam)
    (hlamS_irred : Section1.IsIrreducibleCharacterOnGroup lamS)
    (hlamS_deg : Section1.degree lamS = (u * q : ℂ))
    (hlamS_linear : inducedFromLinearCharacterForSection13 Smax (P ⊔ C) lamS)
    (hlamT_irred : Section1.IsIrreducibleCharacterOnGroup lamT)
    (hlamT_deg : Section1.degree lamT = (v * p : ℂ))
    (hlamT_linear : inducedFromLinearCharacterForSection13 Tmax (Q ⊔ D) lamT) :
    False := by
  classical
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcase, hTypePS, hTypePT, hpCard, hqCard, hC, hD, _hc, _hd,
      _hUcard, _hVcard, hSfamData, hTfamData, _hDadeS, _hDadeT,
      hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBeta, _hChoice, hmin, hFourSixS, hFourSixT⟩
  letI : IsMinCE G := hmin
  rcases hnotationData with
    ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hnotation⟩
  have hsourceT :
      hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
        Tfam Sfam τT τS q p v u d c :=
    section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hnotationT :
      hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1 q p
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  rcases (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig).1
      ω η μ ν μsum νsum δ δ' σ hnotation with
    ⟨_hSignS, τ1S, hcohS, houtputS⟩
  rcases (theorem_13_3 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c hsourceT).1
      (fun i j => ω j i) (fun i j => η j i)
      (fun i j => ν j i) (fun i j => μ j i)
      νsum μsum δ' δ σ hnotationT with
    ⟨_hSignT, τ1T, hcohT, houtputT⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, hW1ne, hW2ne, _hWnorm, _hSmax, _hTmax,
      _hSFP, _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj,
      _hST, _hII, _hSType, _hTType, _hmax⟩
  have h1p : 1 < p := by
    have hcard : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hpCard] using hcard
  have h1q : 1 < q := by
    have hcard : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hqCard] using hcard
  rcases theorem_13_4_signed_eta_line_model_of_signAlternative
      τ1S p q μsum η h1p houtputS.2 with
    ⟨bS, jS, hjS0, hjSp, hmuModel⟩
  rcases theorem_13_4_signed_eta_line_model_of_signAlternative
      τ1T q p νsum (fun i j => η j i) h1q houtputT.2 with
    ⟨bT, iT, hiT0, hiTq, hnuModel'⟩
  have hnuModel :
      τ1T (νsum iT) = ((-1 : ℂ) ^ bT) •
        (Finset.range p).sum (fun j => η 1 j) := by
    simpa using hnuModel'
  rcases houtputS.1 jS hjS0 hjSp with
    ⟨hmuChar, hmuDeg, hmuLinear, hmuMem⟩
  rcases houtputT.1 iT hiT0 hiTq with
    ⟨hnuChar, hnuDeg, hnuLinear, hnuMem⟩
  have hFitS : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hTypePS
  have hFitT : section8FittingSubgroup Tmax = Q ⊔ D := by
    simpa [hD] using Section8.theorem_8_5_a Tmax Q V W2 W1 hTypePT
  have hHnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
    simpa [hFitS] using section8FittingSubgroup_normal_in Smax
  have hKnormal : ((Q ⊔ D).subgroupOf Tmax).Normal := by
    simpa [hFitT] using section8FittingSubgroup_normal_in Tmax
  have hCleU : C ≤ U := by
    intro x hx
    have hx' : x ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact hx
    exact hx'.1
  have hDleV : D ≤ V := by
    intro x hx
    have hx' : x ∈ subgroupCentralizerIn V Q := by
      rw [← hD]
      exact hx
    exact hx'.1
  have hHle : P ⊔ C ≤ section8FittingSubgroup Smax := by
    rw [hFitS]
  have hKle : Q ⊔ D ≤ section8FittingSubgroup Tmax := by
    rw [hFitT]
  have hlamSSupport :
      Section1.supportedOn lamS ((P ⊔ C).subgroupOf Smax : Set Smax) :=
    theorem_13_4_supportedOn_subgroup_of_inducedFromLinear
      Smax (P ⊔ C) lamS hHnormal hlamS_linear
  have hmuSupport :
      Section1.supportedOn (μsum jS)
        ((P ⊔ C).subgroupOf Smax : Set Smax) :=
    theorem_13_4_supportedOn_subgroup_of_inducedFromLinear
      Smax (P ⊔ C) (μsum jS) hHnormal hmuLinear
  have hlamTSupport :
      Section1.supportedOn lamT ((Q ⊔ D).subgroupOf Tmax : Set Tmax) :=
    theorem_13_4_supportedOn_subgroup_of_inducedFromLinear
      Tmax (Q ⊔ D) lamT hKnormal hlamT_linear
  have hnuSupport :
      Section1.supportedOn (νsum iT)
        ((Q ⊔ D).subgroupOf Tmax : Set Tmax) :=
    theorem_13_4_supportedOn_subgroup_of_inducedFromLinear
      Tmax (Q ⊔ D) (νsum iT) hKnormal hnuLinear
  have hdegS : Section1.degree lamS = Section1.degree (μsum jS) := by
    rw [hlamS_deg, hmuDeg]
  have hdegT : Section1.degree lamT = Section1.degree (νsum iT) := by
    rw [hlamT_deg, hnuDeg]
  have hlocalS : Section1.supportedOn (lamS - μsum jS)
      (subgroupSetPreimage Smax
        (Section7.puncturedSubgroupSet (P ⊔ C))) :=
    theorem_13_4_difference_supportedOn_punctured
      Smax (P ⊔ C) hlamSSupport hmuSupport hdegS
  have hlocalT : Section1.supportedOn (lamT - νsum iT)
      (subgroupSetPreimage Tmax
        (Section7.puncturedSubgroupSet (Q ⊔ D))) :=
    theorem_13_4_difference_supportedOn_punctured
      Tmax (Q ⊔ D) hlamTSupport hnuSupport hdegT
  have hbookS : agreesWithInductionOnBookAZero Smax P U W1 W2 τS :=
    theorem_13_2_agreesWithInductionOnBookAZero
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hbookT : agreesWithInductionOnBookAZero Tmax Q V W2 W1 τT :=
    theorem_13_2_agreesWithInductionOnBookAZero
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceT
  have hdiffSupportS : Section1.supportedOn (τ1S (lamS - μsum jS))
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (P ⊔ C)) Set.univ) :=
    theorem_13_4_coherent_difference_supportedOn_conjugateClosure
      Smax P U (P ⊔ C) Sfam τS τ1S lamS (μsum jS)
      hcohS hbookS hlamS_mem hmuMem
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamS_irred)
      (Section1.isCharacter_isClassFunction (μsum jS) hmuChar)
      hdegS hlocalS hHle
  have hdiffSupportT : Section1.supportedOn (τ1T (lamT - νsum iT))
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (Q ⊔ D)) Set.univ) :=
    theorem_13_4_coherent_difference_supportedOn_conjugateClosure
      Tmax Q V (Q ⊔ D) Tfam τT τ1T lamT (νsum iT)
      hcohT hbookT hlamT_mem hnuMem
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamT_irred)
      (Section1.isCharacter_isClassFunction (νsum iT) hnuChar)
      hdegT hlocalT hKle
  have hdisj := theorem_13_4_disjoint_conjugateClosures_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsourceOrig
  have hdiffOrth : Section1.scalarProduct G
      (τ1S (lamS - μsum jS)) (τ1T (lamT - νsum iT)) = 0 :=
    Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
      hdiffSupportS hdiffSupportT hdisj
  have hlamSConjMem : Section1.conjugateCharacter lamS ∈ Sfam :=
    section13_nonkernelInducedFamily_conjugate_mem
      Smax (P ⊔ U) P Sfam hSfamData hlamS_mem
  have hlamTConjMem : Section1.conjugateCharacter lamT ∈ Tfam :=
    section13_nonkernelInducedFamily_conjugate_mem
      Tmax (Q ⊔ V) Q Tfam hTfamData hlamT_mem
  have hlamSConjIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateCharacter lamS) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hlamS_irred
  have hlamTConjIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateCharacter lamT) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hlamT_irred
  have hlamSConjSupport : Section1.supportedOn
      (Section1.conjugateCharacter lamS)
      ((P ⊔ C).subgroupOf Smax : Set Smax) :=
    theorem_13_4_conjugateCharacter_supportedOn lamS _ hlamSSupport
  have hlamTConjSupport : Section1.supportedOn
      (Section1.conjugateCharacter lamT)
      ((Q ⊔ D).subgroupOf Tmax : Set Tmax) :=
    theorem_13_4_conjugateCharacter_supportedOn lamT _ hlamTSupport
  have hdegSConj : Section1.degree lamS =
      Section1.degree (Section1.conjugateCharacter lamS) :=
    (Section5.degree_conjugateCharacter_eq_of_isCharacter
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hlamS_irred)).symm
  have hdegTConj : Section1.degree lamT =
      Section1.degree (Section1.conjugateCharacter lamT) :=
    (Section5.degree_conjugateCharacter_eq_of_isCharacter
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hlamT_irred)).symm
  have hlocalConjS : Section1.supportedOn
      (lamS - Section1.conjugateCharacter lamS)
      (subgroupSetPreimage Smax
        (Section7.puncturedSubgroupSet (P ⊔ C))) :=
    theorem_13_4_difference_supportedOn_punctured Smax (P ⊔ C)
      hlamSSupport hlamSConjSupport hdegSConj
  have hlocalConjT : Section1.supportedOn
      (lamT - Section1.conjugateCharacter lamT)
      (subgroupSetPreimage Tmax
        (Section7.puncturedSubgroupSet (Q ⊔ D))) :=
    theorem_13_4_difference_supportedOn_punctured Tmax (Q ⊔ D)
      hlamTSupport hlamTConjSupport hdegTConj
  have hconjDiffSupportS : Section1.supportedOn
      (τ1S (lamS - Section1.conjugateCharacter lamS))
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (P ⊔ C)) Set.univ) :=
    theorem_13_4_coherent_difference_supportedOn_conjugateClosure
      Smax P U (P ⊔ C) Sfam τS τ1S lamS
      (Section1.conjugateCharacter lamS) hcohS hbookS
      hlamS_mem hlamSConjMem
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamS_irred)
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamSConjIrr)
      hdegSConj hlocalConjS hHle
  have hconjDiffSupportT : Section1.supportedOn
      (τ1T (lamT - Section1.conjugateCharacter lamT))
      (section16ConjugatesOfSetBySet
        (Section7.puncturedSubgroupSet (Q ⊔ D)) Set.univ) :=
    theorem_13_4_coherent_difference_supportedOn_conjugateClosure
      Tmax Q V (Q ⊔ D) Tfam τT τ1T lamT
      (Section1.conjugateCharacter lamT) hcohT hbookT
      hlamT_mem hlamTConjMem
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamT_irred)
      (Section10.isClassFunction_of_isIrreducibleCharacterOnGroup hlamTConjIrr)
      hdegTConj hlocalConjT hKle
  have hconjDiffOrth : Section1.scalarProduct G
      (τ1S (lamS - Section1.conjugateCharacter lamS))
      (τ1T (lamT - Section1.conjugateCharacter lamT)) = 0 :=
    Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
      hconjDiffSupportS hconjDiffSupportT hdisj
  have hPUnormal : ((P ⊔ U).subgroupOf Smax).Normal := by
    have hType := hTypePS
    rcases hType with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUle, _hUnil,
        _hW1norm, hDercomp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
        _hW2le, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
    have hDerNormal :
        ((ambientDerivedSubgroup Smax).subgroupOf Smax).Normal := by
      simpa using
        (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
    simpa [← hDercomp.2.2.1] using hDerNormal
  have hQVnormal : ((Q ⊔ V).subgroupOf Tmax).Normal := by
    have hType := hTypePT
    rcases hType with
      ⟨_hMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVle, _hVnil,
        _hW2norm, hDercomp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
        _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal := by
      simpa using
        (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [← hDercomp.2.2.1] using hDerNormal
  have hoddS : Odd (Nat.card Smax) :=
    section13_odd_card_subgroup_of_odd_group Smax IsMinCE.odd_order
  have hoddT : Odd (Nat.card Tmax) :=
    section13_odd_card_subgroup_of_odd_group Tmax IsMinCE.odd_order
  have hlamSNe : lamS ≠ Section1.conjugateCharacter lamS :=
    section13_nonkernelInducedFamily_ne_conjugate
      Smax (P ⊔ U) P Sfam
      hPUnormal hoddS hSfamData lamS hlamS_mem
  have hlamTNe : lamT ≠ Section1.conjugateCharacter lamT :=
    section13_nonkernelInducedFamily_ne_conjugate
      Tmax (Q ⊔ V) Q Tfam
      hQVnormal hoddT hTfamData lamT hlamT_mem
  have hpairOrthS : Section1.scalarProduct G (τ1S lamS)
      (τ1S (Section1.conjugateCharacter lamS)) = 0 := by
    calc
      Section1.scalarProduct G (τ1S lamS)
          (τ1S (Section1.conjugateCharacter lamS)) =
            Section1.scalarProduct Smax lamS
          (Section1.conjugateCharacter lamS) :=
            Section5.isCFLinearIsometryOnSpan_apply_of_mem
              hcohS.1 hlamS_mem hlamSConjMem
      _ = 0 := Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlamS_irred hlamSConjIrr hlamSNe
  have hpairOrthT : Section1.scalarProduct G (τ1T lamT)
      (τ1T (Section1.conjugateCharacter lamT)) = 0 := by
    calc
      Section1.scalarProduct G (τ1T lamT)
          (τ1T (Section1.conjugateCharacter lamT)) =
            Section1.scalarProduct Tmax lamT
          (Section1.conjugateCharacter lamT) :=
            Section5.isCFLinearIsometryOnSpan_apply_of_mem
              hcohT.1 hlamT_mem hlamTConjMem
      _ = 0 := Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlamT_irred hlamTConjIrr hlamTNe
  have hpairOneS : (τ1S lamS) 1 =
      (τ1S (Section1.conjugateCharacter lamS)) 1 := by
    have hzero := (Section1.supportedOn_iff.mp hconjDiffSupportS) 1
      (theorem_13_4_one_not_mem_conjugateClosure_punctured (P ⊔ C))
    simp only [map_sub] at hzero
    change (τ1S lamS) 1 -
      (τ1S (Section1.conjugateCharacter lamS)) 1 = 0 at hzero
    exact sub_eq_zero.mp hzero
  have hpairOneT : (τ1T lamT) 1 =
      (τ1T (Section1.conjugateCharacter lamT)) 1 := by
    have hzero := (Section1.supportedOn_iff.mp hconjDiffSupportT) 1
      (theorem_13_4_one_not_mem_conjugateClosure_punctured (Q ⊔ D))
    simp only [map_sub] at hzero
    change (τ1T lamT) 1 -
      (τ1T (Section1.conjugateCharacter lamT)) 1 = 0 at hzero
    exact sub_eq_zero.mp hzero
  have hSignedS : Section3.IsSignedIrreducibleCharacter (τ1S lamS) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hcohS hlamS_mem hlamS_irred
  have hSignedSConj : Section3.IsSignedIrreducibleCharacter
      (τ1S (Section1.conjugateCharacter lamS)) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hcohS hlamSConjMem hlamSConjIrr
  have hSignedT : Section3.IsSignedIrreducibleCharacter (τ1T lamT) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hcohT hlamT_mem hlamT_irred
  have hSignedTConj : Section3.IsSignedIrreducibleCharacter
      (τ1T (Section1.conjugateCharacter lamT)) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hcohT hlamTConjMem hlamTConjIrr
  have hcross : Section1.scalarProduct G (τ1S lamS) (τ1T lamT) = 0 :=
    theorem_13_4_scalarProduct_eq_zero_of_pair_differences
      (τ1S lamS) (τ1S (Section1.conjugateCharacter lamS))
      (τ1T lamT) (τ1T (Section1.conjugateCharacter lamT))
      hSignedS hSignedSConj hSignedT hSignedTConj
      hpairOrthS hpairOrthT hpairOneS hpairOneT (by
        simpa only [map_sub] using hconjDiffOrth)
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hMF2S, _hType2S, _hLarge2S, _hUcomm2, _hFrob2S, _hPelem2,
      _hPcard2, _huBound2, hcohBaseS, _hBook2S, _hAZero2S, _hNorm2S⟩
  rcases theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c hsourceT with
    ⟨_hMF2T, _hType2T, _hLarge2T, _hVcomm2, _hFrob2T, _hQelem2,
      _hQcard2, _hvBound2, hcohBaseT, _hBook2T, _hAZero2T, _hNorm2T⟩
  have hmixedS : Section1.scalarProduct G (τ1S lamS)
      ((Finset.range p).sum (fun j => η 1 j)) = 0 := by
    rw [theorem_13_4_scalarProduct_sum_range_right]
    apply Finset.sum_eq_zero
    intro j hj
    exact section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
      Smax Tmax W W1 W2 P U Sfam τS τ1S
      ω η μ ν μsum νsum δ δ' σ p q hTypePS hFourSixS hSfamData
      hcohBaseS hcohS hnotation lamS hlamS_mem hlamS_irred
      1 j h1q (Finset.mem_range.mp hj)
  have hmixedT : Section1.scalarProduct G
      ((Finset.range q).sum (fun i => η i 1)) (τ1T lamT) = 0 := by
    rw [theorem_13_4_scalarProduct_sum_range_left]
    apply Finset.sum_eq_zero
    intro i hi
    have hforward : Section1.scalarProduct G (τ1T lamT) (η i 1) = 0 :=
      section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
        Tmax Smax W W2 W1 Q V Tfam τT τ1T
        (fun i j => ω j i) (fun i j => η j i)
        (fun i j => ν j i) (fun i j => μ j i)
        νsum μsum δ' δ σ q p hTypePT hFourSixT hTfamData
        hcohBaseT hcohT hnotationT lamT hlamT_mem hlamT_irred
        1 i h1p (Finset.mem_range.mp hi)
    have hswap := Section1.scalarProduct_star_swap (η i 1) (τ1T lamT)
    rw [hforward] at hswap
    simpa using hswap.symm
  have heta : Section1.scalarProduct G
      ((Finset.range q).sum (fun i => η i 1))
      ((Finset.range p).sum (fun j => η 1 j)) = 1 :=
    theorem_13_4_eta_column_row_scalarProduct_eq_one
      Smax Tmax W W1 W2 ω η μ ν μsum νsum δ δ' σ
      p q hnotation h1p h1q
  have hmixedSScaled : Section1.scalarProduct G (τ1S lamS)
      (((-1 : ℂ) ^ bT) •
        (Finset.range p).sum (fun j => η 1 j)) = 0 := by
    rw [Section1.scalarProduct_smul_right, hmixedS]
    simp
  have hmixedTScaled : Section1.scalarProduct G
      (((-1 : ℂ) ^ bS) •
        (Finset.range q).sum (fun i => η i 1)) (τ1T lamT) = 0 := by
    rw [Section1.scalarProduct_smul_left, hmixedT]
    simp
  have hetaScaled : Section1.scalarProduct G
      (((-1 : ℂ) ^ bS) •
        (Finset.range q).sum (fun i => η i 1))
      (((-1 : ℂ) ^ bT) •
        (Finset.range p).sum (fun j => η 1 j)) =
      ((-1 : ℂ) ^ bS) * star ((-1 : ℂ) ^ bT) := by
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      heta]
    ring
  have hfinal := hdiffOrth
  rw [map_sub, map_sub, hmuModel, hnuModel,
    Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
    Section5.scalarProduct_sub_right, hcross, hmixedSScaled,
    hmixedTScaled, hetaScaled] at hfinal
  have hsignZero : ((-1 : ℂ) ^ bS) * star ((-1 : ℂ) ^ bT) = 0 := by
    linear_combination hfinal
  have hsignNe : ((-1 : ℂ) ^ bS) * star ((-1 : ℂ) ^ bT) ≠ 0 := by
    simp
  exact hsignNe hsignZero

private theorem theorem_13_4_dual_theorem_13_10_hypothesis_false
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    ¬ theorem_13_10_hypothesis Tmax Q D Tfam q p v := by
  intro h10T
  rcases h10 with ⟨lamS, _hlamS_mem, hlamS_irred, hlamS_deg, hlamS_linear⟩
  rcases h10T with ⟨lamT, _hlamT_mem, hlamT_irred, hlamT_deg, hlamT_linear⟩
  exact theorem_13_4_dual_linear_induction_contradiction_source
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource lamS lamT
    _hlamS_mem _hlamT_mem
    hlamS_irred hlamS_deg hlamS_linear
    hlamT_irred hlamT_deg hlamT_linear

public theorem theorem_13_4
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      theorem_13_10_hypothesis Smax P C Sfam p q u →
        D = ⊥ ∧ case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v ∧
          v = (q ^ p - 1) / (q - 1) := by
  intro hsource h10
  have hsourceT :
      hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
        Tfam Sfam τT τS q p v u d c :=
    section13_hypothesis_13_1_sourceData_swap hsource
  have hnotT :
      ¬ theorem_13_10_hypothesis Tmax Q D Tfam q p v :=
    theorem_13_4_dual_theorem_13_10_hypothesis_false
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  exact (theorem_13_3 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT).2 hnotT
end CFSG.Section13
