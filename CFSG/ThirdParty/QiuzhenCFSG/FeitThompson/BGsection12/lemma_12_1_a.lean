module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_7
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Section 12 Lemma 12.1 Infrastructure

This file contains the reusable notation and support lemmas for Lemma 12.1.
-/

section Notation

variable {G : Type*} [Group G] [Finite G]

/-- The set `τ₁(M) = {p ∈ σ(M)' | p ∉ π(M') and r_p(M) = 1}`. -/
@[expose] public def CFSG.section12Tau1Primes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∉ section10SigmaPrimes M ∧
      p ∉ subgroupPrimeSet (derivedSubgroup M) ∧ primeRank p.val M = 1}

/-- The set `τ₂(M) = {p ∈ σ(M)' | r_p(M) = 2}`. -/
@[expose] public def CFSG.section12Tau2Primes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∉ section10SigmaPrimes M ∧ primeRank p.val M = 2}

/-- The set `τ₃(M) = {p ∈ σ(M)' | p ∈ π(M') and r_p(M) = 1}`. -/
@[expose] public def CFSG.section12Tau3Primes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∉ section10SigmaPrimes M ∧
      p ∈ subgroupPrimeSet (derivedSubgroup M) ∧ primeRank p.val M = 1}

/-- Prime-order subgroups of a subgroup, with the prime not specified. -/
@[expose] public def CFSG.section12PrimeOrderSubgroups (H : Subgroup G) :
    Set (Subgroup G) :=
  {X | X ≤ H ∧ ∃ p : Nat.Primes, Nat.card X = p.val}

/-- Rank-two elementary abelian `p`-subgroups of `H`, viewed in the ambient group. -/
@[expose] public def CFSG.section12RankTwoElementaryAbelianIn
    (p : Nat.Primes) (H : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ H ∧ A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G}

/-- A subgroup `K` is a Hall `π`-subgroup of `H`, both viewed in the same ambient group. -/
@[expose] public def CFSG.section12HallSubgroupIn
    (π : Set Nat.Primes) (K H : Subgroup G) : Prop :=
  ∃ _hKH : K ≤ H, IsHallSubgroup π (K.subgroupOf H)

/-- A subgroup `K` is a Sylow `p`-subgroup of `H`, both viewed in the same ambient group. -/
@[expose] public def CFSG.section12SylowSubgroupIn
    (p : Nat.Primes) (K H : Subgroup G) : Prop :=
  ∃ P : Sylow p.val H, section10AmbientSylowSubgroup H P = K

/-- The subgroup `Ω₁(H)`, viewed in the ambient group. -/
@[expose] public def CFSG.section12OmegaOneSubgroup
    (p : Nat.Primes) (H : Subgroup G) : Subgroup G :=
  (omega₁ (G := H) (p := p.val)).map H.subtype

/-- A complement relation inside a specified overgroup. -/
@[expose] public def CFSG.section12ComplementIn
    (H K L : Subgroup G) : Prop :=
  K ≤ H ∧ L ≤ H ∧ H = K ⊔ L ∧ Disjoint K L

/-- `E` is a complement of `M_σ` in `M`. -/
@[expose] public def CFSG.section12ComplementToMsigma
    (M E : Subgroup G) : Prop :=
  section12ComplementIn M (section10Msigma M) E

/-- The fixed Section 12 choices of `E`, `E₁₂`, `E₁`, `E₂`, and `E₃`. -/
@[expose] public def CFSG.section12EData
    (M E E₁₂ E₁ E₂ E₃ : Subgroup G) : Prop :=
  section12ComplementToMsigma M E ∧
    section12HallSubgroupIn (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E ∧
    section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ ∧
    section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂ ∧
    section12HallSubgroupIn (section12Tau3Primes M) E₃ E

/-- The prime support of a formal quotient `H/K`, recorded by the relative index. -/
@[expose] public def CFSG.section12QuotientPrimeSet
    (K H : Subgroup G) : Set Nat.Primes :=
  {q | ∃ _hKH : K ≤ H, q.val ∣ (K.subgroupOf H).index}

/-- An internal direct product statement for subgroups of a common ambient group. -/
@[expose] public def CFSG.section12InternalDirectProduct
    (K L H : Subgroup G) : Prop :=
  K ≤ H ∧ L ≤ H ∧ H = K ⊔ L ∧ Disjoint K L ∧
    K ≤ Subgroup.centralizer (L : Set G)

/-- The join `KR` is a Frobenius group with kernel `K` and complement `R`. -/
@[expose] public def CFSG.section12FrobeniusJoinWithKernel
    (K R : Subgroup G) : Prop :=
  IsFrobeniusGroupWithKernelComplement
    (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R))

/-- A subgroup has abelian Sylow `p`-subgroups. -/
@[expose] public def CFSG.section12HasAbelianSylowSubgroups
    (p : Nat.Primes) (H : Type*) [Group H] : Prop :=
  ∀ P : Sylow p.val H, IsMulCommutative (P : Subgroup H)

/-- A group has a nonabelian Sylow `p`-subgroup. -/
@[expose] public def CFSG.section12HasNonabelianSylowSubgroup
    (p : Nat.Primes) (H : Type*) [Group H] : Prop :=
  ∃ P : Sylow p.val H, ¬ IsMulCommutative (P : Subgroup H)

/-- Two ambient subgroups are not conjugate. -/
@[expose] public def CFSG.section12NotConjugate
    (H K : Subgroup G) : Prop :=
  ∀ g : G, H.conjBy g ≠ K

/-- The set of ideal primes of the ambient group, denoted `β(G)` in the text. -/
@[expose] public def CFSG.section12BetaPrimesOfGroup
    (G : Type*) [Group G] [Finite G] : Set Nat.Primes :=
  {p | section10IdealPrime p G}

end Notation

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_le_card {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_le_groupRank {R : Type*} [Group R] [Finite R] {q : ℕ}
    (hq : Nat.Prime q) :
    primeRank q R ≤ groupRank R := by
  let S : Set ℕ := {n : ℕ | ∃ q' : ℕ, Nat.Prime q' ∧ n ≤ primeRank q' R}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q', _hq', hnq'⟩
    exact hnq'.trans (section12_primeRank_le_card (R := R) q')
  have hmem : primeRank q R ∈ S := ⟨q, hq, le_rfl⟩
  simpa [groupRank, S] using (le_csSup hSbdd hmem)

omit [IsMinCE G] in
public theorem CFSG.section12_generatorRank_le_of_equiv {R S : Type*} [Group R] [Finite R]
    [Group S] [Finite S] (e : R ≃* S) :
    generatorRank S ≤ generatorRank R := by
  rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
  exact (Group.rank_congr e).ge

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_le_of_equiv {R S : Type*} [Group R] [Finite R]
    [Group S] [Finite S] (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' :=
      IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' :=
        Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      exact section12_generatorRank_le_of_equiv (R := A') (S := A) eA.symm
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
          n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      simpa [primeRank] using le_csSup
        (show BddAbove
            {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
              n ≤ generatorRank B} from
          ⟨Nat.card R, by
            intro n hn
            rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
            exact hnB.trans <|
              (section8_generatorRank_le_natCard B).trans
                (Subgroup.card_le_card_group B)⟩)
        hmem
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

omit [IsMinCE G] in
public theorem CFSG.section12_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank
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
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

omit [IsMinCE G] in
public theorem CFSG.section12_groupRank_le_of_equiv {R S : Type*} [Group R] [Finite R]
    [Group S] [Finite S] (e : R ≃* S) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section12_primeRank_le_card (R := S) q)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R :=
      (section12_primeRank_le_of_equiv (R := R) (S := S) q e).trans
        (section12_primeRank_le_groupRank (R := R) hq)
    rw [groupRank]
    exact hsSup_le.trans hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12Msigma_subgroupOf_eq {M : Subgroup G} :
    (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
  change (piCoreIn (section10SigmaPrimes M) M).subgroupOf M =
    piCore (section10SigmaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10SigmaPrimes M) M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12Malpha_subgroupOf_eq {M : Subgroup G} :
    (section10Malpha M).subgroupOf M = section10MalphaSubgroup M := by
  change (piCoreIn (section10AlphaPrimes M) M).subgroupOf M =
    piCore (section10AlphaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10AlphaPrimes M) M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_complement_to_msigma_isComplement'
    {M E : Subgroup G}
    (hcomp : section12ComplementToMsigma M E) :
    (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) := by
  classical
  rcases hcomp with ⟨hσM, hEM, hM, hdisj⟩
  have hσsub_eq : (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M :=
    section12Msigma_subgroupOf_eq (M := M)
  have hsup_local : E.subgroupOf M ⊔ section10MsigmaSubgroup M = ⊤ := by
    have hsup1 : (section10Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
      calc
        (section10Msigma M).subgroupOf M ⊔ E.subgroupOf M =
            (section10Msigma M ⊔ E).subgroupOf M := by
          symm
          exact
            Subgroup.subgroupOf_sup (A := section10Msigma M) (A' := E) (B := M) hσM hEM
        _ = ⊤ := by
          rw [← hM]
          simp
    simpa [hσsub_eq, sup_comm] using hsup1
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxE hxσ
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdisj
    · have hxσ' : x ∈ (section10Msigma M).subgroupOf M := by
        simpa [hσsub_eq] using hxσ
      simpa [Subgroup.mem_subgroupOf] using hxσ'
    · simpa [Subgroup.mem_subgroupOf] using hxE
  · simpa [hsup_local] using
      (Subgroup.mul_normal (E.subgroupOf M) (section10MsigmaSubgroup M)).symm

public theorem CFSG.section12_msigma_complement_isHall_sigma_compl
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    IsHallSubgroup (section10SigmaPrimes M)ᶜ (E.subgroupOf M) := by
  classical
  have hcomp' :
      (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hNhall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b hM).2
  refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ (E.subgroupOf M) ?_ ?_
  · intro q hqE hqσ
    have hqNidx : q.val ∣ (section10MsigmaSubgroup M).index := by
      simpa [hcomp'.index_eq_card] using hqE
    exact (hNhall.p_in_pi_of_p_dvd_index q hqNidx) hqσ
  · intro q hq_not_σc hqEidx
    have hqN : q.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      simpa [hcomp'.symm.index_eq_card] using hqEidx
    have hqσ : q ∈ section10SigmaPrimes M :=
      hNhall.p_in_pi_of_p_dvd_card q hqN
    exact hq_not_σc hqσ

public noncomputable def CFSG.section12QuotientEquivComplement
    {M E : Subgroup G}
    (hcomp : section12ComplementToMsigma M E) :
    M ⧸ section10MsigmaSubgroup M ≃* E :=
  ((section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp).QuotientMulEquiv).trans
    (Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hcomp.2.1)

public theorem CFSG.section12_groupRank_E_le_two
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    groupRank E ≤ 2 := by
  let eE : E.subgroupOf M ≃* E :=
    Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hcomp.2.1
  have hEsub_rank : groupRank (E.subgroupOf M) ≤ 2 :=
    section10_hall_compl_sigma_groupRank_le_two hM
      (section12_msigma_complement_isHall_sigma_compl hM hcomp)
  exact (section12_groupRank_le_of_equiv eE).trans hEsub_rank

public theorem CFSG.section12_solvable_of_complement
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    Group.IsSolvable E := by
  have hEM : E ≤ M := hcomp.2.1
  have hEproper : E ≠ ⊤ := by
    intro hEtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hEtop] using hEM
    exact hM.1 (top_le_iff.mp htop_le_M)
  exact IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_nilpotent_ambientDerivedSubgroup
    {E : Subgroup G}
    (hE' : Group.IsNilpotent (derivedSubgroup E)) :
    Group.IsNilpotent (ambientDerivedSubgroup E) := by
  exact Group.nilpotent_of_mulEquiv (G := derivedSubgroup E) (G' := ambientDerivedSubgroup E)
    (Subgroup.equivMapOfInjective (f := E.subtype) (derivedSubgroup E) E.subtype_injective)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambientDerivedSubgroup_le
    {E : Subgroup G} :
    ambientDerivedSubgroup E ≤ E := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact (y : E).property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambientDerivedSubgroup_mono {H K : Subgroup G} (hHK : H ≤ K) :
    ambientDerivedSubgroup H ≤ ambientDerivedSubgroup K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  let f : H →* K := H.subtype.codRestrict K (fun h => hHK h.property)
  have hyK : f y ∈ derivedSubgroup K := by
    exact (map_derivedSeries_le_derivedSeries f 1) (Subgroup.mem_map_of_mem f hy)
  change ((y : H) : G) ∈ ambientDerivedSubgroup K
  exact Subgroup.mem_map_of_mem K.subtype hyK

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambientDerivedSubgroup_subgroupOf_eq
    {E : Subgroup G} :
    (ambientDerivedSubgroup E).subgroupOf E = derivedSubgroup E := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ ambientDerivedSubgroup E at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := by
      apply Subtype.ext
      simpa using hyx
    simpa [hy_eq] using hy
  · intro hx
    change (x : G) ∈ ambientDerivedSubgroup E
    exact Subgroup.mem_map_of_mem E.subtype hx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambientDerivedSubgroup_eq_commutator {H : Subgroup G} :
    ambientDerivedSubgroup H = ⁅H, H⁆ := by
  rw [ambientDerivedSubgroup, derivedSubgroup, derivedSeries_one,
    Subgroup.map_subtype_commutator]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_normalIn_ambientDerivedSubgroup
    {E : Subgroup G} :
    section10NormalIn (ambientDerivedSubgroup E) E := by
  refine ⟨section12_ambientDerivedSubgroup_le, ?_⟩
  rw [section12_ambientDerivedSubgroup_subgroupOf_eq]
  infer_instance

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_quotient_mk_injective_on_complement
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) {x y : K}
    (hxy : (QuotientGroup.mk' N (x : R) : R ⧸ N) = QuotientGroup.mk' N (y : R)) :
    x = y := by
  have hdiv : (x : R) * (y : R)⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    simpa [map_mul, map_inv] using
      congrArg (fun q => q * (QuotientGroup.mk' N (y : R))⁻¹) hxy
  have hxyK : (x : R) * (y : R)⁻¹ ∈ K :=
    K.mul_mem x.property (K.inv_mem y.property)
  have htop : ((x : R) * (y : R)⁻¹ : R) = 1 :=
    Subgroup.disjoint_def.mp hcomp.disjoint hxyK hdiv
  exact Subtype.ext (mul_inv_eq_one.mp htop)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_quotient_equiv_complement_apply
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) (x : K) :
    hcomp.QuotientMulEquiv (QuotientGroup.mk' N (x : R)) = x := by
  apply section12_quotient_mk_injective_on_complement hcomp
  rw [Subgroup.IsComplement'.QuotientMulEquiv_apply]
  exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hcomp _

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_map_derived_quotient
    {R : Type*} [Group R] {N : Subgroup R} [N.Normal] :
    (derivedSubgroup R).map (QuotientGroup.mk' N) = derivedSubgroup (R ⧸ N) := by
  change (derivedSeries R 1).map (QuotientGroup.mk' N) = derivedSeries (R ⧸ N) 1
  exact map_derivedSeries_eq (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) 1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_map_derived_mulEquiv
    {R S : Type*} [Group R] [Group S] (e : R ≃* S) :
    (derivedSubgroup R).map e.toMonoidHom = derivedSubgroup S := by
  change (derivedSeries R 1).map e.toMonoidHom = derivedSeries S 1
  exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_complement_inf_derived_eq
    {R : Type*} [Group R] {K N : Subgroup R} [N.Normal]
    (hcomp : K.IsComplement' N) :
    K ⊓ derivedSubgroup R = (derivedSubgroup K).map K.subtype := by
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hx.1
    have hxder : x ∈ derivedSubgroup R := hx.2
    let q : R →* R ⧸ N := QuotientGroup.mk' N
    have hxq_der : q x ∈ derivedSubgroup (R ⧸ N) := by
      have hxmap : q x ∈ (derivedSubgroup R).map q := Subgroup.mem_map_of_mem q hxder
      change (QuotientGroup.mk' N) x ∈ derivedSubgroup (R ⧸ N)
      change (QuotientGroup.mk' N) x ∈ (derivedSubgroup R).map (QuotientGroup.mk' N) at hxmap
      rw [section12_map_derived_quotient (R := R) (N := N)] at hxmap
      exact hxmap
    let e : R ⧸ N ≃* K := hcomp.QuotientMulEquiv
    have hex_der : e (q x) ∈ derivedSubgroup K := by
      have hxmap : e (q x) ∈ (derivedSubgroup (R ⧸ N)).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hxq_der
      change hcomp.QuotientMulEquiv ((QuotientGroup.mk' N) x) ∈ derivedSubgroup K
      change hcomp.QuotientMulEquiv ((QuotientGroup.mk' N) x) ∈
        (derivedSubgroup (R ⧸ N)).map hcomp.QuotientMulEquiv.toMonoidHom at hxmap
      rw [section12_map_derived_mulEquiv (R := R ⧸ N) (S := K) hcomp.QuotientMulEquiv]
        at hxmap
      exact hxmap
    have heqx : e (q x) = ⟨x, hxK⟩ :=
      section12_quotient_equiv_complement_apply hcomp ⟨x, hxK⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    simpa [heqx] using hex_der
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    constructor
    · exact (y : K).property
    · exact (map_derivedSeries_le_derivedSeries K.subtype 1)
        (Subgroup.mem_map_of_mem K.subtype hy)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_complement_inter_ambientDerived_eq
    {M E : Subgroup G}
    (hcomp : section12ComplementToMsigma M E) :
    E ⊓ ambientDerivedSubgroup M = ambientDerivedSubgroup E := by
  classical
  have hEM : E ≤ M := hcomp.2.1
  have hlocal :
      E.subgroupOf M ⊓ derivedSubgroup M =
        (derivedSubgroup (E.subgroupOf M)).map (E.subgroupOf M).subtype :=
    section12_complement_inf_derived_eq
      (section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp)
  apply le_antisymm
  · intro x hx
    have hxE : x ∈ E := hx.1
    have hxMder : x ∈ ambientDerivedSubgroup M := hx.2
    let xm : M := ⟨x, hEM hxE⟩
    have hxlocal_der : xm ∈ derivedSubgroup M := by
      have : xm ∈ (ambientDerivedSubgroup M).subgroupOf M := hxMder
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using this
    have hxlocal_E : xm ∈ E.subgroupOf M := hxE
    have hxlocal_inf : xm ∈ E.subgroupOf M ⊓ derivedSubgroup M :=
      ⟨hxlocal_E, hxlocal_der⟩
    rw [hlocal] at hxlocal_inf
    rcases Subgroup.mem_map.mp hxlocal_inf with ⟨y, hy, hyx⟩
    let e : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM
    have hey : e y ∈ derivedSubgroup E := by
      have hmap_eq : (derivedSubgroup (E.subgroupOf M)).map e.toMonoidHom =
          derivedSubgroup E :=
        section12_map_derived_mulEquiv (R := E.subgroupOf M) (S := E) e
      have hmem : e y ∈ (derivedSubgroup (E.subgroupOf M)).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hy
      rw [hmap_eq] at hmem
      exact hmem
    change x ∈ ambientDerivedSubgroup E
    have hey_val : ((e y : E) : G) = x := by
      have hyxG : (((y : E.subgroupOf M) : M) : G) = x := congrArg Subtype.val hyx
      simpa [e, Subgroup.subgroupOfEquivOfLe] using hyxG
    rw [← hey_val]
    exact Subgroup.mem_map_of_mem E.subtype hey
  · intro x hx
    exact ⟨section12_ambientDerivedSubgroup_le hx,
      section12_ambientDerivedSubgroup_mono hEM hx⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_not_isCyclic_of_two_le_generatorRank
    {H : Type*} [Group H] [Finite H] (hHrank : 2 ≤ generatorRank H) :
    ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_generatorRank_le_primeRank_of_subgroup
    {R : Type*} [Group R] [Finite R] {q : ℕ} {A : Subgroup R}
    (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ primeRank q R := by
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A, hAp, hAcomm, le_rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isElementaryAbelian_map
    {p : ℕ} [Fact p.Prime] {R S : Type*} [Group R] [Group S]
    {A : Subgroup R} [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  exact IsElementaryAbelian.map (p := p) (A := A) f

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_of_isPGroup_of_mem
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {p : Nat.Primes}
    {P : Subgroup R} (hPp : IsPGroup p.val P) (hpπ : p ∈ π) :
    IsPiSubgroup (G := R) π P := by
  intro q hq
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases hPp.exists_card_eq with ⟨n, hn⟩
  have hq_dvd_p : q.val ∣ p.val := q.2.dvd_of_dvd_pow (by simpa [hn] using hq)
  have hqp : q = p := Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_dvd_p)
  simpa [hqp] using hpπ

public theorem CFSG.section12_piCore_isHallSubgroup_of_nilpotent
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    (hnil : Group.IsNilpotent R) :
    IsHallSubgroup π (piCore π R) := by
  classical
  refine isHallSubgroup_of (G := R) π (piCore π R) ?_ ?_
  · exact piCore_isPiSubgroup π
  · intro p hpπ hp_dvd_idx
    have : Fact p.val.Prime := ⟨p.2⟩
    let P : Sylow p.val R := Classical.choice (Sylow.nonempty (p := p.val) (G := R))
    have hPnorm : (P : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal hnil p.val P
    have hPπ : IsPiSubgroup (G := R) π (P : Subgroup R) :=
      section12_isPiSubgroup_of_isPGroup_of_mem P.isPGroup' hpπ
    have : (P : Subgroup R).Normal := hPnorm
    have hP_le_core : (P : Subgroup R) ≤ piCore π R :=
      le_piCore_of_normal_isPiSubgroup (G := R) π (P : Subgroup R) hPπ
    have hidx_dvd : (piCore π R).index ∣ (P : Subgroup R).index :=
      Subgroup.index_dvd_of_le hP_le_core
    exact P.not_dvd_index (hp_dvd_idx.trans hidx_dvd)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_normal_pSubgroup_le_sylow
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    {N : Subgroup R} [N.Normal] (hNp : IsPGroup p N) (P : Sylow p R) :
    N ≤ P := by
  classical
  obtain ⟨Q, hNQ⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hNp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R Q P
  have hN_le_gQ : N ≤ ((g • Q : Sylow p R) : Subgroup R) := by
    intro n hn
    rw [Sylow.coe_subgroup_smul]
    refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
      (S := (Q : Subgroup R)) (x := n)).2 ?_
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using ((inferInstance : N.Normal).conj_mem n hn g⁻¹)
    have hQ : g⁻¹ * n * g ∈ (Q : Subgroup R) := hNQ hconj
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ
  simpa [hg] using hN_le_gQ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_nilpotent_derivedSubgroup_of_ambient
    {E : Subgroup G}
    (hnil : Group.IsNilpotent (ambientDerivedSubgroup E)) :
    Group.IsNilpotent (derivedSubgroup E) := by
  let e : derivedSubgroup E ≃* ambientDerivedSubgroup E :=
    Subgroup.equivMapOfInjective (f := E.subtype) (derivedSubgroup E) E.subtype_injective
  exact Group.nilpotent_of_mulEquiv (G := ambientDerivedSubgroup E) (G' := derivedSubgroup E)
    e.symm

private theorem CFSG.section12_tau3_prime_mem_derived
    {M E : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hp : p ∈ section12Tau3Primes M) :
    p ∈ subgroupPrimeSet (derivedSubgroup E) := by
  classical
  rcases hp with ⟨hpσ, hpMder, _hprank⟩
  change p.val ∣ Nat.card (derivedSubgroup M) at hpMder
  let N : Subgroup M := section10MsigmaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  have hN_le_D : N ≤ D := (theorem_10_2_c (M := M) hM).2
  have hHallN : IsHallSubgroup (section10SigmaPrimes M) N :=
    (theorem_10_2_b (M := M) hM).2
  have hp_not_dvd_N : ¬ p.val ∣ Nat.card N := by
    intro hpdiv
    exact hpσ (hHallN.p_in_pi_of_p_dvd_card p hpdiv)
  have hp_dvd_D : p.val ∣ Nat.card D := by
    simpa [D] using hpMder
  have hNsub_card : Nat.card (N.subgroupOf D) = Nat.card N := by
    exact natCard_subgroupOf_eq N D hN_le_D
  have hp_dvd_quot : p.val ∣ Nat.card (D ⧸ N.subgroupOf D) := by
    have hmul : Nat.card D = Nat.card (D ⧸ N.subgroupOf D) * Nat.card (N.subgroupOf D) := by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := D) (s := N.subgroupOf D))
    have hp_mul : p.val ∣ Nat.card (D ⧸ N.subgroupOf D) * Nat.card (N.subgroupOf D) := by
      simpa [hmul] using hp_dvd_D
    rcases p.2.dvd_mul.mp hp_mul with hpquot | hpN
    · exact hpquot
    · exact False.elim (hp_not_dvd_N (by simpa [hNsub_card] using hpN))
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  have hcard_quot_map : Nat.card (D.map q) = Nat.card (D ⧸ N.subgroupOf D) := by
    simpa [q, D, N] using natCard_map_mk'_eq (K := D) (N := N)
  have hmap_derived : D.map q = derivedSubgroup (M ⧸ N) := by
    simpa [q, D, N] using section12_map_derived_quotient (R := M) (N := N)
  let e : M ⧸ N ≃* E := section12QuotientEquivComplement (M := M) (E := E) hcomp
  have hcard_E_der :
      Nat.card (derivedSubgroup E) = Nat.card (derivedSubgroup (M ⧸ N)) := by
    have hcard_map :
        Nat.card ((derivedSubgroup (M ⧸ N)).map e.toMonoidHom) =
          Nat.card (derivedSubgroup (M ⧸ N)) := by
      exact Subgroup.card_map_of_injective
        (K := derivedSubgroup (M ⧸ N)) (f := e.toMonoidHom) e.injective
    have hmap_eq :
        (derivedSubgroup (M ⧸ N)).map e.toMonoidHom = derivedSubgroup E :=
      section12_map_derived_mulEquiv (R := M ⧸ N) (S := E) e
    rw [hmap_eq] at hcard_map
    exact hcard_map
  change p.val ∣ Nat.card (derivedSubgroup E)
  rw [hcard_E_der, ← hmap_derived, hcard_quot_map]
  exact hp_dvd_quot

omit [IsMinCE G] in
public theorem CFSG.section12_tau3_primeRank_E_le_one
    {M E : Subgroup G} {p : Nat.Primes}
    (hcomp : section12ComplementToMsigma M E)
    (hp : p ∈ section12Tau3Primes M) :
    primeRank p.val E ≤ 1 := by
  rcases hp with ⟨_hpσ, _hpMder, hprank⟩
  have hEM : E ≤ M := hcomp.2.1
  let e : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM
  exact (section12_primeRank_le_of_equiv (R := E.subgroupOf M) (S := E) p.val e).trans
    (by simpa [hprank] using section8_primeRank_le_of_subgroup (S := E.subgroupOf M) p.val)

omit [IsMinCE G] in
public theorem CFSG.section12_sylow_cyclic_of_primeRank_le_one
    {E : Subgroup G} {p : Nat.Primes}
    (hpodd : p.val ≠ 2) (hrank : primeRank p.val E ≤ 1)
    (P : Sylow p.val E) :
    IsCyclic (P : Subgroup E) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  by_contra hPcyc
  have : Fact (IsPGroup p.val (P : Subgroup E)) := ⟨P.isPGroup'⟩
  obtain ⟨A, _hAnorm, hAcard, hAelem⟩ :=
    lemma_4_5_a (R := (P : Subgroup E)) (p := p.val) hpodd hPcyc
  have : IsElementaryAbelian p.val A := hAelem
  let Amap : Subgroup E := A.map (P : Subgroup E).subtype
  have hAmap_p : IsPGroup p.val Amap :=
    IsPGroup.map (IsElementaryAbelian.isPGroup p.val A) (P : Subgroup E).subtype
  have hAmap_comm : IsMulCommutative Amap := by
    simpa [Amap] using (Subgroup.map_isMulCommutative (f := (P : Subgroup E).subtype) (H := A))
  have hgen_A : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p.val) hAcard
  have hgen_eq : generatorRank Amap = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    let e : A ≃* Amap :=
      Subgroup.equivMapOfInjective (f := (P : Subgroup E).subtype) A
        (P : Subgroup E).subtype_injective
    exact (Group.rank_congr e).symm
  have hprime_ge : 2 ≤ primeRank p.val E := by
    exact hgen_A.trans (by
      simpa [hgen_eq] using
        section12_generatorRank_le_primeRank_of_subgroup
          (R := E) (q := p.val) (A := Amap) hAmap_p hAmap_comm)
  omega

public theorem CFSG.section12_tau3_sylow_le_derived
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnilE : Group.IsNilpotent (ambientDerivedSubgroup E))
    (hp : p ∈ section12Tau3Primes M)
    (P : Sylow p.val E) :
    (P : Subgroup E) ≤ derivedSubgroup E := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hcomp : section12ComplementToMsigma M E := hE.1
  have hpD : p ∈ subgroupPrimeSet (derivedSubgroup E) :=
    section12_tau3_prime_mem_derived hM hcomp hp
  change p.val ∣ Nat.card (derivedSubgroup E) at hpD
  have hpE : p.val ∣ Nat.card E := hpD.trans (Subgroup.card_subgroup_dvd_card (derivedSubgroup E))
  have hpG : p.val ∣ Nat.card G := hpE.trans (Subgroup.card_subgroup_dvd_card E)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  have hrank : primeRank p.val E ≤ 1 := section12_tau3_primeRank_E_le_one hcomp hp
  have hPcyc : IsCyclic (P : Subgroup E) :=
    section12_sylow_cyclic_of_primeRank_le_one hpodd hrank P
  rcases corollary_1_19_a (G := E) p.val P hPcyc with hbot | hle
  · exfalso
    let D : Subgroup E := derivedSubgroup E
    let Q : Sylow p.val D := Classical.choice (Sylow.nonempty (p := p.val) (G := D))
    have hQ_ne_bot : (Q : Subgroup D) ≠ ⊥ := Sylow.ne_bot_of_dvd_card (G := D) Q (by
      simpa [D] using hpD)
    let Qmap : Subgroup E := (Q : Subgroup D).map D.subtype
    have hQmap_ne_bot : Qmap ≠ ⊥ := by
      intro hQmap_bot
      have hQ_bot : (Q : Subgroup D) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := (Q : Subgroup D)) (f := D.subtype)
          D.subtype_injective).1 (by simpa [Qmap] using hQmap_bot)
      exact hQ_ne_bot hQ_bot
    have hQmap_p : IsPGroup p.val Qmap :=
      IsPGroup.map Q.isPGroup' D.subtype
    have hDnil : Group.IsNilpotent D :=
      section12_nilpotent_derivedSubgroup_of_ambient hnilE
    have hQ_normal_D : (Q : Subgroup D).Normal :=
      Group.IsNilpotent.sylow_normal hDnil p.val Q
    have : (Q : Subgroup D).Characteristic :=
      Sylow.characteristic_of_normal Q hQ_normal_D
    have : Qmap.Normal := by
      change ((Q : Subgroup D).map D.subtype).Normal
      infer_instance
    have hQmap_le_P : Qmap ≤ (P : Subgroup E) :=
      section12_normal_pSubgroup_le_sylow (p := p.val) hQmap_p P
    have hQmap_le_D : Qmap ≤ D := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQmap_le_inf : Qmap ≤ (P : Subgroup E) ⊓ D := by
      intro x hx
      exact ⟨hQmap_le_P hx, hQmap_le_D hx⟩
    have hQmap_le_bot : Qmap ≤ (⊥ : Subgroup E) := by
      rw [← hbot]
      simpa [D] using hQmap_le_inf
    exact hQmap_ne_bot (le_bot_iff.mp hQmap_le_bot)
  · exact hle

public theorem CFSG.section12_tau3_piCore_hall_in_E
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnilE : Group.IsNilpotent (ambientDerivedSubgroup E)) :
    IsHallSubgroup (section12Tau3Primes M)
      ((piCore (section12Tau3Primes M) (derivedSubgroup E)).map (derivedSubgroup E).subtype) := by
  classical
  let π : Set Nat.Primes := section12Tau3Primes M
  let D : Subgroup E := derivedSubgroup E
  let Dπ : Subgroup E := (piCore π D).map D.subtype
  have hDnil : Group.IsNilpotent D :=
    section12_nilpotent_derivedSubgroup_of_ambient hnilE
  have hDπHallD : IsHallSubgroup π (piCore π D) :=
    section12_piCore_isHallSubgroup_of_nilpotent hDnil
  have hDπ_le_D : Dπ ≤ D := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hDπ_subgroupOf_eq : Dπ.subgroupOf D = piCore π D := by
    change ((piCore π D).map D.subtype).comap D.subtype = piCore π D
    exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective (piCore π D)
  have hDπHallD' : IsHallSubgroup π (Dπ.subgroupOf D) := by
    simpa [hDπ_subgroupOf_eq] using hDπHallD
  refine isHallSubgroup_of (G := E) π Dπ ?_ ?_
  · intro q hqDπ
    have hcard : Nat.card (Dπ.subgroupOf D) = Nat.card Dπ :=
      natCard_subgroupOf_eq Dπ D hDπ_le_D
    exact hDπHallD'.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqDπ)
  · intro q hqπ hq_dvd_idx
    have hnot_dvd_Didx : ¬ q.val ∣ D.index := by
      intro hqDidx
      have : Fact q.val.Prime := ⟨q.2⟩
      let P : Sylow q.val E := Classical.choice (Sylow.nonempty (p := q.val) (G := E))
      have hP_le_D : (P : Subgroup E) ≤ D :=
        section12_tau3_sylow_le_derived (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hnilE hqπ P
      have hDidx_dvd_Pidx : D.index ∣ (P : Subgroup E).index :=
        Subgroup.index_dvd_of_le hP_le_D
      exact P.not_dvd_index (hqDidx.trans hDidx_dvd_Pidx)
    have hnot_dvd_rel : ¬ q.val ∣ Dπ.relIndex D := by
      intro hqrel
      exact (hDπHallD'.p_in_pi_of_p_dvd_index q hqrel) hqπ
    have hidx_eq : Dπ.relIndex D * D.index = Dπ.index :=
      Subgroup.relIndex_mul_index hDπ_le_D
    have hq_prod : q.val ∣ Dπ.relIndex D * D.index := by
      simpa [hidx_eq] using hq_dvd_idx
    rcases q.2.dvd_mul.mp hq_prod with hqrel | hqD
    · exact hnot_dvd_rel hqrel
    · exact hnot_dvd_Didx hqD

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_card_subgroupOf_eq {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  natCard_subgroupOf_eq H K hHK

public theorem CFSG.section12_sigmaPrimes_mem_of_alphaPrimes_mem
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) :
    p ∈ section10SigmaPrimes M := by
  classical
  have hpα_mem : p ∈ section10AlphaPrimes M := hpα
  rcases hpα with ⟨hpM, _hprank⟩
  change p.val ∣ Nat.card M at hpM
  let A : Subgroup M := section10MalphaSubgroup M
  let S : Subgroup M := section10MsigmaSubgroup M
  have hHallA : IsHallSubgroup (section10AlphaPrimes M) A :=
    (theorem_10_2_a (M := M) hM).2
  have hHallS : IsHallSubgroup (section10SigmaPrimes M) S :=
    (theorem_10_2_b (M := M) hM).2
  have hAS : A ≤ S := (theorem_10_2_c (M := M) hM).1
  have hp_not_idx_A : ¬ p.val ∣ A.index := by
    intro hpidx
    exact (hHallA.p_in_pi_of_p_dvd_index p hpidx) hpα_mem
  have hmulA : A.index * Nat.card A = Nat.card M :=
    Subgroup.index_mul_card (H := A)
  have hp_mul : p.val ∣ A.index * Nat.card A := by
    simpa [hmulA] using hpM
  rcases p.2.dvd_mul.mp hp_mul with hpidx | hpA
  · exact False.elim (hp_not_idx_A hpidx)
  · have hA_card_dvd_S : Nat.card A ∣ Nat.card S := by
      have hsub_dvd : Nat.card (A.subgroupOf S) ∣ Nat.card S :=
        Subgroup.card_subgroup_dvd_card (A.subgroupOf S)
      have hcard : Nat.card (A.subgroupOf S) = Nat.card A :=
        natCard_subgroupOf_eq _ _ hAS
      rwa [hcard] at hsub_dvd
    exact hHallS.p_in_pi_of_p_dvd_card p (hpA.trans hA_card_dvd_S)

public theorem CFSG.section12_not_sigma_of_mem_complement
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) {p : Nat.Primes}
    (hpE : p ∈ subgroupPrimeSet E) :
    p ∉ section10SigmaPrimes M := by
  classical
  change p.val ∣ Nat.card E at hpE
  let N : Subgroup M := section10MsigmaSubgroup M
  let Ec : Subgroup M := E.subgroupOf M
  have hHallN : IsHallSubgroup (section10SigmaPrimes M) N :=
    (theorem_10_2_b (M := M) hM).2
  have hcomp' : Ec.IsComplement' N :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hpEc : p.val ∣ Nat.card Ec := by
    have hcard : Nat.card Ec = Nat.card E :=
      natCard_subgroupOf_eq _ _ hcomp.2.1
    simpa [Ec, hcard] using hpE
  have hpNidx : p.val ∣ N.index := by
    simpa [hcomp'.index_eq_card] using hpEc
  intro hpσ
  exact (hHallN.p_in_pi_of_p_dvd_index p hpNidx) hpσ

omit [IsMinCE G] in
private theorem CFSG.section12_one_le_generatorRank_of_nontrivial
    {R : Type*} [Group R] [Finite R] [Nontrivial R] :
    1 ≤ generatorRank R := by
  classical
  rw [generatorRank_eq_group_rank]
  by_contra hlt
  have hrank0 : Group.rank R = 0 := by omega
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec R
  have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
  have hclosureS_bot : Subgroup.closure (S : Set R) = ⊥ := by
    simp [hSempty]
  have hbot_top : (⊥ : Subgroup R) = ⊤ := by
    rw [← hclosureS_bot, hSgen]
  have hsub : Subsingleton R := by
    refine ⟨fun x y => ?_⟩
    have hx : x = 1 := by
      have hxbot : x ∈ (⊥ : Subgroup R) := by
        rw [hbot_top]
        exact trivial
      simpa using hxbot
    have hy : y = 1 := by
      have hybot : y ∈ (⊥ : Subgroup R) := by
        rw [hbot_top]
        exact trivial
      simpa using hybot
    rw [hx, hy]
  exact not_subsingleton R hsub

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_pos_of_mem_subgroupPrimeSet
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hpR : p.val ∣ Nat.card R) :
    1 ≤ primeRank p.val R := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let P : Sylow p.val R := Classical.choice (Sylow.nonempty (p := p.val) (G := R))
  have hP_ne_bot : (P : Subgroup R) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := R) P hpR
  have : Nontrivial (P : Subgroup R) :=
    (Subgroup.nontrivial_iff_ne_bot (H := (P : Subgroup R))).2 hP_ne_bot
  let ZP : Subgroup (P : Subgroup R) := Subgroup.center (P : Subgroup R)
  have hZP_nontrivial : Nontrivial ZP :=
    IsPGroup.center_nontrivial (p := p.val) (G := (P : Subgroup R)) P.isPGroup'
  have hZP_ne_bot : ZP ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := ZP)).1 hZP_nontrivial
  let Z : Subgroup R := ZP.map (P : Subgroup R).subtype
  have hZp : IsPGroup p.val Z := by
    have hZPp : IsPGroup p.val ZP := P.isPGroup'.to_subgroup ZP
    exact IsPGroup.map hZPp (P : Subgroup R).subtype
  have hZcomm : IsMulCommutative Z := by
    simpa [Z, ZP] using
      (Subgroup.map_isMulCommutative (f := (P : Subgroup R).subtype)
        (H := Subgroup.center (P : Subgroup R)))
  have hZ_ne_bot : Z ≠ ⊥ := by
    intro hZbot
    have hZP_bot : ZP = ⊥ := by
      apply Subgroup.map_injective (P : Subgroup R).subtype_injective
      simpa [Z] using hZbot
    exact hZP_ne_bot hZP_bot
  have : Nontrivial Z :=
    (Subgroup.nontrivial_iff_ne_bot (H := Z)).2 hZ_ne_bot
  exact (section12_one_le_generatorRank_of_nontrivial (R := Z)).trans
    (section12_generatorRank_le_primeRank_of_subgroup (R := R) (q := p.val) hZp hZcomm)

public theorem CFSG.section12_prime_mem_tau_union_of_mem_E
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) {p : Nat.Primes}
    (hpE : p ∈ subgroupPrimeSet E) :
    p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M := by
  classical
  have hpM : p ∈ subgroupPrimeSet M :=
    section8_subgroupPrimeSet_mono hcomp.2.1 hpE
  have hpσ : p ∉ section10SigmaPrimes M :=
    section12_not_sigma_of_mem_complement hM hcomp hpE
  have hpos : 1 ≤ primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hle_two : primeRank p.val M ≤ 2 := by
    by_contra hnot
    have hgt : 2 < primeRank p.val M := by omega
    exact hpσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hpM, hgt⟩)
  have hrank : primeRank p.val M = 1 ∨ primeRank p.val M = 2 := by omega
  rcases hrank with hrank1 | hrank2
  · by_cases hpD : p ∈ subgroupPrimeSet (derivedSubgroup M)
    · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hpσ, hpD, hrank1⟩)
    · exact Or.inl (Or.inl (by simpa [section12Tau1Primes] using ⟨hpσ, hpD, hrank1⟩))
  · exact Or.inl (Or.inr (by simpa [section12Tau2Primes] using ⟨hpσ, hrank2⟩))

omit [IsMinCE G] in
public theorem CFSG.section12_card_eq_one_of_no_prime_dvd
    {R : Type*} [Group R] [Finite R]
    (h : ∀ p : Nat.Primes, ¬ p.val ∣ Nat.card R) :
    Nat.card R = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hpprime hpdiv
  exact h ⟨p, hpprime⟩ hpdiv

omit [IsMinCE G] in
private theorem CFSG.section12_not_dvd_card_of_mem_hall_bot
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {p : Nat.Primes}
    (hHall : IsHallSubgroup π (⊥ : Subgroup R)) (hpπ : p ∈ π) :
    ¬ p.val ∣ Nat.card R := by
  intro hpdiv
  have hpidx : p.val ∣ (⊥ : Subgroup R).index := by
    simpa [Subgroup.index_bot] using hpdiv
  exact (hHall.p_in_pi_of_p_dvd_index p hpidx) hpπ

private theorem CFSG.section12_complement_ne_bot
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    E ≠ ⊥ := by
  classical
  intro hEbot
  let N : Subgroup M := section10MsigmaSubgroup M
  let Ec : Subgroup M := E.subgroupOf M
  have hcomp' : Ec.IsComplement' N :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hEc_bot : Ec = ⊥ := by
    ext x
    constructor
    · intro hx
      change x = 1
      apply Subtype.ext
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [Ec, hEbot] using hx
      simpa using hxbot
    · intro hx
      change (x : G) ∈ E
      rw [hEbot]
      change (x : G) = 1
      exact congrArg Subtype.val (by simpa using hx)
  have hNtop : N = ⊤ := by
    have hcomp_bot : (⊥ : Subgroup M).IsComplement' N := by
      simpa [hEc_bot] using hcomp'
    exact Subgroup.isComplement'_bot_left.mp hcomp_bot
  have hder_top : derivedSubgroup M = ⊤ := by
    apply top_le_iff.mp
    rw [← hNtop]
    exact (theorem_10_2_c (M := M) hM).2
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have hMsigma_le_M : section10Msigma M ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hMsigma_bot : section10Msigma M = ⊥ := by
      exact le_bot_iff.mp (by simpa [hMbot] using hMsigma_le_M)
    exact (theorem_10_2_e (M := M) hM) hMsigma_bot
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot (H := M)).2 hM_ne_bot
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hcomm_lt : commutator M < (⊤ : Subgroup M) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
  have hcomm_top : commutator M = (⊤ : Subgroup M) := by
    change derivedSeries M 1 = ⊤ at hder_top
    rw [derivedSeries_one] at hder_top
    exact hder_top
  exact hcomm_lt.ne hcomm_top

public theorem CFSG.section12_ambientDerivedSubgroup_lt
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    ambientDerivedSubgroup E < E := by
  classical
  have hE_ne_bot : E ≠ ⊥ := section12_complement_ne_bot hM hcomp
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot (H := E)).2 hE_ne_bot
  have hsolvE : Group.IsSolvable E := section12_solvable_of_complement hM hcomp
  have hDlt : derivedSubgroup E < (⊤ : Subgroup E) := by
    change derivedSeries E 1 < ⊤
    rw [derivedSeries_one]
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := E)
  refine lt_of_le_of_ne section12_ambientDerivedSubgroup_le ?_
  intro hEq
  have hDtop : derivedSubgroup E = (⊤ : Subgroup E) := by
    have hsubtop : (ambientDerivedSubgroup E).subgroupOf E = ⊤ := by
      rw [hEq]
      exact Subgroup.subgroupOf_eq_top.2 le_rfl
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hsubtop
  exact hDlt.ne hDtop

omit [IsMinCE G] in
public theorem CFSG.section12_E12_eq_bot_of_E1_E2_eq_bot
    {M E E₁₂ E₁ E₂ : Subgroup G}
    (hE12 : section12HallSubgroupIn (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂)
    (hE2 : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂)
    (hE1bot : E₁ = ⊥) (hE2bot : E₂ = ⊥) :
    E₁₂ = ⊥ := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  have hE1sub_bot : E₁.subgroupOf E₁₂ = ⊥ := by
    simp [hE1bot]
  have hE2sub_bot : E₂.subgroupOf E₁₂ = ⊥ := by
    simp [hE2bot]
  have hHallE1bot : IsHallSubgroup (section12Tau1Primes M) (⊥ : Subgroup E₁₂) := by
    simpa [hE1sub_bot] using hHallE1
  have hHallE2bot : IsHallSubgroup (section12Tau2Primes M) (⊥ : Subgroup E₁₂) := by
    simpa [hE2sub_bot] using hHallE2
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro p hpdiv
  have hpdiv_sub : p.val ∣ Nat.card (E₁₂.subgroupOf E) := by
    simpa [natCard_subgroupOf_eq _ _ hE12E] using hpdiv
  have hpτ12 : p ∈ section12Tau1Primes M ∪ section12Tau2Primes M :=
    hHallE12.p_in_pi_of_p_dvd_card p hpdiv_sub
  rcases hpτ12 with hpτ1 | hpτ2
  · exact section12_not_dvd_card_of_mem_hall_bot hHallE1bot hpτ1 hpdiv
  · exact section12_not_dvd_card_of_mem_hall_bot hHallE2bot hpτ2 hpdiv

public theorem CFSG.section12_E3_eq_E_of_E12_eq_bot
    {M E E₁₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hE12 : section12HallSubgroupIn (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE3 : section12HallSubgroupIn (section12Tau3Primes M) E₃ E)
    (hE12bot : E₁₂ = ⊥) :
    E₃ = E := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hE12sub_bot : E₁₂.subgroupOf E = ⊥ := by
    simp [hE12bot]
  have hHallE12bot :
      IsHallSubgroup (section12Tau1Primes M ∪ section12Tau2Primes M)
        (⊥ : Subgroup E) := by
    simpa [hE12sub_bot] using hHallE12
  have hE3sub_top : E₃.subgroupOf E = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hqprime hqidx
    let p : Nat.Primes := ⟨q, hqprime⟩
    have hpidx : p.val ∣ (E₃.subgroupOf E).index := by
      simpa [p] using hqidx
    have hp_not_tau3 : p ∉ section12Tau3Primes M :=
      hHallE3.p_in_pi_of_p_dvd_index p hpidx
    have hpE : p ∈ subgroupPrimeSet E := by
      have hmul : (E₃.subgroupOf E).index * Nat.card (E₃.subgroupOf E) = Nat.card E :=
        Subgroup.index_mul_card (H := E₃.subgroupOf E)
      have hp_mul : p.val ∣ (E₃.subgroupOf E).index * Nat.card (E₃.subgroupOf E) :=
        dvd_mul_of_dvd_left hpidx _
      simpa [subgroupPrimeSet, hmul] using hp_mul
    have hpτ : p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
      section12_prime_mem_tau_union_of_mem_E hM hcomp hpE
    have hpτ12 : p ∈ section12Tau1Primes M ∪ section12Tau2Primes M := by
      rcases hpτ with hp12 | hp3
      · exact hp12
      · exact False.elim (hp_not_tau3 hp3)
    exact section12_not_dvd_card_of_mem_hall_bot hHallE12bot hpτ12 hpE
  exact le_antisymm hE3E (Subgroup.subgroupOf_eq_top.1 hE3sub_top)

omit [IsMinCE G] in
public theorem CFSG.section12_prime_dvd_card_of_nontrivial_pSubgroup
    {p : Nat.Primes} {B : Subgroup G}
    (hBp : IsPGroup p.val B) (hBnontrivial : Nontrivial B) :
    p.val ∣ Nat.card B := by
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := B) (hG := hBp)).1
      hBnontrivial with
    ⟨n, hn_pos, hcard⟩
  rw [hcard]
  exact dvd_pow_self p.val hn_pos.ne'

omit [IsMinCE G] in
private theorem CFSG.section12_prime_dvd_card_of_primeRank_pos
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hpos : 0 < primeRank p.val R) :
    p.val ∣ Nat.card R := by
  classical
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty :=
    ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := R), inferInstance, Nat.zero_le _⟩
  have hSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases hSup_mem with ⟨A, hAp, _hAcomm, hAgen⟩
  have hAgen_pos : 0 < generatorRank A := by
    have hSup_pos : 0 < sSup T := by
      simpa [primeRank, T] using hpos
    exact lt_of_lt_of_le hSup_pos hAgen
  have hAnontrivial : Nontrivial A := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have : Subsingleton A := hsub
    have hgen0 : generatorRank A = 0 := by
      rw [generatorRank_eq_group_rank]
      have : Group.FG A := inferInstance
      apply le_antisymm ?_ (Nat.zero_le _)
      refine Group.rank_le (G := A) (S := ∅) ?_
      rw [Finset.coe_empty, Subgroup.closure_empty]
      exact (Subsingleton.elim (⊤ : Subgroup A) ⊥).symm
    omega
  have : Fact p.val.Prime := ⟨p.property⟩
  have hpA : p.val ∣ Nat.card A := by
    rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := A) (hG := hAp)).1
        hAnontrivial with
      ⟨n, hn_pos, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val hn_pos.ne'
  exact hpA.trans (Subgroup.card_subgroup_dvd_card A)

public theorem CFSG.section12_prime_mem_E_of_mem_tau13
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) {p : Nat.Primes}
    (hp : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    p ∈ subgroupPrimeSet E := by
  classical
  have hpσc : p ∈ (section10SigmaPrimes M)ᶜ := by
    rw [Set.mem_compl_iff]
    rcases hp with hpτ1 | hpτ3
    · exact hpτ1.1
    · exact hpτ3.1
  have hpM : p ∈ subgroupPrimeSet M := by
    rcases hp with hpτ1 | hpτ3
    · have hpos : 0 < primeRank p.val M := by
        rw [hpτ1.2.2]
        decide
      exact section12_prime_dvd_card_of_primeRank_pos hpos
    · have hpambient : p ∈ subgroupPrimeSet (ambientDerivedSubgroup M) := by
        have hcardD :
            Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
              Nat.card (ambientDerivedSubgroup M) :=
          natCard_subgroupOf_eq _ _ section12_ambientDerivedSubgroup_le
        have hpambient_sub : p.val ∣
            Nat.card ((ambientDerivedSubgroup M).subgroupOf M) := by
          simpa [subgroupPrimeSet, section12_ambientDerivedSubgroup_subgroupOf_eq]
            using hpτ3.2.1
        simpa [subgroupPrimeSet, hcardD] using hpambient_sub
      exact section8_subgroupPrimeSet_mono section12_ambientDerivedSubgroup_le hpambient
  change p.val ∣ Nat.card M at hpM
  have hHall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (E.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hE.1
  have hp_not_index : ¬ p.val ∣ (E.subgroupOf M).index := by
    intro hpidx
    exact (hHall.p_in_pi_of_p_dvd_index p hpidx) hpσc
  have hp_prod : p.val ∣ (E.subgroupOf M).index * Nat.card (E.subgroupOf M) := by
    have hmul :
        (E.subgroupOf M).index * Nat.card (E.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := E.subgroupOf M)
    simpa [hmul] using hpM
  rcases p.property.dvd_or_dvd hp_prod with hpidx | hpEsub
  · exact False.elim (hp_not_index hpidx)
  · have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq _ _ hE.1.2.1
    simpa [subgroupPrimeSet, hcard] using hpEsub

omit [IsMinCE G] in
public theorem CFSG.section12_tau1_primeRank_E_le_one
    {M E : Subgroup G} {p : Nat.Primes}
    (hcomp : section12ComplementToMsigma M E)
    (hp : p ∈ section12Tau1Primes M) :
    primeRank p.val E ≤ 1 := by
  rcases hp with ⟨_hpσ, _hpMder, hprank⟩
  have hEM : E ≤ M := hcomp.2.1
  let e : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM
  exact (section12_primeRank_le_of_equiv (R := E.subgroupOf M) (S := E) p.val e).trans
    (by simpa [hprank] using section8_primeRank_le_of_subgroup (S := E.subgroupOf M) p.val)

public theorem CFSG.section12_isZGroup_of_prime_support_rank_le_one
    {E K : Subgroup G} {π : Set Nat.Primes}
    (hKE : K ≤ E)
    (hπ : ∀ p : Nat.Primes, p.val ∣ Nat.card K → p ∈ π)
    (hrank : ∀ p : Nat.Primes, p ∈ π → primeRank p.val E ≤ 1) :
    IsZGroup K := by
  classical
  refine ⟨fun q hq Q => ?_⟩
  let p : Nat.Primes := ⟨q, hq⟩
  have : Fact p.val.Prime := ⟨p.2⟩
  by_cases hpK : p.val ∣ Nat.card K
  · have hpπ : p ∈ π := hπ p hpK
    have hpG : p.val ∣ Nat.card G := hpK.trans (Subgroup.card_subgroup_dvd_card K)
    have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
    let f : K →* E := K.subtype.codRestrict E (fun x => hKE x.property)
    let Qmap : Subgroup E := (Q : Subgroup K).map f
    have hQmap_p : IsPGroup p.val Qmap :=
      IsPGroup.map (p := p.val) (H := (Q : Subgroup K)) Q.isPGroup' f
    obtain ⟨S, hQmap_le_S⟩ := IsPGroup.exists_le_sylow (G := E) (p := p.val) hQmap_p
    have hS_cyc : IsCyclic (S : Subgroup E) :=
      section12_sylow_cyclic_of_primeRank_le_one hpodd (hrank p hpπ) S
    have hQmap_cyc : IsCyclic Qmap := by
      let : IsCyclic (S : Subgroup E) := hS_cyc
      exact Subgroup.isCyclic_of_le hQmap_le_S
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hxy
    let e : (Q : Subgroup K) ≃* Qmap :=
      Subgroup.equivMapOfInjective (f := f) (Q : Subgroup K) hf_inj
    exact e.isCyclic.2 hQmap_cyc
  · have hQbot : (Q : Subgroup K) = ⊥ := by
      by_contra hQne
      have : Nontrivial (Q : Subgroup K) :=
        (Subgroup.nontrivial_iff_ne_bot (H := (Q : Subgroup K))).2 hQne
      have hpQ : p.val ∣ Nat.card (Q : Subgroup K) :=
        section12_prime_dvd_card_of_nontrivial_pSubgroup
          (p := p) (B := (Q : Subgroup K)) Q.isPGroup' inferInstance
      exact hpK (hpQ.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup K)))
    have : Subsingleton (Q : Subgroup K) := by
      rw [hQbot]
      infer_instance
    exact isCyclic_of_subsingleton (α := (Q : Subgroup K))

omit [IsMinCE G] in
public theorem CFSG.section12_E1_inf_ambientDerivedSubgroup_M_eq_bot
    {M E₁₂ E₁ : Subgroup G}
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂) :
    E₁ ⊓ ambientDerivedSubgroup M = ⊥ := by
  classical
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  let I : Subgroup G := E₁ ⊓ ambientDerivedSubgroup M
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro p hpdiv
  have hpE1 : p.val ∣ Nat.card E₁ := by
    have hsub_dvd : Nat.card (I.subgroupOf E₁) ∣ Nat.card E₁ :=
      Subgroup.card_subgroup_dvd_card (I.subgroupOf E₁)
    have hcard : Nat.card (I.subgroupOf E₁) = Nat.card I :=
      natCard_subgroupOf_eq _ _ inf_le_left
    have hpI : p.val ∣ Nat.card I := by
      simpa [I] using hpdiv
    have hpIsub : p.val ∣ Nat.card (I.subgroupOf E₁) := by
      rwa [hcard]
    exact hpIsub.trans hsub_dvd
  have hpτ1 : p ∈ section12Tau1Primes M :=
    hHallE1.p_in_pi_of_p_dvd_card p (by
      simpa [natCard_subgroupOf_eq _ _ hE1E12] using hpE1)
  have hp_not_derived : p ∉ subgroupPrimeSet (derivedSubgroup M) := hpτ1.2.1
  have hp_derived : p ∈ subgroupPrimeSet (derivedSubgroup M) := by
    have hsub_dvd : Nat.card (I.subgroupOf (ambientDerivedSubgroup M)) ∣
        Nat.card (ambientDerivedSubgroup M) :=
      Subgroup.card_subgroup_dvd_card (I.subgroupOf (ambientDerivedSubgroup M))
    have hcard : Nat.card (I.subgroupOf (ambientDerivedSubgroup M)) = Nat.card I :=
      natCard_subgroupOf_eq _ _ inf_le_right
    have hpI : p.val ∣ Nat.card I := by
      simpa [I] using hpdiv
    have hpIsub : p.val ∣ Nat.card (I.subgroupOf (ambientDerivedSubgroup M)) := by
      rwa [hcard]
    have hpambient : p.val ∣ Nat.card (ambientDerivedSubgroup M) :=
      hpIsub.trans hsub_dvd
    have hcardD :
        Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
          Nat.card (ambientDerivedSubgroup M) :=
      natCard_subgroupOf_eq _ _ section12_ambientDerivedSubgroup_le
    have hpambient_sub : p.val ∣ Nat.card ((ambientDerivedSubgroup M).subgroupOf M) := by
      rwa [hcardD]
    simpa [subgroupPrimeSet, section12_ambientDerivedSubgroup_subgroupOf_eq]
      using hpambient_sub
  exact hp_not_derived hp_derived

omit [IsMinCE G] in
public theorem CFSG.section12_E1_commutator_eq_bot
    {M E E₁₂ E₁ : Subgroup G}
    (hcomp : section12ComplementToMsigma M E)
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂) :
    ⁅E₁, E₁⁆ = ⊥ := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  have hE1M : E₁ ≤ M := hE1E12.trans (hE12E.trans hcomp.2.1)
  have hInfBot : E₁ ⊓ ambientDerivedSubgroup M = ⊥ :=
    section12_E1_inf_ambientDerivedSubgroup_M_eq_bot
      (M := M) (E₁₂ := E₁₂) (E₁ := E₁) ⟨hE1E12, hHallE1⟩
  apply bot_unique
  intro x hx
  have hxE1 : x ∈ E₁ := Subgroup.commutator_le_self E₁ hx
  have hxD1 : x ∈ ambientDerivedSubgroup E₁ := by
    simpa [section12_ambientDerivedSubgroup_eq_commutator] using hx
  have hxD : x ∈ ambientDerivedSubgroup M :=
    section12_ambientDerivedSubgroup_mono hE1M hxD1
  have hxinf : x ∈ E₁ ⊓ ambientDerivedSubgroup M := ⟨hxE1, hxD⟩
  simpa [hInfBot] using hxinf

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isMulCommutative_of_commutator_eq_bot
    {H : Subgroup G} (hcomm : ⁅H, H⁆ = ⊥) :
    IsMulCommutative H := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hyc : (y : G) ∈ Subgroup.centralizer (H : Set G) := hcomm y.property
  have hxy : (x : G) * y = y * x := by
    simpa [Subgroup.mem_centralizer_iff] using hyc x x.property
  exact hxy

end Section12

/-!
# lemma_12_1_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(a). -/
public theorem CFSG.lemma_12_1_a
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Group.IsNilpotent (ambientDerivedSubgroup E) := by
  classical
  have hcomp : section12ComplementToMsigma M E := hE.1
  have hsolv : Group.IsSolvable E := section12_solvable_of_complement hM hcomp
  have hodd : Odd (Nat.card E) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card E)
  have hrank : groupRank E ≤ 2 := section12_groupRank_E_le_two hM hcomp
  exact section12_nilpotent_ambientDerivedSubgroup
    (theorem_4_20_a (G := E) hsolv hodd (Or.inl hrank))

end Section12
