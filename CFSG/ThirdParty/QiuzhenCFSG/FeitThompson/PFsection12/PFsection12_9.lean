module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.9)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.9) -/

/-- Noncyclicity transfers between Sylow subgroups of the same finite group. -/
public theorem not_isCyclic_sylow_of_not_isCyclic_sylow
    {R : Type u} [Group R] [Finite R]
    {p : ℕ} (hp : Nat.Prime p)
    (P Q : Sylow p R)
    (hQnoncyc : ¬ IsCyclic (Q : Subgroup R)) :
    ¬ IsCyclic (P : Subgroup R) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hPcyc
  let e : (P : Subgroup R) ≃* (Q : Subgroup R) := Sylow.equiv P Q
  exact hQnoncyc (e.isCyclic.mp hPcyc)

/-- Transport a noncyclic Sylow subgroup across an explicit equivalence from a
quotient `M/K`.

This is the group-theoretic core used in the contrapositive of PF `(8.2.b)`:
once a Type-F complement has a noncyclic Sylow subgroup, the quotient `M/K`
has a noncyclic Sylow subgroup as well. -/
public theorem quotientHasNoncyclicSylow_of_quotient_mulEquiv
    {G Q : Type u} [Group G] [Finite G] [Group Q] [Finite Q]
    {K M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hKM : K ≤ M)
    (hN : (K.subgroupOf M).Normal)
    (e : M ⧸ K.subgroupOf M ≃* Q)
    (P : Sylow p Q)
    (hPnoncyc : ¬ IsCyclic (P : Subgroup Q)) :
    quotientHasNoncyclicSylow p K M := by
  classical
  haveI : (K.subgroupOf M).Normal := hN
  let Pbar : Sylow p (M ⧸ K.subgroupOf M) :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPbarNoncyc :
      ¬ IsCyclic (Pbar : Subgroup (M ⧸ K.subgroupOf M)) := by
    intro hPbarCyc
    let P' : Sylow p Q :=
      Pbar.mapSurjective (f := e.toMonoidHom) e.surjective
    have hP'Cyc : IsCyclic (P' : Subgroup Q) := by
      let ePbar :
          (Pbar : Subgroup (M ⧸ K.subgroupOf M)) ≃*
            (P' : Subgroup Q) :=
        Subgroup.equivMapOfInjective
          (f := e.toMonoidHom) (Pbar : Subgroup (M ⧸ K.subgroupOf M))
          e.injective
      exact ePbar.isCyclic.mp hPbarCyc
    exact hPnoncyc ((Sylow.equiv P P').isCyclic.mpr hP'Cyc)
  exact ⟨hKM, hN, Pbar, hPbarNoncyc⟩

/-- If the Type-F complement in a Type-I maximal subgroup has a noncyclic Sylow
subgroup, then the quotient by the Frobenius kernel has a noncyclic Sylow
subgroup.  This is the quotient-transfer part of the PF `(12.7)` contradiction
route. -/
public theorem quotientHasNoncyclicSylow_of_typeFData_noncyclic_sylow
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hF : Section8.typeFData M MF U U1 U0)
    (P : Sylow p U)
    (hPnoncyc : ¬ IsCyclic (P : Subgroup U)) :
    quotientHasNoncyclicSylow p MF M := by
  classical
  rcases hF with
    ⟨_hsolv, _hodd, hMF, _hMFne, _hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
  have hN : (MF.subgroupOf M).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have hcompLocal : (MF.subgroupOf M).IsComplement' (U.subgroupOf M) :=
    section12ComplementIn_left_normal_isComplement' hcomp hN
  let eQuot : M ⧸ MF.subgroupOf M ≃* U.subgroupOf M :=
    hcompLocal.symm.QuotientMulEquiv
  let eU : U.subgroupOf M ≃* U :=
    Subgroup.subgroupOfEquivOfLe (H := U) (K := M) hcomp.2.1
  exact
    quotientHasNoncyclicSylow_of_quotient_mulEquiv
      (K := MF) (M := M) hcomp.1 hN (eQuot.trans eU) P hPnoncyc

/-- Contrapositive of the PF `(8.2.b)` route used by PF `(12.7)`: a Type-F
datum which is not Frobenius supplies a prime with a noncyclic Sylow subgroup
in the quotient by the Frobenius kernel. -/
public theorem exists_quotientHasNoncyclicSylow_of_typeFData_not_frobenius
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hF : Section8.typeFData M MF U U1 U0)
    (hnot : ¬ Section7.frobeniusWithKernel M MF) :
    ∃ p : ℕ, Nat.Prime p ∧ quotientHasNoncyclicSylow p MF M := by
  classical
  by_contra hnone
  have hcyc :
      ∀ p : Nat.Primes, ∀ P : Sylow p.val U,
        IsCyclic (P : Subgroup U) := by
    intro p P
    by_contra hPnoncyc
    haveI : Fact p.val.Prime := ⟨p.property⟩
    exact hnone
      ⟨p.val, p.property,
        quotientHasNoncyclicSylow_of_typeFData_noncyclic_sylow
          (M := M) (MF := MF) (U := U) (U1 := U1) (U0 := U0)
          hF P hPnoncyc⟩
  exact hnot (frobeniusWithKernel_of_typeFData_cyclicSylow hF hcyc)

/-- A non-Frobenius Type-I maximal subgroup contributes a prime to the PF
Hypothesis `(12.8)` bad-prime set.

The remaining work needed to build the full `hypothesis_12_8_data` package for
PF `(12.7)` is the global minimal-prime choice together with the Section 8
`msChoiceSource` package. -/
public theorem exists_badPrimeForHypothesis12_of_typeIDefinitionData_not_frobenius
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeI : Section8.typeIDefinitionData M MF)
    (hnot : ¬ Section7.frobeniusWithKernel M MF) :
    ∃ p : ℕ, badPrimeForHypothesis12 G p := by
  classical
  rcases hTypeI with ⟨U, U1, U0, hF, _hCases⟩
  rcases exists_quotientHasNoncyclicSylow_of_typeFData_not_frobenius
      (M := M) (MF := MF) (U := U) (U1 := U1) (U0 := U0) hF hnot with
    ⟨p, hp, hquot⟩
  exact ⟨p, hp, M, MF, hM, hMF, ⟨U, U1, U0, hF, _hCases⟩, hquot⟩

/-- Build the full PF Hypothesis `(12.8)` package from a minimal bad prime and
the strengthened Section 8 source choice for the corresponding Type-I witness.

This isolates the remaining source-choice input in the proof of PF `(12.7)`:
once `M_s = M_F` is available for the bad-prime witness, the rest of the
Hypothesis `(12.8)` data is canonical. -/
public theorem exists_hypothesis_12_8_data_of_minimal_badPrimeForHypothesis12
    {G : Type u} [Group G] [Finite G]
    (p : ℕ)
    (hbad : badPrimeForHypothesis12 G p)
    (hmin : ∀ q : ℕ, badPrimeForHypothesis12 G q → p ≤ q)
    (hMs :
      ∀ M MF : Subgroup G,
        M ∈ section9MaximalSubgroups G →
          section16MFSubgroup M MF →
            Section8.typeIDefinitionData M MF →
              quotientHasNoncyclicSylow p MF M →
                Section8.msChoiceSource M MF MF) :
    ∃ M K K' P0 : Subgroup G, hypothesis_12_8_data M K K' P0 p := by
  classical
  have hbadFull : badPrimeForHypothesis12 G p := hbad
  rcases hbad with ⟨hp, M, MF, hM, hMF, hTypeI, hquot⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let pp : Nat.Primes := ⟨p, hp⟩
  let P : Sylow pp.val M := Classical.choice (Sylow.nonempty (p := pp.val) (G := M))
  let P0 : Subgroup G := section10AmbientSylowSubgroup M P
  refine ⟨M, MF, ambientDerivedSubgroup MF, P0, ?_⟩
  refine ⟨hp, hbadFull, hmin, hM, hMF, hTypeI, ?_, rfl, hquot, ?_⟩
  · exact hMs M MF hM hMF hTypeI hquot
  · exact ⟨P, rfl⟩

/-- Choose the global minimal bad prime and build PF Hypothesis `(12.8)`, once
the source-choice package is available for each bad-prime witness. -/
public theorem exists_hypothesis_12_8_data_of_badPrimeForHypothesis12_exists
    {G : Type u} [Group G] [Finite G]
    (hbadExists : ∃ p : ℕ, badPrimeForHypothesis12 G p)
    (hMs :
      ∀ p : ℕ, ∀ M MF : Subgroup G,
        badPrimeForHypothesis12 G p →
          M ∈ section9MaximalSubgroups G →
            section16MFSubgroup M MF →
              Section8.typeIDefinitionData M MF →
                quotientHasNoncyclicSylow p MF M →
                  Section8.msChoiceSource M MF MF) :
    ∃ M K K' P0 : Subgroup G, ∃ p : ℕ,
      hypothesis_12_8_data M K K' P0 p := by
  classical
  let p : ℕ := Nat.find hbadExists
  have hbad : badPrimeForHypothesis12 G p := Nat.find_spec hbadExists
  have hmin : ∀ q : ℕ, badPrimeForHypothesis12 G q → p ≤ q := by
    intro q hq
    exact Nat.find_min' hbadExists hq
  rcases exists_hypothesis_12_8_data_of_minimal_badPrimeForHypothesis12
      (G := G) p hbad hmin
      (fun M MF hM hMF hTypeI hquot => hMs p M MF hbad hM hMF hTypeI hquot) with
    ⟨M, K, K', P0, h128⟩
  exact ⟨M, K, K', P0, p, h128⟩

/-- If a prime is not in the prime support of a subgroup, then it is coprime
to the subgroup order. -/
public theorem prime_coprime_card_of_not_mem_subgroupPrimeSet
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} (hp : Nat.Prime p)
    (hnot : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet H) :
    Nat.Coprime p (Nat.card H) := by
  exact hp.coprime_iff_not_dvd.2 (by
    intro hdiv
    apply hnot
    change p ∣ Nat.card H
    exact hdiv)

/-- In the Hypothesis `(12.8)` setup, a prime producing a noncyclic Sylow
subgroup in `M/K` is outside the prime support of the Hall subgroup `K`. -/
public theorem theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (p : ℕ) (hp : Nat.Prime p)
    (hMF : section16MFSubgroup M K)
    (hnoncyc : quotientHasNoncyclicSylow p K M) :
    (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hHall : IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf M) :=
    section16MFSubgroup_subgroupOf_isHall hMF
  rcases hnoncyc with ⟨_hKM, hN, Q, hQnoncyc⟩
  haveI : (K.subgroupOf M).Normal := hN
  have hQnontr : Nontrivial (Q : Subgroup (M ⧸ K.subgroupOf M)) :=
    Nontrivial.of_not_isCyclic hQnoncyc
  have hp_dvd_Q : p ∣ Nat.card (Q : Subgroup (M ⧸ K.subgroupOf M)) := by
    rcases (IsPGroup.nontrivial_iff_card
        (p := p) (G := (Q : Subgroup (M ⧸ K.subgroupOf M))) (hG := Q.isPGroup')).mp
        hQnontr with ⟨n, hnpos, hcard⟩
    rcases n with _ | n
    · omega
    · rw [hcard]
      exact ⟨p ^ n, by rw [pow_succ']⟩
  have hp_dvd_quot : p ∣ Nat.card (M ⧸ K.subgroupOf M) :=
    hp_dvd_Q.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup (M ⧸ K.subgroupOf M)))
  have hp_dvd_index : p ∣ (K.subgroupOf M).index := by
    simpa [Subgroup.index_eq_card] using hp_dvd_quot
  exact hHall.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hp_dvd_index

/-- The quotient part of the first assertion of PF `(12.9)`: any Sylow
subgroup of `M/K` is noncyclic and has generator rank exactly `2`. -/
public theorem theorem_12_9_quotient_sylow_generatorRank_eq_two
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (p : ℕ) (hp : Nat.Prime p)
    (hquotRank : section16QuotientHasAbelianSylowRankAtMostTwo K M)
    (hnoncyc : quotientHasNoncyclicSylow p K M) :
    ∃ _ : K ≤ M, ∃ _ : (K.subgroupOf M).Normal,
      ∀ Pbar : Sylow p (M ⧸ K.subgroupOf M),
        IsMulCommutative (Pbar : Subgroup (M ⧸ K.subgroupOf M)) ∧
          generatorRank (Pbar : Subgroup (M ⧸ K.subgroupOf M)) = 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hquotRank with ⟨hKM, hN, hRankQ⟩
  haveI : (K.subgroupOf M).Normal := hN
  rcases hnoncyc with ⟨_hKMnc, _hNnc, Q, hQnoncyc⟩
  refine ⟨hKM, hN, ?_⟩
  intro Pbar
  have hPbarRank := hRankQ ⟨p, hp⟩ Pbar
  have hPbarNoncyc : ¬ IsCyclic (Pbar : Subgroup (M ⧸ K.subgroupOf M)) :=
    not_isCyclic_sylow_of_not_isCyclic_sylow hp Pbar Q hQnoncyc
  have hgen_ge :
      2 ≤ generatorRank (Pbar : Subgroup (M ⧸ K.subgroupOf M)) := by
    by_contra hnot
    have hle1 :
        generatorRank (Pbar : Subgroup (M ⧸ K.subgroupOf M)) ≤ 1 := by
      omega
    exact hPbarNoncyc (isCyclic_of_generatorRank_le_one hle1)
  exact ⟨hPbarRank.1, le_antisymm hPbarRank.2 hgen_ge⟩

/-- In the PF `(12.9)` setup, the Hall subgroup `K` meets a chosen Sylow
`p`-subgroup of `M` trivially. -/
public theorem theorem_12_9_sylow_inf_mf_eq_bot
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (p : ℕ) (hp : Nat.Prime p)
    (hMF : section16MFSubgroup M K)
    (hnoncyc : quotientHasNoncyclicSylow p K M)
    (P : Sylow p M) :
    K.subgroupOf M ⊓ (P : Subgroup M) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K :=
    theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
      M K p hp hMF hnoncyc
  have hcopK : Nat.Coprime p (Nat.card K) :=
    prime_coprime_card_of_not_mem_subgroupPrimeSet hp hnot
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M (section16MFSubgroup_le hMF)
  rcases P.isPGroup'.exists_card_eq with ⟨n, hPcard⟩
  have hcop :
      Nat.Coprime (Nat.card (K.subgroupOf M)) (Nat.card (P : Subgroup M)) := by
    rw [hKcard, hPcard]
    exact Nat.Coprime.symm (Nat.Coprime.pow_left n hcopK)
  exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot

/-- Transfer exact generator rank two and commutativity across a multiplicative
equivalence, returning the Section 12 group-rank formulation. -/
public theorem theorem_12_9_rank_two_of_mulEquiv
    {R S : Type u} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S)
    (hcommS : IsMulCommutative S)
    (hgenS : generatorRank S = 2)
    {p : ℕ} [Fact p.Prime] (hRp : IsPGroup p R) :
    IsMulCommutative R ∧ groupRank R = 2 := by
  classical
  have hcommR : IsMulCommutative R := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply e.injective
    calc
      e (x * y) = e x * e y := e.map_mul x y
      _ = e y * e x := hcommS.is_comm.comm _ _
      _ = e (y * x) := (e.map_mul y x).symm
  have hgen_le : generatorRank R ≤ 2 := by
    have hle : generatorRank R ≤ generatorRank S :=
      section12_generatorRank_le_of_equiv e.symm
    exact hle.trans (by simp [hgenS])
  have hgen_ge : 2 ≤ generatorRank R := by
    have hle : generatorRank S ≤ generatorRank R :=
      section12_generatorRank_le_of_equiv e
    simpa [hgenS] using hle
  have hgroup_le : groupRank R ≤ 2 :=
    (groupRank_le_generatorRank_of_commutative_pgroup (p := p) hRp hcommR).trans hgen_le
  have hgroup_ge : 2 ≤ groupRank R := by
    haveI : Fact (IsPGroup p R) := ⟨hRp⟩
    exact hgen_ge.trans (generatorRank_le_groupRank_of_commutative_pgroup (p := p) R)
  exact ⟨hcommR, le_antisymm hgroup_le hgroup_ge⟩


/-- Source-data endpoint for Peterfalvi `(12.9)`.

This projects the fully packaged source proof of the `(8.17)/(8.11)` and
centralizer steps to the public existential conclusion. -/
public theorem theorem_12_9_of_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 : Subgroup G)
    (p : ℕ)
    (hsrc : theorem_12_9_source_data M K p)
    (h128 : hypothesis_12_8_data M K K' P0 p) :
    ∃ (L LF Ls : Subgroup G) (x : G),
      theorem_12_9_data M K K' P0 L LF Ls x p :=
  hsrc K' P0 h128

private theorem theorem_12_9_isMulCommutative_of_mulEquiv
    {R S : Type*} [Group R] [Group S]
    (e : R ≃* S)
    (hS : IsMulCommutative S) :
    IsMulCommutative R := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.injective
  calc
    e (x * y) = e x * e y := e.map_mul x y
    _ = e y * e x := hS.is_comm.comm _ _
    _ = e (y * x) := (e.map_mul y x).symm

private theorem theorem_12_9_hasAbelianSylowRankAtMostTwo_of_mulEquiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S)
    (hS : section16HasAbelianSylowRankAtMostTwo S) :
    section16HasAbelianSylowRankAtMostTwo R := by
  classical
  intro p P
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let f : R →* S := e.toMonoidHom
  let Q : Sylow p.val S := P.mapSurjective (f := f) e.surjective
  have hQ := hS p Q
  change IsMulCommutative ((P : Subgroup R).map f) ∧
    generatorRank ((P : Subgroup R).map f) ≤ 2 at hQ
  let ePmap : (P : Subgroup R) ≃* ((P : Subgroup R).map f) :=
    Subgroup.equivMapOfInjective (f := f) (P : Subgroup R) e.injective
  have hQmap_comm : IsMulCommutative ((P : Subgroup R).map f) := hQ.1
  have hcomm : IsMulCommutative (P : Subgroup R) :=
    theorem_12_9_isMulCommutative_of_mulEquiv ePmap hQmap_comm
  have hrank : generatorRank (P : Subgroup R) ≤ 2 := by
    have hle :
        generatorRank (P : Subgroup R) ≤
          generatorRank ((P : Subgroup R).map f) :=
      generatorRank_le_of_equiv ePmap.symm
    exact hle.trans hQ.2
  exact ⟨hcomm, hrank⟩

/-- PF `(8.12)(a)`, applied to source Type-I data, gives the quotient Sylow-rank
input needed in PF `(12.9)` without using the BG16 Type-I predicate. -/
public theorem theorem_12_9_quotient_sylow_rank_of_typeI_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K : Subgroup G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M K)
    (hMs : Section8.msChoiceSource M K K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    section16QuotientHasAbelianSylowRankAtMostTwo K M := by
  classical
  let A : Set G := Section8.section8CentralizerUnion M K
  let A1 : Set G := Section8.a1Set K
  have hTypeI_copy : Section8.typeIDefinitionData M K := hTypeI
  rcases hTypeI with ⟨U, U1, U0, hF, hCases⟩
  have hSrc :
      Section8.theorem_8_12_source_data M K U K A A A1 := by
    refine ⟨?_, ?_⟩
    · refine ⟨hM, hMF, hMs, rfl, Or.inl ?_⟩
      exact ⟨hTypeI_copy, rfl, rfl⟩
    · exact Or.inl ⟨⟨U1, U0, hF, hCases⟩, rfl, rfl⟩
  have hmin : IsMinCE G := inferInstance
  have h812 : Section8.theorem_8_12_source_conclusion M K U A A1 :=
    Section8.theorem_8_12 M K U K A A A1 hmin hSrc
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsrc, _hKne, _hKlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
  have hKnorm : (K.subgroupOf M).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  haveI : (K.subgroupOf M).Normal := hKnorm
  have hcompLocal : (K.subgroupOf M).IsComplement' (U.subgroupOf M) :=
    section12ComplementIn_left_normal_isComplement' hcomp hKnorm
  let eQuot : M ⧸ K.subgroupOf M ≃* U.subgroupOf M :=
    hcompLocal.symm.QuotientMulEquiv
  have hRankUsub : section16HasAbelianSylowRankAtMostTwo (U.subgroupOf M) :=
    theorem_12_9_hasAbelianSylowRankAtMostTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hcomp.2.1) h812.1
  have hRankQuot : section16HasAbelianSylowRankAtMostTwo (M ⧸ K.subgroupOf M) :=
    theorem_12_9_hasAbelianSylowRankAtMostTwo_of_mulEquiv eQuot hRankUsub
  exact ⟨hcomp.1, hKnorm, hRankQuot⟩

/-- Quotient-to-ambient Sylow transfer used in the first assertion of
PF `(12.9)`.

This isolates the group-theoretic step: a noncyclic Sylow subgroup of
`M/K`, together with the PF `(8.12)(a)` quotient Sylow rank bound, forces the
chosen ambient Sylow subgroup `P0` of `M` to be abelian of exact rank `2`. -/
public theorem theorem_12_9_p0_rank_two_of_quotient_rank
    {G : Type u} [Group G] [Finite G]
    (M K P0 : Subgroup G)
    (p : ℕ) (hp : Nat.Prime p)
    (hMF : section16MFSubgroup M K)
    (hquotRank : section16QuotientHasAbelianSylowRankAtMostTwo K M)
    (hnoncyc : quotientHasNoncyclicSylow p K M)
    (hP0 : section12SylowSubgroupIn ⟨p, hp⟩ P0 M) :
    IsMulCommutative P0 ∧ groupRank P0 = 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hP0 with ⟨P, rfl⟩
  rcases theorem_12_9_quotient_sylow_generatorRank_eq_two
      M K p hp hquotRank hnoncyc with
    ⟨hKM, hN, hquot⟩
  haveI : (K.subgroupOf M).Normal := hN
  let q : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Pbar : Sylow p (M ⧸ K.subgroupOf M) :=
    P.mapSurjective (f := q) (QuotientGroup.mk'_surjective (K.subgroupOf M))
  have hPbar := hquot Pbar
  have hKP_bot :
      K.subgroupOf M ⊓ (P : Subgroup M) = ⊥ :=
    theorem_12_9_sylow_inf_mf_eq_bot M K p hp hMF hnoncyc P
  let ePbar : (P : Subgroup M) ≃* ((P : Subgroup M).map q) :=
    Section6.theorem_6_8_map_mk'_equiv_of_inf_eq_bot
      (P : Subgroup M) (K.subgroupOf M) (by simpa [inf_comm] using hKP_bot)
  let eP0 : (P : Subgroup M) ≃* section10AmbientSylowSubgroup M P :=
    Subgroup.equivMapOfInjective
      (f := M.subtype) (P : Subgroup M) M.subtype_injective
  let eP0Pbar : section10AmbientSylowSubgroup M P ≃* (Pbar : Subgroup (M ⧸ K.subgroupOf M)) := by
    exact (eP0.symm.trans ePbar).trans (MulEquiv.subgroupCongr (by rfl))
  have hP0p : IsPGroup p (section10AmbientSylowSubgroup M P) :=
    section11_ambientSylow_isPGroup M P
  exact theorem_12_9_rank_two_of_mulEquiv eP0Pbar hPbar.1 hPbar.2 hP0p


/-- First assertion of Peterfalvi `(12.9)`: from PF `(8.12)(a)` and
Hypothesis `(12.8)`, the chosen Sylow subgroup `P0` is abelian of rank `2`. -/
public theorem theorem_12_9_p0_rank_two
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 : Subgroup G)
    (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p) :
    IsMulCommutative P0 ∧ groupRank P0 = 2 := by
  rcases h128 with
    ⟨hp, _hbad, _hmin, hM, hMF, hTypeI, hMs, _hK', hnoncyc, hP0⟩
  have hquotRank : section16QuotientHasAbelianSylowRankAtMostTwo K M :=
    theorem_12_9_quotient_sylow_rank_of_typeI_source M K hM hMF hMs hTypeI
  exact theorem_12_9_p0_rank_two_of_quotient_rank M K P0 p hp hMF
    hquotRank hnoncyc hP0

/-- The PF `(8.17.a)` maximal-overgroup step in PF `(12.9)`, constructed
directly from a Sylow overgroup of `P0` and the book-facing PF `(8.10)`
choice of `L_s`. -/
public theorem theorem_12_9_exists_maximal_msChoice_containing_p0
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (P0 : Subgroup G) (p : ℕ) (hp : Nat.Prime p)
    (hP0p : IsPGroup p P0) (hP0rank : groupRank P0 = 2) :
    ∃ L LF Ls : Subgroup G,
      L ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup L LF ∧
        Section8.msChoice L LF Ls ∧ P0 ≤ Ls := by
  classical
  let pp : Nat.Primes := ⟨p, hp⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hP0ne : P0 ≠ ⊥ := by
    intro hbot
    have hcyc : IsCyclic P0 := by
      rw [hbot]
      infer_instance
    letI : IsCyclic P0 := hcyc
    have hle : groupRank P0 ≤ 1 := groupRank_le_one_of_isCyclic P0
    omega
  rcases IsPGroup.exists_le_sylow (G := G) (p := p) hP0p with ⟨Q, hP0Q⟩
  have hQne : (Q : Subgroup G) ≠ ⊥ := by
    intro hQbot
    exact hP0ne (bot_unique (hP0Q.trans (le_of_eq hQbot)))
  have hnorm_ne_top :
      Subgroup.normalizer ((Q : Subgroup G) : Set G) ≠ ⊤ := by
    simpa [pp] using
      (section10_sylow_normalizer_ne_top_of_ne_bot (G := G) (p := pp) Q hQne)
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hnorm_ne_top with ⟨L, hL, hnormL⟩
  have hQleL : (Q : Subgroup G) ≤ L := Subgroup.le_normalizer.trans hnormL
  have hP0L : P0 ≤ L := hP0Q.trans hQleL
  rcases section16_exists_mfSubgroup (G := G) L with ⟨LF, hLF⟩
  have hChoice : ∃ Ls : Subgroup G, Section8.msChoice L LF Ls := by
    rcases section16_type_exhaustive_of_maximal (G := G) hL hLF with
      hI | hII | hIII | hIV | hV
    · exact ⟨LF, Or.inl ⟨Or.inl hI, rfl⟩⟩
    · exact ⟨LF, Or.inl ⟨Or.inr (Or.inl hII), rfl⟩⟩
    · exact ⟨ambientDerivedSubgroup L, Or.inr ⟨Or.inl hIII, rfl⟩⟩
    · exact ⟨ambientDerivedSubgroup L, Or.inr ⟨Or.inr hIV, rfl⟩⟩
    · exact ⟨LF, Or.inl ⟨Or.inr (Or.inr hV), rfl⟩⟩
  rcases hChoice with ⟨Ls, hLs⟩
  have hLs_eq : Ls = section10Msigma L :=
    Section8.theorem_8_11_msChoice_eq_msigma (G := G) hL hLF hLs
  let QL : Sylow pp.val L := Q.subtype hQleL
  have hQLmap : section10AmbientSylowSubgroup L QL = (Q : Subgroup G) := by
    change Subgroup.map L.subtype ((Q : Subgroup G).subgroupOf L) = (Q : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hQleL
  have hpQ : pp ∈ subgroupPrimeSet (Q : Subgroup G) := by
    have hQnontrivial : Nontrivial (Q : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot (H := (Q : Subgroup G))).2 hQne
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Q) (hG := Q.isPGroup')).mp
        hQnontrivial with ⟨n, hnpos, hcard⟩
    rw [subgroupPrimeSet, hcard]
    exact dvd_pow_self p hnpos.ne'
  have hpL : pp ∈ subgroupPrimeSet L :=
    section8_subgroupPrimeSet_mono hQleL hpQ
  have hpSigma : pp ∈ section10SigmaPrimes L := by
    refine ⟨hpL, QL, ?_⟩
    simpa [hQLmap] using hnormL
  let P0L : Subgroup L := P0.subgroupOf L
  have hP0Lp : IsPGroup p P0L :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0L).symm
  have hP0Lle : P0L ≤ section10MsigmaSubgroup L := by
    exact section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := L) (π := section10SigmaPrimes L) (H := section10MsigmaSubgroup L)
      (A := P0L) (p := pp) (theorem_10_2_b (G := G) hL).2 hpSigma
      (by simpa [pp] using hP0Lp)
  have hP0sigma : P0 ≤ section10Msigma L := by
    have hmap :
        P0L.map L.subtype ≤ (section10MsigmaSubgroup L).map L.subtype :=
      Subgroup.map_mono hP0Lle
    have hmapP0 : P0L.map L.subtype = P0 :=
      Subgroup.map_subgroupOf_eq_of_le hP0L
    have hmapSigma :
        (section10MsigmaSubgroup L).map L.subtype = section10Msigma L := rfl
    rw [hmapP0, hmapSigma] at hmap
    exact hmap
  exact ⟨L, LF, Ls, hL, hLF, hLs, by simpa [hLs_eq] using hP0sigma⟩

/-- The subgroup `Omega_1(P0)` in PF `(12.9)` is elementary abelian and
noncyclic. -/
public theorem theorem_12_9_omega_one_noncyclic
    {G : Type u} [Group G] [Finite G]
    (P0 : Subgroup G) (p : ℕ) (hp : Nat.Prime p)
    (hP0p : IsPGroup p P0) (hP0comm : IsMulCommutative P0)
    (hP0rank : groupRank P0 = 2) :
    IsElementaryAbelian p (section12OmegaOneSubgroup ⟨p, hp⟩ P0) ∧
      ¬ IsCyclic (section12OmegaOneSubgroup ⟨p, hp⟩ P0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative P0 := hP0comm
  letI : Fact (IsPGroup p P0) := ⟨hP0p⟩
  have hgen : generatorRank P0 = 2 := by
    apply le_antisymm
    · exact
        (generatorRank_le_groupRank_of_commutative_pgroup (p := p) P0).trans_eq
          hP0rank
    · rw [← hP0rank]
      exact groupRank_le_generatorRank_of_commutative_pgroup hP0p hP0comm
  have hOmegaElem : IsElementaryAbelian p (omega₁ (G := P0) (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative P0
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  have hP1Elem : IsElementaryAbelian p P1 := by
    letI : IsElementaryAbelian p (omega₁ (G := P0) (p := p)) := hOmegaElem
    exact section11_isElementaryAbelian_map
      (G := P0) (p := p) (A := omega₁ (G := P0) (p := p)) P0.subtype
  have hP1card : Nat.card P1 = p ^ 2 := by
    calc
      Nat.card P1 = Nat.card (omega₁ (G := P0) (p := p)) := by
        exact Subgroup.card_map_of_injective
          (K := omega₁ (G := P0) (p := p)) (f := P0.subtype)
          P0.subtype_injective
      _ = p ^ generatorRank P0 :=
        omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) P0
      _ = p ^ 2 := by rw [hgen]
  letI : IsElementaryAbelian p P1 := hP1Elem
  have hgenP1 : 2 ≤ generatorRank P1 :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq hP1card
  exact ⟨hP1Elem, section12_not_isCyclic_of_two_le_generatorRank hgenP1⟩

/-- The BG Proposition 1.16 step in PF `(12.9)`: some nonidentity element of
the elementary abelian subgroup has a centralizer in `K` not contained in
`K'`. -/
public theorem theorem_12_9_exists_centralizer_witness
    {G : Type u} [Group G] [Finite G]
    (M K K' P1 : Subgroup G) (p : ℕ) (hp : Nat.Prime p)
    (hMF : section16MFSubgroup M K) (hP1M : P1 ≤ M)
    (hP1Elem : IsElementaryAbelian p P1) (hP1noncyc : ¬ IsCyclic P1)
    (hcop : Nat.Coprime p (Nat.card K))
    (hKsolv : Group.IsSolvable K) (hKne : K ≠ ⊥)
    (hK' : K' = ambientDerivedSubgroup K) :
    ∃ x : G, x ∈ P1 ∧ x ≠ 1 ∧ ¬ elementCentralizerIn K x ≤ K' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : IsElementaryAbelian p P1 := hP1Elem
  letI : CommGroup P1 := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup p P1) := ⟨IsElementaryAbelian.isPGroup p P1⟩
  have hKleM : K ≤ M := section16MFSubgroup_le hMF
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleM).1
      (section16MFSubgroup_subgroupOf_normal hMF)
  have hP1normK : P1 ≤ Subgroup.normalizer (K : Set G) :=
    hP1M.trans hMnormK
  letI : Subgroup.Normalizes P1 K := ⟨hP1normK⟩
  have hfix_top :
      (⨆ (a : P1) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K) = ⊤ := by
    simpa using proposition_1_16_a (G := K) (A := P1) p hcop hP1noncyc
  by_contra hno
  have hcentralizers :
      ∀ a : G, a ∈ P1 → a ≠ 1 → elementCentralizerIn K a ≤ K' := by
    intro a ha hane
    by_contra hnot
    exact hno ⟨a, ha, hane, hnot⟩
  have hfixed_map_le :
      ∀ a : P1, ∀ ha_ne : a ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map K.subtype ≤ K' := by
    intro a ha_ne
    have haG_ne : (a : G) ≠ 1 := by
      intro haG
      exact ha_ne (Subtype.ext haG)
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K =
          (elementCentralizerIn K (a : G)).subgroupOf K := by
      simpa using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
          K P1 hP1normK a
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map K.subtype =
          elementCentralizerIn K (a : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map K.subtype =
            ((elementCentralizerIn K (a : G)).subgroupOf K).map K.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn K (a : G) ⊓ K := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn K (a : G) := inf_eq_left.2 inf_le_left
    rw [hfix_map]
    exact hcentralizers (a : G) a.2 haG_ne
  have htop_map_K : (⊤ : Subgroup K).map K.subtype = K := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
  have hKleK' : K ≤ K' := by
    calc
      K = (⊤ : Subgroup K).map K.subtype := htop_map_K.symm
      _ =
          (⨆ (a : P1) (_ : a ≠ 1),
            fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥K).map K.subtype := by
            simp [hfix_top]
      _ ≤ K' := by
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro a
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro ha_ne
        exact hfixed_map_le a ha_ne
  have hDlt : ambientDerivedSubgroup K < K := by
    let : Group.IsSolvable K := hKsolv
    haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKne
    have hcomm_lt : derivedSubgroup K < (⊤ : Subgroup K) := by
      simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)
    refine lt_of_le_of_ne section12_ambientDerivedSubgroup_le ?_
    intro hEq
    have hDtop : derivedSubgroup K = (⊤ : Subgroup K) := by
      have hsubtop : (ambientDerivedSubgroup K).subgroupOf K = ⊤ := by
        rw [hEq]
        exact Subgroup.subgroupOf_eq_top.2 le_rfl
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hsubtop
    exact hcomm_lt.ne hDtop
  rw [hK'] at hKleK'
  exact (not_le_of_gt hDlt) hKleK'

/-- A Type-F complement contains an `M`-conjugate of the Sylow subgroup
`P0` occurring in PF `(12.9)`. -/
public theorem theorem_12_9_exists_conjugate_le_typeF_complement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K U P0 : Subgroup G) (p : ℕ) (hp : Nat.Prime p)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M K)
    (hcomp : section12ComplementIn M K U)
    (hP0M : P0 ≤ M) (hP0p : IsPGroup p P0)
    (hpK : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K) :
    ∃ g : M, P0.conjBy (g : G) ≤ U := by
  classical
  let pp : Nat.Primes := ⟨p, hp⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hKnorm : (K.subgroupOf M).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have hcompLocal : (K.subgroupOf M).IsComplement' (U.subgroupOf M) :=
    section12ComplementIn_left_normal_isComplement' hcomp hKnorm
  have hKHall :
      IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf M) :=
    section16MFSubgroup_subgroupOf_isHall hMF
  have hUHall :
      IsHallSubgroup (subgroupPrimeSet K)ᶜ (U.subgroupOf M) := by
    refine isHallSubgroup_of (G := M) (π := (subgroupPrimeSet K)ᶜ)
      (H := U.subgroupOf M) ?_ ?_
    · intro q hqU hqKc
      have hqKidx : q.val ∣ (K.subgroupOf M).index := by
        simpa [hcompLocal.symm.index_eq_card] using hqU
      exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqKc
    · intro q hqKc hqUidx
      have hqK : q.val ∣ Nat.card (K.subgroupOf M) := by
        simpa [hcompLocal.index_eq_card] using hqUidx
      exact hqKc (hKHall.p_in_pi_of_p_dvd_card q hqK)
  let P0sub : Subgroup M := P0.subgroupOf M
  have hP0pi : IsPiSubgroup (G := G) (subgroupPrimeSet K)ᶜ P0 := by
    have hsingle :
        IsPiSubgroup (G := G) ({pp} : Set Nat.Primes) P0 :=
      section8_isPiSubgroup_singleton_of_isPGroup (q := pp)
        (by simpa [pp] using hP0p)
    intro q hqP0
    have hqpp : q ∈ ({pp} : Set Nat.Primes) := hsingle q hqP0
    have hqeq : q = pp := by simpa using hqpp
    change q ∉ subgroupPrimeSet K
    rw [hqeq]
    exact hpK
  have hP0subpi :
      IsPiSubgroup (G := M) (subgroupPrimeSet K)ᶜ P0sub := by
    intro q hqP0sub
    have hcard : Nat.card P0sub = Nat.card P0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0M).toEquiv
    have hqP0 : q.val ∣ Nat.card P0 := by
      rw [← hcard]
      exact hqP0sub
    exact hP0pi q hqP0
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hP0subInv : IsInvariant Unit M P0sub := by
    refine ⟨?_⟩
    intro _ x
    simp [P0sub]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  obtain ⟨H, hHHall, _hHInv, hP0subH⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM (by simp)
      (subgroupPrimeSet K)ᶜ P0sub hP0subpi hP0subInv
  obtain ⟨g, hg⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hsolvM hHHall hUHall
  refine ⟨g, ?_⟩
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, hyP0, hyz⟩
  have hyM : y ∈ M := hP0M hyP0
  let yM : M := ⟨y, hyM⟩
  have hyH : yM ∈ H := hP0subH hyP0
  have hconjH :
      (MulAut.conj g) yM ∈ H.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨yM, hyH, rfl⟩
  have hconjU : (MulAut.conj g) yM ∈ U.subgroupOf M := by
    rw [hg]
    exact hconjH
  have hz_eq : z = (g : G) * y * (g : G)⁻¹ := by
    simpa [MulAut.conj_apply] using hyz.symm
  simpa [Subgroup.mem_subgroupOf, hz_eq, MulAut.conj_apply] using hconjU

/-- The PF `(8.12.b)` step in `(12.9)`: the centralizer of the chosen
nonidentity element is contained in the unique maximal subgroup `M`. -/
private theorem theorem_12_9_unique_maximal_centralizer
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K P0 : Subgroup G) (p : ℕ) (hp : Nat.Prime p)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K)
    (hMs : Section8.msChoiceSource M K K)
    (hP0M : P0 ≤ M) (hP0p : IsPGroup p P0)
    (hpK : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K)
    {x : G} (hxP0 : x ∈ P0) (hxne : x ≠ 1)
    (hCKne : elementCentralizerIn K x ≠ ⊥) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x} : Set G)) = {M} := by
  classical
  rcases hTypeI with ⟨U, U1, U0, hF, hAlt⟩
  have hcomp : section12ComplementIn M K U := hF.2.2.2.2.2.2.1
  rcases theorem_12_9_exists_conjugate_le_typeF_complement
      M K U P0 p hp hM hMF hcomp hP0M hP0p hpK with
    ⟨g, hP0gU⟩
  let xg : G := (g : G) * x * (g : G)⁻¹
  have hxgU : xg ∈ U := by
    apply hP0gU
    exact Subgroup.mem_map.mpr
      ⟨x, hxP0, by simp [xg, MulAut.conj_apply]⟩
  have hxgne : xg ≠ 1 := by
    intro hxg
    have hback := congrArg (fun z : G => (g : G)⁻¹ * z * (g : G)) hxg
    exact hxne (by simpa [xg, mul_assoc] using hback)
  let A : Set G := Section8.section8CentralizerUnion M K
  let A0 : Set G := A
  let A1 : Set G := Section8.a1Set K
  have hNotation : Section8.notation_8_10_source_data M K K A A0 A1 := by
    exact ⟨hM, hMF, hMs, rfl,
      Or.inl ⟨⟨U, U1, U0, hF, hAlt⟩, rfl, rfl⟩⟩
  have hSource : Section8.theorem_8_12_source_data M K U K A A0 A1 := by
    exact ⟨hNotation, Or.inl ⟨⟨U1, U0, hF, hAlt⟩, rfl, rfl⟩⟩
  have h812 : Section8.theorem_8_12_source_conclusion M K U A A1 :=
    Section8.theorem_8_12 M K U K A A0 A1 (by infer_instance) hSource
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (section16MFSubgroup_le hMF)).1
      (section16MFSubgroup_subgroupOf_normal hMF)
  have hgNormK : (g : G) ∈ Subgroup.normalizer (K : Set G) :=
    hMnormK g.property
  have hKconj : K.conjBy (g : G) = K :=
    section11_conjBy_eq_of_mem_normalizer hgNormK
  have hCKgne : section16CentralizerInSet K ({xg} : Set G) ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCKne with ⟨y, hyne⟩
    let yg : G := (g : G) * (y : G) * (g : G)⁻¹
    have hyGne : (y : G) ≠ 1 := by
      intro hy
      exact hyne (Subtype.ext hy)
    have hygne : yg ≠ 1 := by
      intro hyg
      have hback := congrArg (fun z : G => (g : G)⁻¹ * z * (g : G)) hyg
      exact hyGne (by simpa [yg, mul_assoc] using hback)
    have hygK : yg ∈ K := by
      have hygMap : yg ∈ K.conjBy (g : G) :=
        Subgroup.mem_map.mpr
          ⟨(y : G), y.property.1, by simp [yg, MulAut.conj_apply]⟩
      simpa [hKconj] using hygMap
    have hygCent : yg ∈ Subgroup.centralizer ({xg} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hycomm : (y : G) * x = x * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp y.property.2
      have hconj :=
        congrArg (fun z : G => (g : G) * z * (g : G)⁻¹) hycomm
      simpa [yg, xg, mul_assoc] using hconj
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨yg, hygK, hygCent⟩, ?_⟩
    intro hone
    exact hygne (congrArg Subtype.val hone)
  have hUniqueG :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({xg} : Set G)) = {M} := by
    exact h812.2.1 ({xg} : Set G) ⟨xg, rfl⟩
      (by
        intro z hz
        have hzEq : z = xg := by simpa using hz
        subst z
        exact ⟨hxgU, hxgne⟩)
      hCKgne
  have hUniqueGz :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer
          ((Subgroup.zpowers xg : Subgroup G) : Set G)) = {M} := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hUniqueG
  have hConjBack :=
    section16_maximalSubgroupsContaining_centralizer_conjBy
      (G := G) (X := Subgroup.zpowers xg) (M := M)
      hM (g : G)⁻¹ hUniqueGz
  have hzpowers :
      (Subgroup.zpowers xg).conjBy (g : G)⁻¹ = Subgroup.zpowers x := by
    have hmap :
        (Subgroup.zpowers x).map (MulAut.conj (g : G)).toMonoidHom =
          Subgroup.zpowers xg := by
      simp [MonoidHom.map_zpowers, xg, MulAut.conj_apply]
    rw [← hmap]
    exact Subgroup.conjBy_inv (Subgroup.zpowers x) (g : G)
  have hMback : M.conjBy (g : G)⁻¹ = M := by
    exact section11_conjBy_eq_of_mem_normalizer
      (Subgroup.le_normalizer (M.inv_mem g.property))
  have hUniqueZ :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer
          ((Subgroup.zpowers x : Subgroup G) : Set G)) = {M} := by
    simpa [hzpowers, hMback] using hConjBack
  simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hUniqueZ

/-- Every maximal subgroup of a minimal counterexample is self-normalizing. -/
private theorem theorem_12_9_maximal_normalizer_eq_self
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hMsigmaSub_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    exact hMsigma_ne (by simp [section10Msigma, hbot])
  have hnorm :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM (N := section10MsigmaSubgroup M) hMsigmaSub_ne
  have hnormSigma :
      Subgroup.normalizer (section10Msigma M : Set G) = M := by
    simpa [section10Msigma] using hnorm
  apply le_antisymm
  · intro g hgNormM
    have hle :
        Subgroup.normalizer (M : Set G) ≤
          Subgroup.normalizer
            (((section10MsigmaSubgroup M : Subgroup M).map M.subtype :
              Subgroup G) : Set G) :=
      section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := M) (K := section10MsigmaSubgroup M)
    have hgNormSigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) := by
      simpa [section10Msigma] using hle hgNormM
    simpa [hnormSigma] using hgNormSigma
  · exact Subgroup.le_normalizer

/-- Unique maximal containment of a centralizer, together with
self-normalization of that maximal subgroup, controls the normalizer of the
centralized set. -/
private theorem theorem_12_9_normalizer_le_of_unique_maximal_centralizer
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hSelfNorm : Subgroup.normalizer (M : Set G) = M)
    (huniq :
      section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M}) :
    Subgroup.normalizer X ≤ M := by
  intro g hgX
  have hC_le_M : Subgroup.centralizer X ≤ M := by
    have hMmem :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer X) := by
      simp [huniq]
    exact hMmem.2
  have hMconj_mem :
      M.conjBy g ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer X) := by
    refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
    intro x hxC
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, hC_le_M ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro a haX
    have hga : g * a * g⁻¹ ∈ X := (hgX a).1 haX
    have hcomm := hxC (g * a * g⁻¹) hga
    have hcomm' := congrArg (fun t : G => g⁻¹ * t * g) hcomm
    simpa [mul_assoc] using hcomm'
  have hMconj_eq : M.conjBy g = M := by
    have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniq] using hMconj_mem
    simpa using hsingle
  have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
    section10_mem_normalizer_of_conjBy_eq (G := G) hMconj_eq
  simpa [hSelfNorm] using hgNormM

/-- The last contradiction in PF `(12.9)`: the full centralizer of the
witness cannot lie in the maximal subgroup `L` chosen over `P0`. -/
private theorem theorem_12_9_centralizer_not_le_choice
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K P0 L LF Ls : Subgroup G) (x : G)
    (p : ℕ) (hp : Nat.Prime p)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M K)
    (hMs : Section8.msChoiceSource M K K)
    (hL : L ∈ section9MaximalSubgroups G)
    (hLF : section16MFSubgroup L LF)
    (hLs : Section8.msChoice L LF Ls)
    (hP0Ls : P0 ≤ Ls)
    (hP1Elem :
      IsElementaryAbelian p (section12OmegaOneSubgroup ⟨p, hp⟩ P0))
    (hxP1 : x ∈ section12OmegaOneSubgroup ⟨p, hp⟩ P0)
    (hxP0 : x ∈ P0) (hxne : x ≠ 1)
    (hpK : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K)
    (hUnique :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({x} : Set G)) = {M}) :
    ¬ elementCentralizerIn (⊤ : Subgroup G) x ≤ L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hcentL
  have hLcont :
      L ∈ section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({x} : Set G)) := by
    refine ⟨hL, ?_⟩
    simpa [elementCentralizerIn] using hcentL
  have hLsingle : L ∈ ({M} : Set (Subgroup G)) := by
    simpa [hUnique] using hLcont
  have hLM : L = M := by simpa using hLsingle
  have hLsEq : Ls = section10Msigma L :=
    Section8.theorem_8_11_msChoice_eq_msigma (G := G) hL hLF hLs
  have hKsigma : K = section10Msigma M :=
    Section8.theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  have hxLs : x ∈ Ls := hP0Ls hxP0
  have hxSigmaL : x ∈ section10Msigma L := by
    simpa [hLsEq] using hxLs
  have hxSigmaM : x ∈ section10Msigma M := by
    simpa [hLM] using hxSigmaL
  have hxK : x ∈ K := by
    simpa [hKsigma] using hxSigmaM
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  letI : IsElementaryAbelian p P1 := by
    simpa [P1] using hP1Elem
  have hxpowP1 : (⟨x, by simpa [P1] using hxP1⟩ : P1) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p P1) _
  have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowP1
  have horder : orderOf x = p := orderOf_eq_prime hxpow hxne
  have hpCardK : p ∣ Nat.card K := by
    rw [← horder]
    exact Subgroup.orderOf_dvd_natCard K hxK
  apply hpK
  change p ∣ Nat.card K
  exact hpCardK

/-- Source leaf for PF `(12.9)`.

The public proof of `(12.9)` is now reduced to the source-data package that
contains the `(8.17)/(8.11)` and centralizer construction of `L`, `L_s`, and
`x`. -/
public theorem theorem_12_9_source_data_of_hypothesis_12_8
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K : Subgroup G)
    (p : ℕ)
    (_h128 : ∃ K' P0 : Subgroup G, hypothesis_12_8_data M K K' P0 p) :
    theorem_12_9_source_data M K p := by
  classical
  intro K' P0 h128'
  have hRank : IsMulCommutative P0 ∧ groupRank P0 = 2 :=
    theorem_12_9_p0_rank_two M K K' P0 p h128'
  rcases h128' with
    ⟨hp, _hbad, _hmin, hM, hMF, hTypeI, hMs, hK', hnoncyc, hP0⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hP0 with ⟨P, hP0eq⟩
  have hP0M : P0 ≤ M := by
    rw [← hP0eq]
    exact section11_ambientSylow_le M P
  have hP0p : IsPGroup p P0 := by
    rw [← hP0eq]
    exact section11_ambientSylow_isPGroup M P
  rcases theorem_12_9_exists_maximal_msChoice_containing_p0
      P0 p hp hP0p hRank.2 with
    ⟨L, LF, Ls, hL, hLF, hLs, hP0Ls⟩
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  have hP1leP0 : P1 ≤ P0 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hyOmega, hyx⟩
    have hyP0 : (y : G) ∈ P0 := y.property
    simpa [P1] using hyx ▸ hyP0
  have hP1M : P1 ≤ M := hP1leP0.trans hP0M
  have hP1data : IsElementaryAbelian p P1 ∧ ¬ IsCyclic P1 := by
    simpa [P1] using
      theorem_12_9_omega_one_noncyclic P0 p hp hP0p hRank.1 hRank.2
  have hpK : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K :=
    theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
      M K p hp hMF hnoncyc
  have hcop : Nat.Coprime p (Nat.card K) :=
    prime_coprime_card_of_not_mem_subgroupPrimeSet hp hpK
  have hKsolv : IsSolvable K := by
    letI : Group.IsNilpotent K := hMF.1.2.2.1
    exact IsNilpotent.to_isSolvable
  have hKne : K ≠ ⊥ := by
    rcases hTypeI with ⟨_U, _U1, _U0, hF, _hAlt⟩
    exact ne_of_gt hF.2.2.2.1
  rcases theorem_12_9_exists_centralizer_witness
      M K K' P1 p hp hMF hP1M hP1data.1 hP1data.2
      hcop hKsolv hKne hK' with
    ⟨x, hxP1, hxne, hCKnot⟩
  have hxP0 : x ∈ P0 := hP1leP0 hxP1
  have hCKne : elementCentralizerIn K x ≠ ⊥ := by
    intro hbot
    apply hCKnot
    rw [hbot]
    exact bot_le
  have hUnique :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({x} : Set G)) = {M} :=
    theorem_12_9_unique_maximal_centralizer
      M K P0 p hp hM hMF hTypeI hMs hP0M hP0p hpK
      hxP0 hxne hCKne
  have hSelfNorm : Subgroup.normalizer (M : Set G) = M :=
    theorem_12_9_maximal_normalizer_eq_self hM
  have hUniqueZ :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer
          ((Subgroup.zpowers x : Subgroup G) : Set G)) = {M} := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hUnique
  have hNormalizer :
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M :=
    theorem_12_9_normalizer_le_of_unique_maximal_centralizer
      hM hSelfNorm hUniqueZ
  have hCentralizerNotL :
      ¬ elementCentralizerIn (⊤ : Subgroup G) x ≤ L :=
    theorem_12_9_centralizer_not_le_choice
      M K P0 L LF Ls x p hp hM hMF hMs hL hLF hLs hP0Ls
      hP1data.1 hxP1 hxP0 hxne hpK hUnique
  have hLsEq : Ls = section10Msigma L :=
    Section8.theorem_8_11_msChoice_eq_msigma (G := G) hL hLF hLs
  have hxL : x ∈ L := by
    have hxSigma : x ∈ section10Msigma L := by
      simpa [hLsEq] using hP0Ls hxP0
    exact section11_msigma_le L hxSigma
  exact ⟨L, LF, Ls, x, hRank.1, hRank.2, hL, hLF, hLs, hP0Ls,
    hxL, ⟨hp, hxP1, hxne⟩, hCKnot, hNormalizer, hCentralizerNotL⟩

/-- Peterfalvi `(12.9)`.

`P₀` is abelian of rank `2`.  There is a maximal subgroup `L` of `G`
such that `P₀ ⊂ L_s`.  There is an element `x ∈ Ω₁(P₀)^#` such that
`C_K(x) ⊈ K'`, `N_G(⟨x⟩) ⊂ M`, and `C_G(x) ⊈ L`. -/
public theorem theorem_12_9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 : Subgroup G)
    (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p) :
    ∃ (L LF Ls : Subgroup G) (x : G),
      theorem_12_9_data M K K' P0 L LF Ls x p := by
  have hsrc : theorem_12_9_source_data M K p :=
    theorem_12_9_source_data_of_hypothesis_12_8 M K p ⟨K', P0, h128⟩
  exact theorem_12_9_of_source_data M K K' P0 p hsrc h128

end CFSG.Section12
