module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.ConjugateAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingIntersections
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 4(b): source-facing contract

Theorem 4(b) belongs to the minimal-counterexample development in Sections
2--7 of `docs/cfsg-vol4.tex`.  The later proof of Theorem 6 uses it in the
following form: if an involution in the base stabilizer normalizes an odd-order
subgroup of that stabilizer, then it centralizes the subgroup unless the
subgroup fixes exactly one conjugate of the stabilizer.

This file records that conclusion as an explicit contract for the canonical
action on conjugates of `M`.  It does not assert that strong embedding alone
proves Theorem 4(b); the proof from the minimal-counterexample hypotheses is a
separate source obligation.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise commutatorElement

open PFAppendixIII PFchapter1section1

universe u

/-- The fixed-point type denoted `Omega_W` in the source, specialized to the
canonical action on conjugates of `M`. -/
public abbrev theorem4bFixedPoints
    {X : Type u} [Group X] (M W : Subgroup X) :=
  {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) W}

/-- Source-faithful base-point contract for Theorem 4(b).

Because `W ≤ M`, the base coset is fixed by `W`; hence cardinality one is
exactly the source assertion that `W` fixes a unique point.  The first
alternative is the centralizer form of `[z, W] = 1`. -/
public def Theorem4bAtBase
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) : Prop :=
  ∀ (z : X) (W : Subgroup X),
    IsInvolution z →
    z ∈ M →
    Odd (Nat.card W) →
    W ≤ M →
    z ∈ Subgroup.normalizer W →
      W ≤ Subgroup.centralizer ({z} : Set X) ∨
        Nat.card (theorem4bFixedPoints M W) = 1

/-! ## The Section 3 counting parameters -/

/-- The source parameter `m = |M : C_M(z)|` from `(3E)`, specialized to the
fixed base involution `z`. -/
@[expose] public def theorem4bM
    {X : Type u} [Group X] (M : Subgroup X) (z : X) : ℕ :=
  ((M ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf M).index

/-- The `p`-share `m_p` of the source parameter `m`. -/
@[expose] public def theorem4bPrimeShare
    {X : Type u} [Group X] (M : Subgroup X) (z : X) (p : ℕ) : ℕ :=
  p ^ (theorem4bM M z).factorization p

/-- Cardinality of the source set `I_P(z)` of elements of `P` inverted by
`z`. -/
@[expose] public def theorem4bInvertedCard
    {X : Type u} [Group X] (z : X) (P : Subgroup X) : ℕ :=
  Nat.card {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹}

/-- Inclusion of subgroups induces inclusion of their inverted-element sets. -/
public theorem theorem4bInvertedCard_mono
    {X : Type u} [Group X] [Finite X] {z : X} {P Q : Subgroup X}
    (hPQ : P ≤ Q) :
    theorem4bInvertedCard z P ≤ theorem4bInvertedCard z Q := by
  let f : {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹} →
      {x : X // x ∈ Q ∧ z * x * z⁻¹ = x⁻¹} :=
    fun x => ⟨x, hPQ x.property.1, x.property.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun q : {x : X // x ∈ Q ∧ z * x * z⁻¹ = x⁻¹} => (q : X)) hxy
  simpa [theorem4bInvertedCard] using
    Nat.card_le_card_of_injective f hf

/-- Ambient-subgroup form of `P ∈ Syl_p(D)`. -/
@[expose] public def theorem4bIsSylowSubgroupOf
    {X : Type u} [Group X] (p : ℕ) (P D : Subgroup X) : Prop :=
  ∃ Q : Sylow p D,
    P = (Q : Subgroup D).map D.subtype

/-- Exact base-point form of Proposition 3.8(b).  This is an earlier-section
source contract, not a conclusion of Theorem 4(b). -/
public def Theorem4bProposition38bAtBase
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) : Prop :=
  ∀ (z : X) (p : ℕ) (beta : conjugateCosetSpace M) (P : Subgroup X),
    IsInvolution z →
    z ∈ M →
    Nat.Prime p →
    IsPGroup p P →
    P ≤ M →
    P ≤ MulAction.stabilizer X beta →
    beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) →
    z ∈ Subgroup.normalizer (P : Set X) →
      theorem4bInvertedCard z P ≤ theorem4bPrimeShare M z p ∧
        (theorem4bIsSylowSubgroupOf p P
            (M ⊓ MulAction.stabilizer X beta) →
          theorem4bInvertedCard z P = theorem4bPrimeShare M z p)

/-- The source `(1) ↔ (3)` part of Proposition 3.8(c): existence of a
`z`-invariant Sylow `p`-subgroup of the two-point stabilizer is equivalent to
existence of some `z`-invariant `p`-subgroup whose inverted set has cardinality
`m_p`. -/
@[expose] public def Theorem4bProposition38cAtBase
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) : Prop :=
  ∀ (z : X) (p : ℕ) (beta : conjugateCosetSpace M),
    IsInvolution z →
    z ∈ M →
    Nat.Prime p →
    beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      ((∃ Q : Subgroup X,
          theorem4bIsSylowSubgroupOf p Q
            (M ⊓ MulAction.stabilizer X beta) ∧
          z ∈ Subgroup.normalizer (Q : Set X)) ↔
        ∃ P : Subgroup X,
          IsPGroup p P ∧
          P ≤ M ⊓ MulAction.stabilizer X beta ∧
          z ∈ Subgroup.normalizer (P : Set X) ∧
          theorem4bInvertedCard z P = theorem4bPrimeShare M z p)

/-! ## Proposition 3.8(a): the direct stabilizer transport -/

/-- If `z` normalizes `P` and `P` fixes `beta`, then `P` also fixes
`z • beta`.  This is the group-action core of Proposition 3.8(a). -/
public theorem theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {P : Subgroup G} {z : G} {beta : Ω}
    (hzNorm : z ∈ Subgroup.normalizer (P : Set G))
    (hPbeta : P ≤ MulAction.stabilizer G beta) :
    P ≤ MulAction.stabilizer G (z • beta) := by
  intro p hp
  apply MulAction.mem_stabilizer_iff.mpr
  have hzInvNorm : z⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hzNorm
  have hconj : z⁻¹ * p * z ∈ P := by
    simpa using (Subgroup.mem_normalizer_iff.mp hzInvNorm p).1 hp
  have hfix : (z⁻¹ * p * z) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp (hPbeta hconj)
  calc
    p • (z • beta) = (p * z) • beta := (mul_smul p z beta).symm
    _ = (z * (z⁻¹ * p * z)) • beta := by group
    _ = z • ((z⁻¹ * p * z) • beta) := mul_smul z (z⁻¹ * p * z) beta
    _ = z • beta := by rw [hfix]

/-- Proposition 3.8(a) in the source's two- and three-point stabilizer
notation: a `z`-invariant subgroup of `M ⊓ X_beta` lies in
`(M ⊓ X_beta) ⊓ X_(z • beta)`. -/
public theorem theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {M P : Subgroup G} {z : G} {beta : Ω}
    (hzNorm : z ∈ Subgroup.normalizer (P : Set G))
    (hPD : P ≤ M ⊓ MulAction.stabilizer G beta) :
    P ≤ (M ⊓ MulAction.stabilizer G beta) ⊓
      MulAction.stabilizer G (z • beta) := by
  refine le_inf hPD ?_
  apply theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer hzNorm
  exact hPD.trans inf_le_right

/-- The involution fixing the base point normalizes the triple stabilizer
obtained from `beta` and `z • beta`, interchanging its last two points. -/
public theorem theorem4b_mem_normalizer_tripleStabilizer
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {M : Subgroup G} {z : G} {beta : Ω}
    (hz : IsInvolution z) (hzM : z ∈ M) :
    z ∈ Subgroup.normalizer
      (((M ⊓ MulAction.stabilizer G beta) ⊓
        MulAction.stabilizer G (z • beta) : Subgroup G) : Set G) := by
  have hzz : z * z = 1 := by
    simpa [pow_two] using hz.sq_eq_one
  have hforward : ∀ x : G,
      x ∈ ((M ⊓ MulAction.stabilizer G beta) ⊓
        MulAction.stabilizer G (z • beta) : Subgroup G) →
      z * x * z⁻¹ ∈ ((M ⊓ MulAction.stabilizer G beta) ⊓
        MulAction.stabilizer G (z • beta) : Subgroup G) := by
    intro x hx
    rcases hx with ⟨⟨hxM, hxBeta⟩, hxZBeta⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact M.mul_mem (M.mul_mem hzM hxM) (M.inv_mem hzM)
    · apply MulAction.mem_stabilizer_iff.mpr
      have hxFix := MulAction.mem_stabilizer_iff.mp hxZBeta
      calc
        (z * x * z⁻¹) • beta = z • (x • (z⁻¹ • beta)) := by
          simp only [mul_smul]
        _ = z • (x • (z • beta)) := by rw [hz.inv_eq_self]
        _ = z • (z • beta) := by rw [hxFix]
        _ = beta := by rw [← mul_smul, hzz, one_smul]
    · apply MulAction.mem_stabilizer_iff.mpr
      have hxFix := MulAction.mem_stabilizer_iff.mp hxBeta
      calc
        (z * x * z⁻¹) • (z • beta) =
            z • (x • (z⁻¹ • (z • beta))) := by
              simp only [mul_smul]
        _ = z • (x • beta) := by rw [inv_smul_smul]
        _ = z • beta := by rw [hxFix]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have hback := hforward (z * x * z⁻¹) hx
    have hcancel : z * (z * x * z⁻¹) * z⁻¹ = x := by
      rw [hz.inv_eq_self]
      calc
        z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; simp
    simpa only [hcancel] using hback

/-- Centralizing `z` makes the third fixed-point condition automatic, so the
`z`-centralizers in the two- and three-point stabilizers coincide. -/
public theorem theorem4b_tripleStabilizer_inf_centralizer_eq
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (M : Subgroup G) (z : G) (beta : Ω) :
    (((M ⊓ MulAction.stabilizer G beta) ⊓
          MulAction.stabilizer G (z • beta)) ⊓
        Subgroup.centralizer ({z} : Set G)) =
      ((M ⊓ MulAction.stabilizer G beta) ⊓
        Subgroup.centralizer ({z} : Set G)) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1.1, hx.2⟩
  · intro x hx
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hxFix := MulAction.mem_stabilizer_iff.mp hx.1.2
    have hxComm : x * z = z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx.2
    calc
      x • (z • beta) = (x * z) • beta := (mul_smul x z beta).symm
      _ = (z * x) • beta := by rw [hxComm]
      _ = z • (x • beta) := mul_smul z x beta
      _ = z • beta := by rw [hxFix]

/-- A two-point stabilizer involving the distinguished base point and a
different point has odd order. -/
public theorem IsStronglyEmbedded.base_inf_stabilizer_card_odd
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {beta : conjugateCosetSpace M}
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    Odd (Nat.card (M ⊓ MulAction.stabilizer X beta : Subgroup X)) := by
  rcases QuotientGroup.mk_surjective beta with ⟨g, rfl⟩
  have hgInvNotM : g⁻¹ ∉ M := by
    intro hgInvM
    apply hbeta
    exact QuotientGroup.eq.mpr (by simpa using hgInvM)
  rw [conjugateCoset_stabilizer]
  exact hM.inf_rightConjugate_card_odd hgInvNotM

/-- Coprime action on an odd subgroup: an involution-normalized `p`-subgroup
is contained in an involution-normalized Sylow `p`-subgroup. -/
public theorem theorem4b_exists_invariant_sylow_containing
    {X : Type u} [Group X] [Finite X]
    {D P : Subgroup X} {z : X} {p : ℕ}
    (hDodd : Odd (Nat.card D))
    (hz : IsInvolution z)
    (hzNormD : z ∈ Subgroup.normalizer (D : Set X))
    (hp : Nat.Prime p)
    (hPp : IsPGroup p P)
    (hPD : P ≤ D)
    (hzNormP : z ∈ Subgroup.normalizer (P : Set X)) :
    ∃ Q : Subgroup X,
      theorem4bIsSylowSubgroupOf p Q D ∧ P ≤ Q ∧
        z ∈ Subgroup.normalizer (Q : Set X) := by
  classical
  let A : Subgroup X := Subgroup.zpowers z
  have hA_normD : A ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hzNormD
  have hA_normP : A ≤ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hzNormP
  letI : Subgroup.Normalizes A D := ⟨hA_normD⟩
  let p' : Nat.Primes := ⟨p, hp⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hPsub_p : IsPGroup p (P.subgroupOf D) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  have hPpi : IsPiSubgroup (G := D) ({p'} : Set Nat.Primes)
      (P.subgroupOf D) :=
    isPiSubgroup_singleton_of_isPGroup hPsub_p
  have hPinv : IsInvariant (↥A) (↥D) (P.subgroupOf D) :=
    isInvariant_subgroupOf_of_le_normalizer hA_normD hA_normP hPD
  have hsolvD : IsSolvable D := odd_order_theorem D hDodd
  have hzOrder : orderOf z = 2 :=
    (orderOf_eq_prime_iff).2 ⟨hz.sq_eq_one, hz.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simpa [A] using (Nat.card_zpowers z).trans hzOrder
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D) := by
    rw [hAcard]
    exact hDodd.coprime_two_left
  obtain ⟨H, hHHall, hHinv, hPsub_le_H⟩ :=
    proposition_1_5_b (G := D) (A := A) hsolvD hcop
      ({p'} : Set Nat.Primes) (P.subgroupOf D) hPpi hPinv
  have hHp : IsPGroup p H := by
    simpa [p'] using isPGroup_of_isPiSubgroup_singleton hHHall.isPiSubgroup
  have hp_not_dvd_index : ¬ p ∣ H.index := by
    intro hpIndex
    exact (hHHall.p_in_pi_of_p_dvd_index p' hpIndex) (by simp)
  let S : Sylow p D := IsPGroup.toSylow (p := p) hHp hp_not_dvd_index
  have hS_eq : (S : Subgroup D) = H := by
    simpa [S] using IsPGroup.toSylow_coe hHp hp_not_dvd_index
  let Q : Subgroup X := H.map D.subtype
  have hPQ : P ≤ Q := by
    intro x hxP
    apply Subgroup.mem_map.mpr
    have hxPD : (⟨x, hPD hxP⟩ : D) ∈ P.subgroupOf D := by
      change x ∈ P
      exact hxP
    exact ⟨⟨x, hPD hxP⟩, hPsub_le_H hxPD, rfl⟩
  letI : IsInvariant (↥A) (↥D) H := hHinv
  have hA_normQ : A ≤ Subgroup.normalizer (Q : Set X) := by
    refine subgroup_le_normalizer_of_conj_mem Q A ?_
    intro a x hxQ
    rcases Subgroup.mem_map.mp hxQ with ⟨y, hyH, rfl⟩
    have hyInv : a • y ∈ H :=
      (IsInvariant.invariant (A := ↥A) (G := ↥D) (H := H) a y).1 hyH
    apply Subgroup.mem_map.mpr
    refine ⟨a • y, hyInv, ?_⟩
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  refine ⟨Q, ?_, hPQ, ?_⟩
  · refine ⟨S, ?_⟩
    simp [Q, hS_eq]
  · exact hA_normQ (show z ∈ A from Subgroup.mem_zpowers z)

/-- Proposition 3.7(b): an involution-invariant Sylow `p`-subgroup of an
odd group contains an ambient Sylow `p`-subgroup of the involution
centralizer.  The conjugating element supplied by coprime Hall conjugacy is
fixed by the involution, so it preserves the centralizer. -/
public theorem theorem4b_exists_centralizer_sylow_le_of_invariant_sylow
    {X : Type u} [Group X] [Finite X]
    {D Q : Subgroup X} {t : X} {p : ℕ}
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (htNormD : t ∈ Subgroup.normalizer (D : Set X))
    (hp : Nat.Prime p)
    (htNormQ : t ∈ Subgroup.normalizer (Q : Set X))
    (hQSylow : theorem4bIsSylowSubgroupOf p Q D) :
    ∃ S : Subgroup X,
      theorem4bIsSylowSubgroupOf p S
        (D ⊓ Subgroup.centralizer ({t} : Set X)) ∧
      S ≤ Q := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup X := D ⊓ Subgroup.centralizer ({t} : Set X)
  let S0 : Sylow p C := default
  let S : Subgroup X := (S0 : Subgroup C).map C.subtype
  have hSC : S ≤ C := by
    simpa [S] using
      (Subgroup.map_le_range C.subtype (S0 : Subgroup C))
  have hSp : IsPGroup p S := by
    exact S0.isPGroup'.map C.subtype
  have hSD : S ≤ D := hSC.trans inf_le_left
  have htCentS : t ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSC hs).2
  have htNormS : t ∈ Subgroup.normalizer (S : Set X) :=
    centralizer_le_normalizer S htCentS
  obtain ⟨R, hRSylow, hSR, htNormR⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hDodd ht htNormD hp hSp hSD htNormS
  rcases hQSylow with ⟨Qd, hQeq⟩
  rcases hRSylow with ⟨Rd, hReq⟩
  have hQD : Q ≤ D := by
    rw [hQeq]
    simpa using
      (Subgroup.map_le_range D.subtype (Qd : Subgroup D))
  have hRD : R ≤ D := by
    rw [hReq]
    simpa using
      (Subgroup.map_le_range D.subtype (Rd : Subgroup D))
  let A : Subgroup X := Subgroup.zpowers t
  have hA_normD : A ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact htNormD
  letI : Subgroup.Normalizes A D := ⟨hA_normD⟩
  have hA_normQ : A ≤ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.zpowers_le]
    exact htNormQ
  have hA_normR : A ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.zpowers_le]
    exact htNormR
  have hQinvSub : IsInvariant A D (Q.subgroupOf D) :=
    isInvariant_subgroupOf_of_le_normalizer
      hA_normD hA_normQ hQD
  have hRinvSub : IsInvariant A D (R.subgroupOf D) :=
    isInvariant_subgroupOf_of_le_normalizer
      hA_normD hA_normR hRD
  have hQsubEq : Q.subgroupOf D = (Qd : Subgroup D) := by
    rw [hQeq]
    exact subgroupOf_map_subtype_eq (Qd : Subgroup D)
  have hRsubEq : R.subgroupOf D = (Rd : Subgroup D) := by
    rw [hReq]
    exact subgroupOf_map_subtype_eq (Rd : Subgroup D)
  have hQinv : IsInvariant A D (Qd : Subgroup D) := by
    simpa only [hQsubEq] using hQinvSub
  have hRinv : IsInvariant A D (Rd : Subgroup D) := by
    simpa only [hRsubEq] using hRinvSub
  let p' : Nat.Primes := ⟨p, hp⟩
  have hQPi : IsPiSubgroup (G := D) ({p'} : Set Nat.Primes)
      (Qd : Subgroup D) := by
    simpa [p'] using
      isPiSubgroup_singleton_of_isPGroup Qd.isPGroup'
  have hRPi : IsPiSubgroup (G := D) ({p'} : Set Nat.Primes)
      (Rd : Subgroup D) := by
    simpa [p'] using
      isPiSubgroup_singleton_of_isPGroup Rd.isPGroup'
  have hQHall : IsHallSubgroup ({p'} : Set Nat.Primes)
      (Qd : Subgroup D) := by
    refine isHallSubgroup_of ({p'} : Set Nat.Primes) (Qd : Subgroup D)
      hQPi ?_
    intro q hq
    have hqp : q = p' := by simpa using hq
    subst q
    simpa [p'] using Qd.not_dvd_index
  have hRHall : IsHallSubgroup ({p'} : Set Nat.Primes)
      (Rd : Subgroup D) := by
    refine isHallSubgroup_of ({p'} : Set Nat.Primes) (Rd : Subgroup D)
      hRPi ?_
    intro q hq
    have hqp : q = p' := by simpa using hq
    subst q
    simpa [p'] using Rd.not_dvd_index
  have hsolvD : IsSolvable D := odd_order_theorem D hDodd
  have htOrder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simpa [A] using (Nat.card_zpowers t).trans htOrder
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D) := by
    rw [hAcard]
    exact hDodd.coprime_two_left
  obtain ⟨g, hgfix, hQdEq⟩ :=
    proposition_1_5_c (G := D) (A := A) hsolvD hcop
      ({p'} : Set Nat.Primes) (Rd : Subgroup D) (Qd : Subgroup D)
      hRHall hQHall hRinv hQinv
  have hfixEq :
      fixedPointSubgroup A D =
        (subgroupCentralizerIn D A).subgroupOf D := by
    simpa using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        D A hA_normD
  rw [hfixEq] at hgfix
  have hgcent : ((g : D) : X) ∈ subgroupCentralizerIn D A := by
    simpa [Subgroup.mem_subgroupOf] using hgfix
  have hgCt : ((g : D) : X) ∈
      Subgroup.centralizer ({t} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hgcent.2
      t (Subgroup.mem_zpowers t)).symm
  let gC : C := ⟨((g : D) : X), ⟨g.property, hgCt⟩⟩
  let Sg0 : Sylow p C :=
    S0.mapSurjective (f := (MulAut.conj gC).toMonoidHom)
      (MulAut.conj gC).surjective
  let Sg : Subgroup X := (Sg0 : Subgroup C).map C.subtype
  refine ⟨Sg, ⟨Sg0, rfl⟩, ?_⟩
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨xc, hxc, rfl⟩
  change xc ∈ (S0 : Subgroup C).map
      (MulAut.conj gC).toMonoidHom at hxc
  rcases Subgroup.mem_map.mp hxc with ⟨sc, hsc, rfl⟩
  have hscS : (sc : X) ∈ S :=
    Subgroup.mem_map.mpr ⟨sc, hsc, rfl⟩
  have hscD : (sc : X) ∈ D := hSD hscS
  let scD : D := ⟨(sc : X), hscD⟩
  have hscRd : scD ∈ (Rd : Subgroup D) := by
    have hscR : (sc : X) ∈ R := hSR hscS
    rw [hReq] at hscR
    rcases Subgroup.mem_map.mp hscR with ⟨y, hyRd, hy⟩
    have hyEq : y = scD := Subtype.ext hy
    simpa [hyEq] using hyRd
  have hconjQd : (MulAut.conj g) scD ∈ (Qd : Subgroup D) := by
    rw [hQdEq]
    exact Subgroup.mem_map.mpr ⟨scD, hscRd, rfl⟩
  rw [hQeq]
  apply Subgroup.mem_map.mpr
  refine ⟨(MulAut.conj g) scD, hconjQd, ?_⟩
  simp [gC, scD, MulAut.conj_apply]

/-- The fixed/inverted cardinal factorization `(3G)` for an odd normalized
subgroup, specialized to the inverted-cardinality encoding used here. -/
public theorem theorem4b_card_eq_card_fixed_mul_inverted
    {X : Type u} [Group X] [Finite X]
    {z : X} {P : Subgroup X}
    (hz : IsInvolution z)
    (hPodd : Odd (Nat.card P))
    (hzNorm : z ∈ Subgroup.normalizer (P : Set X)) :
    Nat.card P =
      Nat.card (P ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) *
        theorem4bInvertedCard z P := by
  change Nat.card P =
    Nat.card (P ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) *
      Nat.card {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹}
  rw [show Nat.card {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹} =
      ({x : X | x ∈ P ∧ z * x * z⁻¹ = x⁻¹}).ncard by rfl]
  simpa [rightConjugateElem, hz.inv_eq_self] using
    (PFchapter1section1.lemma_a z P hz hPodd hzNorm).2.2

/-- Simultaneous conjugation of the involution and subgroup preserves the
cardinality of the inverted set. -/
public theorem theorem4bInvertedCard_conjBy
    {X : Type u} [Group X] (z g : X) (P : Subgroup X) :
    theorem4bInvertedCard (rightConjugateElem z g) (P.conjBy g⁻¹) =
      theorem4bInvertedCard z P := by
  let φ : X ≃* X := MulAut.conj g⁻¹
  let e : {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹} ≃
      {x : X // x ∈ P.conjBy g⁻¹ ∧
        rightConjugateElem z g * x * (rightConjugateElem z g)⁻¹ = x⁻¹} :=
    { toFun := fun x => by
        refine ⟨φ x, ?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨x, x.property.1, rfl⟩
        · have hzg : rightConjugateElem z g = φ z := by
            simp [φ, rightConjugateElem, MulAut.conj_apply]
          rw [hzg]
          change φ z * φ x * (φ z)⁻¹ = (φ x)⁻¹
          simpa using congrArg φ x.property.2
      invFun := fun x => by
        refine ⟨φ.symm x, ?_, ?_⟩
        · rcases Subgroup.mem_map.mp x.property.1 with ⟨y, hy, hyx⟩
          have hxy : φ.symm x = y := by
            rw [← hyx]
            exact φ.symm_apply_apply y
          simpa [hxy] using hy
        · have hzg : rightConjugateElem z g = φ z := by
            simp [φ, rightConjugateElem, MulAut.conj_apply]
          have hxprop : φ z * (x : X) * (φ z)⁻¹ = (x : X)⁻¹ := by
            rw [← hzg]
            exact x.property.2
          have hx := congrArg φ.symm hxprop
          simpa using hx
      left_inv := by
        intro x
        apply Subtype.ext
        exact φ.symm_apply_apply x
      right_inv := by
        intro x
        apply Subtype.ext
        exact φ.apply_symm_apply x }
  exact (Nat.card_congr e).symm

private theorem theorem4b_inf_rightConjugate_centralizer_index_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    (((D ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf D)).index =
      theorem4bM M z := by
  let C : Subgroup X := Subgroup.centralizer ({z} : Set X)
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hCM : C ≤ M := hM.centralizer_le hzM hz
  have hDM : D ≤ M := inf_le_left
  have hprod : (C : Set X) * (D : Set X) = (M : Set X) := by
    simpa [C, D] using
      hM.centralizer_mul_inf_rightConjugate_eq hzM hz ht htM
  have hprodRev : (D : Set X) * (C : Set X) = (M : Set X) := by
    ext x
    constructor
    · rintro ⟨d, hd, c, hc, rfl⟩
      exact M.mul_mem (hDM hd) (hCM hc)
    · intro hxM
      have hxInvM : x⁻¹ ∈ M := M.inv_mem hxM
      have hxInvProd : x⁻¹ ∈ (C : Set X) * (D : Set X) := by
        rw [hprod]
        exact hxInvM
      rcases hxInvProd with ⟨c, hc, d, hd, hcd⟩
      refine ⟨d⁻¹, D.inv_mem hd, c⁻¹, C.inv_mem hc, ?_⟩
      have := congrArg Inv.inv hcd
      simpa only [mul_inv_rev, inv_inv] using this
  let CM : Subgroup M := C.subgroupOf M
  let DM : Subgroup M := D.subgroupOf M
  letI : MulAction.IsPretransitive DM (M ⧸ CM) := by
    constructor
    intro q₁ q₂
    have hbase (q : M ⧸ CM) :
        ∃ d : DM, d • ((1 : M) : M ⧸ CM) = q := by
      rcases QuotientGroup.mk_surjective q with ⟨m, rfl⟩
      have hmProd : (m : X) ∈ (D : Set X) * (C : Set X) := by
        rw [hprodRev]
        exact m.property
      rcases hmProd with ⟨d, hd, c, hc, hdc⟩
      let dM : DM := ⟨⟨d, hDM hd⟩, hd⟩
      refine ⟨dM, ?_⟩
      change QuotientGroup.mk ((dM : M) * (1 : M)) = QuotientGroup.mk m
      rw [QuotientGroup.eq]
      change ((d : X) * 1)⁻¹ * (m : X) ∈ C
      rw [mul_one, ← hdc]
      simpa using hc
    obtain ⟨d₁, hd₁⟩ := hbase q₁
    obtain ⟨d₂, hd₂⟩ := hbase q₂
    refine ⟨d₂ * d₁⁻¹, ?_⟩
    rw [← hd₁, ← hd₂, mul_smul, inv_smul_smul]
  have hstab :
      MulAction.stabilizer DM ((1 : M) : M ⧸ CM) =
        CM.comap DM.subtype := by
    ext d
    rw [MulAction.mem_stabilizer_iff]
    change QuotientGroup.mk ((d : M) * (1 : M)) =
        QuotientGroup.mk (1 : M) ↔ (d : M) ∈ CM
    rw [QuotientGroup.eq]
    simp
  have hindex : (CM.comap DM.subtype).index = CM.index := by
    rw [← hstab]
    exact MulAction.index_stabilizer_of_transitive DM
      ((1 : M) : M ⧸ CM)
  change (D ⊓ C).relIndex D = (M ⊓ C).relIndex M
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
  rw [← Subgroup.relIndex_subgroupOf hDM]
  exact hindex

/-- Proposition 3.6(d), now with the outside involution in the centralizer:
for `D = M ⊓ M^t`, the index of `C_D(t)` is the same source parameter
`m = |M : C_M(z)|`. -/
public theorem IsStronglyEmbedded.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    (((D ⊓ Subgroup.centralizer ({t} : Set X)).subgroupOf D)).index =
      theorem4bM M z := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let Ct : Subgroup X := D ⊓ Subgroup.centralizer ({t} : Set X)
  let Cz : Subgroup X := D ⊓ Subgroup.centralizer ({z} : Set X)
  change (Ct.subgroupOf D).index = theorem4bM M z
  have hcard : Nat.card Ct = Nat.card Cz := by
    simpa [Ct, Cz, D] using
      hM.inf_rightConjugate_outside_inside_centralizer_card_eq
        hzM hz ht htM
  have hindexZ : (Cz.subgroupOf D).index = theorem4bM M z := by
    simpa [Cz, D] using
      theorem4b_inf_rightConjugate_centralizer_index_eq hM hzM hz ht htM
  have hcardCtSub : Nat.card (Ct.subgroupOf D) = Nat.card Ct :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show Ct ≤ D from inf_le_left))
  have hcardCzSub : Nat.card (Cz.subgroupOf D) = Nat.card Cz :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show Cz ≤ D from inf_le_left))
  have hmul :
      Nat.card Ct * (Ct.subgroupOf D).index =
        Nat.card Ct * (Cz.subgroupOf D).index := by
    calc
      Nat.card Ct * (Ct.subgroupOf D).index = Nat.card D := by
        rw [← hcardCtSub]
        exact (Ct.subgroupOf D).card_mul_index
      _ = Nat.card Cz * (Cz.subgroupOf D).index := by
        rw [← hcardCzSub]
        exact (Cz.subgroupOf D).card_mul_index.symm
      _ = Nat.card Ct * (Cz.subgroupOf D).index := by rw [← hcard]
  rw [← hindexZ]
  exact Nat.mul_left_cancel Nat.card_pos hmul

/-- Proposition 3.7(c), in the base/intersection coordinates: if an outside
involution `t` normalizes a `p`-subgroup of `D = M ⊓ M^t`, then the number of
elements it inverts is at most the `p`-share of
`m = |M : C_M(z)|`. -/
public theorem IsStronglyEmbedded.theorem4b_inf_rightConjugate_invertedCard_le_primeShare
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X} {p : ℕ} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hp : Nat.Prime p) (hPp : IsPGroup p P)
    (hPD : P ≤ M ⊓ rightConjugate M t)
    (htNormP : t ∈ Subgroup.normalizer (P : Set X)) :
    theorem4bInvertedCard t P ≤ theorem4bPrimeShare M z p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let D : Subgroup X := M ⊓ rightConjugate M t
  let Ct : Subgroup X := Subgroup.centralizer ({t} : Set X)
  let C : Subgroup X := D ⊓ Ct
  have hPD' : P ≤ D := by simpa [D] using hPD
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  obtain ⟨Q, hQSylow, hPQ, htNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hDodd ht htNormD hp hPp hPD' htNormP
  obtain ⟨S, hSSylow, hSQ⟩ :=
    theorem4b_exists_centralizer_sylow_le_of_invariant_sylow
      hDodd ht htNormD hp htNormQ hQSylow
  rcases hQSylow with ⟨Q0, hQeq⟩
  rcases hSSylow with ⟨S0, hSeq⟩
  have hQD : Q ≤ D := by
    rw [hQeq]
    simpa using
      (Subgroup.map_le_range D.subtype (Q0 : Subgroup D))
  have hQp : IsPGroup p Q := by
    rw [hQeq]
    exact Q0.isPGroup'.map D.subtype
  have hQcard : Nat.card Q = p ^ (Nat.card D).factorization p := by
    rw [hQeq, Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity Q0
  have hQodd : Odd (Nat.card Q) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hQD)
  let CQ : Subgroup X := Q ⊓ Ct
  have hfixed :
      Nat.card Q = Nat.card CQ * theorem4bInvertedCard t Q := by
    simpa [CQ, Ct] using
      theorem4b_card_eq_card_fixed_mul_inverted ht hQodd htNormQ
  have hSC : S ≤ C := by
    rw [hSeq]
    simpa [C] using
      (Subgroup.map_le_range C.subtype (S0 : Subgroup C))
  have hSCQ : S ≤ CQ := by
    exact le_inf hSQ (hSC.trans inf_le_right)
  have hCQC : CQ ≤ C := by
    exact inf_le_inf hQD le_rfl
  have hCQp : IsPGroup p CQ := hQp.to_inf_left
  have hScard : Nat.card S = p ^ (Nat.card C).factorization p := by
    rw [hSeq, Subgroup.card_map_of_injective C.subtype_injective]
    exact Sylow.card_eq_multiplicity S0
  obtain ⟨a, hCQcardPow⟩ := hCQp.exists_card_eq
  have hfacC_le_a : (Nat.card C).factorization p ≤ a := by
    have hfac := Nat.factorization_le_factorization_of_dvd_right
      (a := p) (Subgroup.card_dvd_of_le hSCQ)
      Nat.card_pos.ne' Nat.card_pos.ne'
    rw [hScard, hCQcardPow, Nat.factorization_pow_self hp,
      Nat.factorization_pow_self hp] at hfac
    exact hfac
  have ha_le_facC : a ≤ (Nat.card C).factorization p := by
    have hfac := Nat.factorization_le_factorization_of_dvd_right
      (a := p) (Subgroup.card_dvd_of_le hCQC)
      Nat.card_pos.ne' Nat.card_pos.ne'
    rw [hCQcardPow, Nat.factorization_pow_self hp] at hfac
    exact hfac
  have ha : a = (Nat.card C).factorization p :=
    Nat.le_antisymm ha_le_facC hfacC_le_a
  have hCQcard : Nat.card CQ = p ^ (Nat.card C).factorization p := by
    rw [hCQcardPow, ha]
  have hindex : (C.subgroupOf D).index = theorem4bM M z := by
    simpa [C, D, Ct] using
      hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
        hzM hz ht htM
  have hcardSub : Nat.card (C.subgroupOf D) = Nat.card C :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show C ≤ D from inf_le_left))
  have hcardC : Nat.card C * theorem4bM M z = Nat.card D := by
    rw [← hcardSub, ← hindex]
    exact (C.subgroupOf D).card_mul_index
  have hmne : theorem4bM M z ≠ 0 := by
    rw [← hindex]
    exact Subgroup.index_ne_zero_of_finite
  have hfacC :
      (Nat.card C).factorization p +
          (theorem4bM M z).factorization p =
        (Nat.card D).factorization p := by
    have hfac := congrArg (fun n : ℕ => n.factorization p) hcardC
    change (Nat.card C * theorem4bM M z).factorization p =
      (Nat.card D).factorization p at hfac
    have hmulFac :
        (Nat.card C * theorem4bM M z).factorization p =
          (Nat.card C).factorization p +
            (theorem4bM M z).factorization p := by
      have hmulFacAll := Nat.factorization_mul (a := Nat.card C)
        (b := theorem4bM M z) Nat.card_pos.ne' hmne
      simpa using congrArg (fun f : ℕ →₀ ℕ => f p) hmulFacAll
    exact hmulFac.symm.trans hfac
  have hpPartEq :
      Nat.card CQ * theorem4bPrimeShare M z p = Nat.card Q := by
    calc
      Nat.card CQ * theorem4bPrimeShare M z p =
          p ^ ((Nat.card C).factorization p +
            (theorem4bM M z).factorization p) := by
              rw [hCQcard, theorem4bPrimeShare, pow_add]
      _ = p ^ (Nat.card D).factorization p := by rw [hfacC]
      _ = Nat.card Q := hQcard.symm
  have hmul :
      Nat.card CQ * theorem4bInvertedCard t Q =
        Nat.card CQ * theorem4bPrimeShare M z p := by
    exact hfixed.symm.trans hpPartEq.symm
  have hQinv :
      theorem4bInvertedCard t Q = theorem4bPrimeShare M z p :=
    Nat.mul_left_cancel Nat.card_pos hmul
  let f : {x : X // x ∈ P ∧ t * x * t⁻¹ = x⁻¹} →
      {x : X // x ∈ Q ∧ t * x * t⁻¹ = x⁻¹} :=
    fun x => ⟨x, hPQ x.property.1, x.property.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxyval := congrArg
      (fun q : {x : X // x ∈ Q ∧ t * x * t⁻¹ = x⁻¹} => (q : X)) hxy
    simpa [f] using hxyval
  have hmono : theorem4bInvertedCard t P ≤ theorem4bInvertedCard t Q := by
    simpa [theorem4bInvertedCard] using
      Nat.card_le_card_of_injective f hf
  exact hmono.trans_eq hQinv

/-- Proposition 3.7(d): if an outside involution normalizes a Sylow
`p`-subgroup of `D = M \cap M^t`, then its inverted-element set has exactly
the `p`-share of `m = |M : C_M(z)|`. -/
public theorem IsStronglyEmbedded.theorem4b_inf_rightConjugate_invertedCard_eq_primeShare_of_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X} {p : ℕ} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hp : Nat.Prime p)
    (hPSylow : theorem4bIsSylowSubgroupOf p P
      (M ⊓ rightConjugate M t))
    (htNormP : t ∈ Subgroup.normalizer (P : Set X)) :
    theorem4bInvertedCard t P = theorem4bPrimeShare M z p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let D : Subgroup X := M ⊓ rightConjugate M t
  let Ct : Subgroup X := Subgroup.centralizer ({t} : Set X)
  let C : Subgroup X := D ⊓ Ct
  rcases hPSylow with ⟨P0, hPeq⟩
  have hPD : P ≤ D := by
    rw [hPeq]
    simpa [D] using
      (Subgroup.map_le_range D.subtype (P0 : Subgroup D))
  have hPp : IsPGroup p P := by
    rw [hPeq]
    exact P0.isPGroup'.map D.subtype
  have hPcard : Nat.card P = p ^ (Nat.card D).factorization p := by
    rw [hPeq, Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity P0
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hPodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hPD)
  let CP : Subgroup X := P ⊓ Ct
  have hfixed :
      Nat.card P = Nat.card CP * theorem4bInvertedCard t P := by
    simpa [CP, Ct] using
      theorem4b_card_eq_card_fixed_mul_inverted ht hPodd htNormP
  obtain ⟨S, hSSylow, hSP⟩ :=
    theorem4b_exists_centralizer_sylow_le_of_invariant_sylow
      hDodd ht htNormD hp htNormP ⟨P0, hPeq⟩
  rcases hSSylow with ⟨S0, hSeq⟩
  have hSC : S ≤ C := by
    rw [hSeq]
    simpa [C] using
      (Subgroup.map_le_range C.subtype (S0 : Subgroup C))
  have hSCP : S ≤ CP := by
    exact le_inf hSP (hSC.trans inf_le_right)
  have hCPC : CP ≤ C := by
    exact inf_le_inf hPD le_rfl
  have hCPp : IsPGroup p CP := hPp.to_inf_left
  have hScard : Nat.card S = p ^ (Nat.card C).factorization p := by
    rw [hSeq, Subgroup.card_map_of_injective C.subtype_injective]
    exact Sylow.card_eq_multiplicity S0
  obtain ⟨a, hCPcardPow⟩ := hCPp.exists_card_eq
  have hfacC_le_a : (Nat.card C).factorization p ≤ a := by
    have hfac := Nat.factorization_le_factorization_of_dvd_right
      (a := p) (Subgroup.card_dvd_of_le hSCP)
      Nat.card_pos.ne' Nat.card_pos.ne'
    rw [hScard, hCPcardPow, Nat.factorization_pow_self hp,
      Nat.factorization_pow_self hp] at hfac
    exact hfac
  have ha_le_facC : a ≤ (Nat.card C).factorization p := by
    have hfac := Nat.factorization_le_factorization_of_dvd_right
      (a := p) (Subgroup.card_dvd_of_le hCPC)
      Nat.card_pos.ne' Nat.card_pos.ne'
    rw [hCPcardPow, Nat.factorization_pow_self hp] at hfac
    exact hfac
  have ha : a = (Nat.card C).factorization p :=
    Nat.le_antisymm ha_le_facC hfacC_le_a
  have hCPcard : Nat.card CP = p ^ (Nat.card C).factorization p := by
    rw [hCPcardPow, ha]
  have hindex : (C.subgroupOf D).index = theorem4bM M z := by
    simpa [C, D, Ct] using
      hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
        hzM hz ht htM
  have hcardSub : Nat.card (C.subgroupOf D) = Nat.card C :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show C ≤ D from inf_le_left))
  have hcardC : Nat.card C * theorem4bM M z = Nat.card D := by
    rw [← hcardSub, ← hindex]
    exact (C.subgroupOf D).card_mul_index
  have hmne : theorem4bM M z ≠ 0 := by
    rw [← hindex]
    exact Subgroup.index_ne_zero_of_finite
  have hfacC :
      (Nat.card C).factorization p +
          (theorem4bM M z).factorization p =
        (Nat.card D).factorization p := by
    have hfac := congrArg (fun n : ℕ => n.factorization p) hcardC
    change (Nat.card C * theorem4bM M z).factorization p =
      (Nat.card D).factorization p at hfac
    have hmulFac :
        (Nat.card C * theorem4bM M z).factorization p =
          (Nat.card C).factorization p +
            (theorem4bM M z).factorization p := by
      have hmulFacAll := Nat.factorization_mul (a := Nat.card C)
        (b := theorem4bM M z) Nat.card_pos.ne' hmne
      simpa using congrArg (fun f : ℕ →₀ ℕ => f p) hmulFacAll
    exact hmulFac.symm.trans hfac
  have hpPartEq :
      Nat.card CP * theorem4bPrimeShare M z p = Nat.card P := by
    calc
      Nat.card CP * theorem4bPrimeShare M z p =
          p ^ ((Nat.card C).factorization p +
            (theorem4bM M z).factorization p) := by
              rw [hCPcard, theorem4bPrimeShare, pow_add]
      _ = p ^ (Nat.card D).factorization p := by rw [hfacC]
      _ = Nat.card P := hPcard.symm
  have hmul :
      Nat.card CP * theorem4bInvertedCard t P =
        Nat.card CP * theorem4bPrimeShare M z p := by
    exact hfixed.symm.trans hpPartEq.symm
  exact Nat.mul_left_cancel Nat.card_pos hmul

/-- Proposition 3.8(b), upper half: every normalized `p`-subgroup of the
base two-point stabilizer has at most `m_p` inverted elements.  The proof
transports the pair of nonbase points to the base/intersection coordinates of
Proposition 3.7, preserving the inverted-set cardinality by conjugation. -/
public theorem IsStronglyEmbedded.theorem4b_invertedCard_le_primeShare_of_stabilizer
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X} {p : ℕ}
    {beta : conjugateCosetSpace M} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z) (hp : Nat.Prime p)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hPp : IsPGroup p P)
    (hPD : P ≤ M ⊓ MulAction.stabilizer X beta)
    (hzNormP : z ∈ Subgroup.normalizer (P : Set X)) :
    theorem4bInvertedCard z P ≤ theorem4bPrimeShare M z p := by
  have hzBase : z • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact hzM
  have hzMoves : z • beta ≠ beta := by
    intro hzBeta
    apply hbeta
    exact (hM.involution_fixed_coset_unique hz).unique hzBeta hzBase
  rcases QuotientGroup.mk_surjective beta with ⟨g, rfl⟩
  let t : X := rightConjugateElem z g
  have ht : IsInvolution t := by
    simpa [t] using isInvolution_rightConjugateElem (x := z) (g := g) hz
  have hzNotStab : z ∉ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) := by
    intro hzStab
    exact hzMoves (MulAction.mem_stabilizer_iff.mp hzStab)
  have htM : t ∉ M := by
    intro htM
    apply hzNotStab
    rw [conjugateCoset_stabilizer]
    have hmem := rightConjugateElem_mem_rightConjugate
      (g := g⁻¹) htM
    simpa [t, rightConjugateElem, mul_assoc] using hmem
  let P' : Subgroup X := P.conjBy g⁻¹
  have hPp' : IsPGroup p P' := by
    exact hPp.map (MulAut.conj g⁻¹).toMonoidHom
  have hPbeta : P ≤ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) :=
    hPD.trans inf_le_right
  have hPzbeta : P ≤ MulAction.stabilizer X
      (z • (QuotientGroup.mk g : conjugateCosetSpace M)) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      hzNormP hPbeta
  have hP'D : P' ≤ M ⊓ rightConjugate M t := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxP, rfl⟩
    constructor
    · have hxRight : x ∈ rightConjugate M g⁻¹ := by
        rw [← conjugateCoset_stabilizer]
        exact hPbeta hxP
      simpa [rightConjugateElem, MulAut.conj_apply] using
        rightConjugateElem_mem_of_mem_rightConjugate hxRight
    · have hxRight : x ∈ rightConjugate M (z * g)⁻¹ := by
        rw [← conjugateCoset_stabilizer]
        simpa using hPzbeta hxP
      have hmM : rightConjugateElem x (z * g) ∈ M :=
        rightConjugateElem_mem_of_mem_rightConjugate hxRight
      have hmem := rightConjugateElem_mem_rightConjugate
        (g := t) hmM
      have heq :
          rightConjugateElem (rightConjugateElem x (z * g)) t =
            (MulAut.conj g⁻¹) x := by
        have hzz : z * z = 1 := by
          simpa [pow_two] using hz.sq_eq_one
        simp [t, rightConjugateElem, MulAut.conj_apply, hz.inv_eq_self,
          hzz, mul_assoc]
        calc
          z * (z * (x * (z * (z * g)))) =
              (z * z) * x * (z * z) * g := by group
          _ = x * g := by rw [hzz]; simp
      rw [heq] at hmem
      exact hmem
  have hPfix : P.conjBy z = P :=
    section11_conjBy_eq_of_mem_normalizer hzNormP
  have hP'fix : P'.conjBy t = P' := by
    calc
      P'.conjBy t = P.conjBy (g⁻¹ * z) := by
        rw [show P' = P.conjBy g⁻¹ from rfl,
          Subgroup.conjBy_conjBy]
        congr 1
        simp [t, rightConjugateElem, mul_assoc]
      _ = (P.conjBy z).conjBy g⁻¹ :=
        (Subgroup.conjBy_conjBy P z g⁻¹).symm
      _ = P.conjBy g⁻¹ := by rw [hPfix]
      _ = P' := rfl
  have htNormP' : t ∈ Subgroup.normalizer (P' : Set X) := by
    have hforward {x : X} (hx : x ∈ P') : t * x * t⁻¹ ∈ P' := by
      rw [← hP'fix]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward
    · intro hx
      have hback := hforward hx
      have htt : t * t = 1 := by
        simpa [pow_two] using ht.sq_eq_one
      have hcancel : t * (t * x * t) * t = x := by
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rw [ht.inv_eq_self, hcancel] at hback
      exact hback
  have hupper :=
    hM.theorem4b_inf_rightConjugate_invertedCard_le_primeShare
      hzM hz ht htM hp hPp' hP'D htNormP'
  have hcard := theorem4bInvertedCard_conjBy z g P
  rw [← hcard]
  simpa [t, P'] using hupper

/-- Proposition 3.6(d), in the form needed for Proposition 3.8: at every
nonbase point, the index of the `z`-centralizer in the two-point stabilizer is
the base parameter `m = |M : C_M(z)|`. -/
public theorem IsStronglyEmbedded.theorem4b_twoPoint_centralizer_index_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X} {beta : conjugateCosetSpace M}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    ((((M ⊓ MulAction.stabilizer X beta) ⊓
          Subgroup.centralizer ({z} : Set X)).subgroupOf
        (M ⊓ MulAction.stabilizer X beta))).index = theorem4bM M z := by
  rcases QuotientGroup.mk_surjective beta with ⟨g, rfl⟩
  have hgInvNotM : g⁻¹ ∉ M := by
    intro hgInvM
    apply hbeta
    exact QuotientGroup.eq.mpr (by simpa using hgInvM)
  obtain ⟨t, htCoset, ht⟩ :=
    (hM.existsUnique_involution_in_centralizer_rightCoset
      hzM hz hgInvNotM).exists
  have htgM : t * g ∈ M :=
    hM.centralizer_le hzM hz (by simpa using htCoset)
  have htM : t ∉ M := by
    intro htM
    apply hgInvNotM
    have hgInvEq : g⁻¹ = (t * g)⁻¹ * t := by group
    rw [hgInvEq]
    exact M.mul_mem (M.inv_mem htgM) htM
  have hright : rightConjugate M t = rightConjugate M g⁻¹ := by
    have htEq : t = (t * g) * g⁻¹ := by simp
    change M.conjBy t⁻¹ = M.conjBy (g⁻¹)⁻¹
    rw [htEq, mul_inv_rev, inv_inv, Subgroup.conjBy_mul]
    have hconj : M.conjBy (t * g)⁻¹ = M :=
      section11_conjBy_eq_of_mem_normalizer
        ((Subgroup.normalizer (M : Set X)).inv_mem
          (Subgroup.le_normalizer htgM))
    rw [hconj]
  rw [conjugateCoset_stabilizer, ← hright]
  exact theorem4b_inf_rightConjugate_centralizer_index_eq hM hzM hz ht htM

/-- The `p`-part of the two-point stabilizer factors as the `p`-part of its
`z`-centralizer times the source parameter `m_p`. -/
public theorem IsStronglyEmbedded.theorem4b_twoPoint_primePart_mul_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X} {p : ℕ}
    {beta : conjugateCosetSpace M}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    p ^ (Nat.card ((M ⊓ MulAction.stabilizer X beta) ⊓
          Subgroup.centralizer ({z} : Set X) : Subgroup X)).factorization p *
        theorem4bPrimeShare M z p =
      p ^ (Nat.card (M ⊓ MulAction.stabilizer X beta : Subgroup X)).factorization p := by
  let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
  let C : Subgroup X := Subgroup.centralizer ({z} : Set X)
  let HD : Subgroup X := D ⊓ C
  have hindex : (HD.subgroupOf D).index = theorem4bM M z := by
    simpa [HD, D, C] using
      hM.theorem4b_twoPoint_centralizer_index_eq hzM hz hbeta
  have hcardSub : Nat.card (HD.subgroupOf D) = Nat.card HD :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show HD ≤ D from inf_le_left))
  have hcardHD :
      Nat.card HD * theorem4bM M z = Nat.card D := by
    rw [← hcardSub, ← hindex]
    exact (HD.subgroupOf D).card_mul_index
  have hmne : theorem4bM M z ≠ 0 := by
    rw [← hindex]
    exact Subgroup.index_ne_zero_of_finite
  have hfacHD :
      (Nat.card HD).factorization p + (theorem4bM M z).factorization p =
        (Nat.card D).factorization p := by
    have hfac := congrArg (fun n : ℕ => n.factorization p) hcardHD
    change (Nat.card HD * theorem4bM M z).factorization p =
      (Nat.card D).factorization p at hfac
    have hmulFac :
        (Nat.card HD * theorem4bM M z).factorization p =
          (Nat.card HD).factorization p +
            (theorem4bM M z).factorization p := by
      have hmulFacAll := Nat.factorization_mul (a := Nat.card HD)
        (b := theorem4bM M z) Nat.card_pos.ne' hmne
      simpa using congrArg (fun f : ℕ →₀ ℕ => f p) hmulFacAll
    exact hmulFac.symm.trans hfac
  calc
    p ^ (Nat.card HD).factorization p * theorem4bPrimeShare M z p =
        p ^ ((Nat.card HD).factorization p +
          (theorem4bM M z).factorization p) := by
            rw [theorem4bPrimeShare, pow_add]
    _ = p ^ (Nat.card D).factorization p := by rw [hfacHD]

/-- The lower half of Proposition 3.8(b): a normalized Sylow subgroup of a
two-point stabilizer has at least the source `m_p` inverted elements. -/
public theorem IsStronglyEmbedded.theorem4b_primeShare_le_invertedCard_of_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X} {p : ℕ}
    {beta : conjugateCosetSpace M} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z) (hp : Nat.Prime p)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hzNormP : z ∈ Subgroup.normalizer (P : Set X))
    (hPSylow : theorem4bIsSylowSubgroupOf p P
      (M ⊓ MulAction.stabilizer X beta)) :
    theorem4bPrimeShare M z p ≤ theorem4bInvertedCard z P := by
  let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
  let C : Subgroup X := Subgroup.centralizer ({z} : Set X)
  let HD : Subgroup X := D ⊓ C
  let CP : Subgroup X := P ⊓ C
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPSylow with ⟨Q, hPQ⟩
  have hPD : P ≤ D := by
    rw [hPQ]
    simpa [D] using
      (Subgroup.map_le_range D.subtype (Q : Subgroup D))
  have hPp : IsPGroup p P := by
    rw [hPQ]
    exact Q.isPGroup'.map D.subtype
  have hPcard : Nat.card P = p ^ (Nat.card D).factorization p := by
    rw [hPQ, Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.base_inf_stabilizer_card_odd hbeta
  have hPodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hPD)
  have hfixed :
      Nat.card P = Nat.card CP * theorem4bInvertedCard z P := by
    simpa [CP, C] using
      theorem4b_card_eq_card_fixed_mul_inverted hz hPodd hzNormP
  have hCPHD : CP ≤ HD := by
    exact inf_le_inf hPD le_rfl
  have hCPdvd : Nat.card CP ∣ Nat.card HD :=
    Subgroup.card_dvd_of_le hCPHD
  have hCPp : IsPGroup p CP := by
    exact hPp.to_inf_left
  obtain ⟨a, hCPcard⟩ := hCPp.exists_card_eq
  have ha_le : a ≤ (Nat.card HD).factorization p := by
    have hfac := Nat.factorization_le_factorization_of_dvd_right
      (a := p) hCPdvd Nat.card_pos.ne' Nat.card_pos.ne'
    rw [hCPcard, Nat.factorization_pow_self hp] at hfac
    exact hfac
  have hCPle : Nat.card CP ≤ p ^ (Nat.card HD).factorization p := by
    rw [hCPcard]
    exact Nat.pow_le_pow_right hp.pos ha_le
  have hindex : (HD.subgroupOf D).index = theorem4bM M z := by
    simpa [HD, D, C] using
      hM.theorem4b_twoPoint_centralizer_index_eq hzM hz hbeta
  have hcardSub : Nat.card (HD.subgroupOf D) = Nat.card HD :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show HD ≤ D from inf_le_left))
  have hcardHD :
      Nat.card HD * theorem4bM M z = Nat.card D := by
    rw [← hcardSub, ← hindex]
    exact (HD.subgroupOf D).card_mul_index
  have hmne : theorem4bM M z ≠ 0 := by
    rw [← hindex]
    exact Subgroup.index_ne_zero_of_finite
  have hfacHD :
      (Nat.card HD).factorization p + (theorem4bM M z).factorization p =
        (Nat.card D).factorization p := by
    have hfac := congrArg (fun n : ℕ => n.factorization p) hcardHD
    change (Nat.card HD * theorem4bM M z).factorization p =
      (Nat.card D).factorization p at hfac
    have hmulFac :
        (Nat.card HD * theorem4bM M z).factorization p =
          (Nat.card HD).factorization p +
            (theorem4bM M z).factorization p := by
      have hmulFacAll := Nat.factorization_mul (a := Nat.card HD)
        (b := theorem4bM M z) Nat.card_pos.ne' hmne
      simpa using congrArg (fun f : ℕ →₀ ℕ => f p) hmulFacAll
    exact hmulFac.symm.trans hfac
  have hpPartEq :
      p ^ (Nat.card HD).factorization p * theorem4bPrimeShare M z p =
        Nat.card P := by
    calc
      p ^ (Nat.card HD).factorization p * theorem4bPrimeShare M z p =
          p ^ ((Nat.card HD).factorization p +
            (theorem4bM M z).factorization p) := by
              rw [theorem4bPrimeShare, pow_add]
      _ = p ^ (Nat.card D).factorization p := by rw [hfacHD]
      _ = Nat.card P := hPcard.symm
  have hmulLe :
      p ^ (Nat.card HD).factorization p * theorem4bPrimeShare M z p ≤
        p ^ (Nat.card HD).factorization p * theorem4bInvertedCard z P := by
    calc
      p ^ (Nat.card HD).factorization p * theorem4bPrimeShare M z p =
          Nat.card CP * theorem4bInvertedCard z P := hpPartEq.trans hfixed
      _ ≤ p ^ (Nat.card HD).factorization p * theorem4bInvertedCard z P :=
        Nat.mul_le_mul_right _ hCPle
  exact Nat.le_of_mul_le_mul_left hmulLe (pow_pos hp.pos _)

/-- The exact Proposition 3.8(b) contract follows from the checked
Proposition 3.6/3.7 counting route. -/
public theorem IsStronglyEmbedded.theorem4b_proposition38bAtBase
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) :
    Theorem4bProposition38bAtBase M := by
  intro z p beta P hz hzM hp hPp hPM hPbeta hbeta hzNormP
  have hPD : P ≤ M ⊓ MulAction.stabilizer X beta := le_inf hPM hPbeta
  have hupper := hM.theorem4b_invertedCard_le_primeShare_of_stabilizer
    hzM hz hp hbeta hPp hPD hzNormP
  refine ⟨hupper, ?_⟩
  intro hPSylow
  exact Nat.le_antisymm hupper
    (hM.theorem4b_primeShare_le_invertedCard_of_sylow
      hzM hz hp hbeta hzNormP hPSylow)

/-- Proposition 3.8(c), assembled from Proposition 3.8(a,b), invariant Sylow
extension in the triple stabilizer, and the centralizer/index count. -/
public theorem IsStronglyEmbedded.theorem4b_proposition38cAtBase
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) :
    Theorem4bProposition38cAtBase M := by
  intro z p beta hz hzM hp hbeta
  let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
  let E : Subgroup X := D ⊓ MulAction.stabilizer X (z • beta)
  let C : Subgroup X := Subgroup.centralizer ({z} : Set X)
  let CD : Subgroup X := D ⊓ C
  let CE : Subgroup X := E ⊓ C
  letI : Fact p.Prime := ⟨hp⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.base_inf_stabilizer_card_odd hbeta
  have hEodd : Odd (Nat.card E) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le inf_le_left)
  have hzNormE : z ∈ Subgroup.normalizer (E : Set X) := by
    simpa [E, D] using
      theorem4b_mem_normalizer_tripleStabilizer hz hzM
  have hCEeq : CE = CD := by
    simpa [CE, CD, E, D, C] using
      theorem4b_tripleStabilizer_inf_centralizer_eq M z beta
  constructor
  · rintro ⟨Q, hQSylow, hzNormQ⟩
    obtain ⟨Qd, hQeq⟩ := hQSylow
    have hQD : Q ≤ D := by
      rw [hQeq]
      simpa using
        (Subgroup.map_le_range D.subtype (Qd : Subgroup D))
    have hQp : IsPGroup p Q := by
      rw [hQeq]
      exact Qd.isPGroup'.map D.subtype
    refine ⟨Q, hQp, hQD, hzNormQ, ?_⟩
    have h38b := hM.theorem4b_proposition38bAtBase
      z p beta Q hz hzM hp hQp (hQD.trans inf_le_left)
        (hQD.trans inf_le_right) hbeta hzNormQ
    exact h38b.2 ⟨Qd, hQeq⟩
  · rintro ⟨P, hPp, hPD, hzNormP, hPinv⟩
    have hPE : P ≤ E := by
      simpa [E, D] using
        theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
          hzNormP hPD
    obtain ⟨Q, hQSylowE, hPQ, hzNormQ⟩ :=
      theorem4b_exists_invariant_sylow_containing
        hEodd hz hzNormE hp hPp hPE hzNormP
    obtain ⟨Qe, hQeq⟩ := hQSylowE
    have hQE : Q ≤ E := by
      rw [hQeq]
      simpa using
        (Subgroup.map_le_range E.subtype (Qe : Subgroup E))
    have hQD : Q ≤ D := hQE.trans inf_le_left
    have hQp : IsPGroup p Q := by
      rw [hQeq]
      exact Qe.isPGroup'.map E.subtype
    obtain ⟨S, hSSylow, hSQ⟩ :=
      theorem4b_exists_centralizer_sylow_le_of_invariant_sylow
        hEodd hz hzNormE hp hzNormQ ⟨Qe, hQeq⟩
    obtain ⟨Se, hSeq⟩ := hSSylow
    have hSCE : S ≤ CE := by
      rw [hSeq]
      simpa using
        (Subgroup.map_le_range CE.subtype (Se : Subgroup CE))
    have hScard : Nat.card S = p ^ (Nat.card CE).factorization p := by
      rw [hSeq, Subgroup.card_map_of_injective CE.subtype_injective]
      exact Sylow.card_eq_multiplicity Se
    let CQ : Subgroup X := Q ⊓ C
    have hSleCQ : S ≤ CQ := le_inf hSQ (hSCE.trans inf_le_right)
    have hcentralPartLe :
        p ^ (Nat.card CD).factorization p ≤ Nat.card CQ := by
      calc
        p ^ (Nat.card CD).factorization p =
            p ^ (Nat.card CE).factorization p := by rw [hCEeq]
        _ = Nat.card S := hScard.symm
        _ ≤ Nat.card CQ := Subgroup.card_le_of_le hSleCQ
    have hinvertedLe : theorem4bPrimeShare M z p ≤
        theorem4bInvertedCard z Q := by
      calc
        theorem4bPrimeShare M z p = theorem4bInvertedCard z P := hPinv.symm
        _ ≤ theorem4bInvertedCard z Q := theorem4bInvertedCard_mono hPQ
    have hQodd : Odd (Nat.card Q) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hQD)
    have hQfactor :
        Nat.card Q = Nat.card CQ * theorem4bInvertedCard z Q := by
      simpa [CQ, C] using
        theorem4b_card_eq_card_fixed_mul_inverted hz hQodd hzNormQ
    have hprimePart :
        p ^ (Nat.card CD).factorization p * theorem4bPrimeShare M z p =
          p ^ (Nat.card D).factorization p := by
      simpa [CD, D, C] using
        hM.theorem4b_twoPoint_primePart_mul_eq hzM hz hbeta (p := p)
    have htargetLe :
        p ^ (Nat.card D).factorization p ≤ Nat.card Q := by
      rw [← hprimePart, hQfactor]
      exact Nat.mul_le_mul hcentralPartLe hinvertedLe
    have hQdvd : Nat.card Q ∣ Nat.card D :=
      Subgroup.card_dvd_of_le hQD
    obtain ⟨a, hQcardPow⟩ := hQp.exists_card_eq
    have ha_le : a ≤ (Nat.card D).factorization p := by
      have hfac := Nat.factorization_le_factorization_of_dvd_right
        (a := p) hQdvd Nat.card_pos.ne' Nat.card_pos.ne'
      rw [hQcardPow, Nat.factorization_pow_self hp] at hfac
      exact hfac
    have hQle : Nat.card Q ≤ p ^ (Nat.card D).factorization p := by
      rw [hQcardPow]
      exact Nat.pow_le_pow_right hp.pos ha_le
    have hQcard : Nat.card Q = p ^ (Nat.card D).factorization p :=
      Nat.le_antisymm hQle htargetLe
    have hQdcard : Nat.card (Q.subgroupOf D) =
        p ^ (Nat.card D).factorization p := by
      rw [natCard_subgroupOf_eq Q D hQD, hQcard]
    refine ⟨Q, ?_, hzNormQ⟩
    refine ⟨Sylow.ofCard (Q.subgroupOf D) hQdcard, ?_⟩
    have hmap := Subgroup.subgroupOf_map_subtype Q D
    change Q = (Q.subgroupOf D).map D.subtype
    exact (inf_eq_left.mpr hQD).symm.trans hmap.symm

/-- A subgroup of the base stabilizer fixes the distinguished base coset. -/
public theorem theorem4b_baseCoset_mem_fixedPoints
    {X : Type u} [Group X] {M W : Subgroup X} (hWM : W ≤ M) :
    (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) W := by
  intro w hw
  apply MulAction.mem_stabilizer_iff.mp
  rw [baseCoset_stabilizer M]
  exact hWM hw

/-- The literal counterexample obtained by negating the base-point form of
Theorem 4(b).  The fixed-point lower bound is the honest negation of the
singleton alternative; no conclusion of Theorem 4(b) is assumed here. -/
public structure Theorem4bCounterexample
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) where
  z : X
  W : Subgroup X
  hz : IsInvolution z
  hzM : z ∈ M
  hWodd : Odd (Nat.card W)
  hWM : W ≤ M
  hzNorm : z ∈ Subgroup.normalizer (W : Set X)
  hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set X)
  hfixed : 2 ≤ Nat.card (theorem4bFixedPoints M W)

/-- The source configuration `(6A)`: an odd-prime subgroup on which `z` acts
nontrivially, saturated by the action commutator, and fixing more than one
point. -/
public structure Theorem4bSixA
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) where
  p : ℕ
  hp : Nat.Prime p
  hpOdd : Odd p
  z : X
  W : Subgroup X
  hz : IsInvolution z
  hzM : z ∈ M
  hWp : IsPGroup p W
  hWM : W ≤ M
  hzNorm : z ∈ Subgroup.normalizer (W : Set X)
  hcomm : ⁅W, Subgroup.zpowers z⁆ = W
  hWne : W ≠ ⊥
  hfixed : 2 ≤ Nat.card (theorem4bFixedPoints M W)

/-- A noncentral action of an involution on an odd subgroup contains a
nonidentity element inverted by the involution. -/
public theorem Theorem4bCounterexample.exists_inverted
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bCounterexample M) :
    ∃ x : X, x ∈ d.W ∧ x ≠ 1 ∧ d.z * x * d.z⁻¹ = x⁻¹ := by
  rcases SetLike.not_le_iff_exists.mp d.hnot with ⟨w, hwW, hwNot⟩
  have hzwW : d.z * w * d.z⁻¹ ∈ d.W :=
    (Subgroup.mem_normalizer_iff.mp d.hzNorm w).mp hwW
  let x : X := w⁻¹ * (d.z * w * d.z⁻¹)
  have hxW : x ∈ d.W := d.W.mul_mem (d.W.inv_mem hwW) hzwW
  have hxne : x ≠ 1 := by
    intro hx
    apply hwNot
    rw [Subgroup.mem_centralizer_singleton_iff]
    have heq : w = d.z * w * d.z⁻¹ := eq_of_inv_mul_eq_one hx
    calc
      w * d.z = (d.z * w * d.z⁻¹) * d.z :=
        congrArg (fun q : X => q * d.z) heq
      _ = d.z * w := by simp [mul_assoc]
  have hz2 : d.z * d.z = 1 := by
    simpa [pow_two] using d.hz.sq_eq_one
  have hzinv : d.z * x * d.z⁻¹ = x⁻¹ := by
    rw [d.hz.inv_eq_self]
    dsimp only [x]
    simp only [d.hz.inv_eq_self]
    calc
      d.z * (w⁻¹ * (d.z * w * d.z)) * d.z =
          d.z * w⁻¹ * d.z * w := by simp [mul_assoc, hz2]
      _ = (d.z * w * d.z)⁻¹ * w := by
        simp [d.hz.inv_eq_self, mul_assoc]
      _ = (w⁻¹ * (d.z * w * d.z))⁻¹ := by simp
  exact ⟨x, hxW, hxne, hzinv⟩

/-- Prime-order extraction from an inverted element, preserving inversion. -/
public theorem exists_prime_order_inverted_of_mem_odd_subgroup
    {X : Type u} [Group X] [Finite X]
    {z x : X} {W : Subgroup X}
    (hxW : x ∈ W) (hxne : x ≠ 1)
    (hzx : z * x * z⁻¹ = x⁻¹) (hWodd : Odd (Nat.card W)) :
    ∃ (p : ℕ) (y : X), Nat.Prime p ∧ orderOf y = p ∧ y ∈ W ∧
      y ≠ 1 ∧ z * y * z⁻¹ = y⁻¹ := by
  have horder_ne : orderOf x ≠ 1 := by
    intro h
    exact hxne (orderOf_eq_one_iff.mp h)
  have horder_dvd : orderOf x ∣ Nat.card W := by
    simpa using orderOf_dvd_natCard (⟨x, hxW⟩ : W)
  have horder_odd : Odd (orderOf x) := hWodd.of_dvd_nat horder_dvd
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd horder_ne
  letI : Fact p.Prime := ⟨hp⟩
  let H : Subgroup X := Subgroup.zpowers x
  have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
  have hpdivH : p ∣ Nat.card H := by simpa [hcardH] using hpdiv
  obtain ⟨yH, hyHorder⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpdivH
  let y : X := yH
  have hyW : y ∈ W := by
    change (yH : X) ∈ W
    exact Subgroup.zpowers_le.mpr hxW yH.property
  have hyorder : orderOf y = p := by simpa [y] using hyHorder
  have hyne : y ≠ 1 := by
    intro h
    have : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    exact hp.ne_one (by simpa [hyorder] using this)
  have hyPow : ∃ n : ℤ, y = x ^ n := by
    rcases Subgroup.mem_zpowers_iff.mp yH.property with ⟨n, hn⟩
    exact ⟨n, by simpa [y] using hn.symm⟩
  have hzy : z * y * z⁻¹ = y⁻¹ := by
    rcases hyPow with ⟨n, hn⟩
    rw [hn, ← zpow_neg]
    calc
      z * x ^ n * z⁻¹ = (z * x * z⁻¹) ^ n := by simp
      _ = (x⁻¹) ^ n := by rw [hzx]
      _ = x ^ (-n) := by simp
  exact ⟨p, y, hp, hyorder, hyW, hyne, hzy⟩

/-- An involution inverting `y` normalizes the cyclic subgroup generated by
`y`. -/
public theorem theorem4b_mem_normalizer_zpowers_of_inverts
    {X : Type u} [Group X] {z y : X} (hz : IsInvolution z)
    (hzy : z * y * z⁻¹ = y⁻¹) :
    z ∈ Subgroup.normalizer (Subgroup.zpowers y : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  have hsemi : SemiconjBy z y y⁻¹ := by
    rw [SemiconjBy]
    calc
      z * y = (z * y * z⁻¹) * z := by simp [mul_assoc]
      _ = y⁻¹ * z := by rw [hzy]
  have hforward : ∀ x : X, x ∈ Subgroup.zpowers y →
      z * x * z⁻¹ ∈ Subgroup.zpowers y := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-n, ?_⟩
    have hpow := hsemi.zpow_right n
    rw [SemiconjBy] at hpow
    calc
      y ^ (-n) = (y⁻¹) ^ n := by simp
      _ = z * y ^ n * z⁻¹ := by
        symm
        calc
          z * y ^ n * z⁻¹ = (y⁻¹ ^ n * z) * z⁻¹ := by rw [hpow]
          _ = y⁻¹ ^ n := by simp
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h2 := hforward (z * x * z⁻¹) hx
    have hzz : z * z = 1 := by simpa [pow_two] using hz.sq_eq_one
    have heq : z * (z * x * z⁻¹) * z⁻¹ = x := by
      rw [hz.inv_eq_self]
      calc
        z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; simp
    rw [heq] at h2
    exact h2

/-- An odd prime-order element inverted by `z` generates the whole action
commutator. -/
public theorem commutator_zpowers_eq_of_inverts_prime
    {X : Type u} [Group X] [Finite X]
    {z y : X} (hz : IsInvolution z) (hyne : y ≠ 1)
    (hzy : z * y * z⁻¹ = y⁻¹) (hp : Nat.Prime (orderOf y))
    (hyodd : Odd (orderOf y)) :
    ⁅Subgroup.zpowers y, Subgroup.zpowers z⁆ = Subgroup.zpowers y := by
  let P : Subgroup X := Subgroup.zpowers y
  let A : Subgroup X := Subgroup.zpowers z
  have hPcard : Nat.card P = orderOf y := by simp [P]
  letI : Fact (Nat.card P).Prime := ⟨by simpa [hPcard] using hp⟩
  have hA_norm_P : A ≤ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.zpowers_le]
    simpa [P] using theorem4b_mem_normalizer_zpowers_of_inverts hz hzy
  letI : Subgroup.Normalizes A P := ⟨hA_norm_P⟩
  have hcommAction_ne_bot : commutatorAction (A := A) (G := P) ≠ ⊥ := by
    intro hbot
    let hyP : P := ⟨y, Subgroup.mem_zpowers y⟩
    let az : A := ⟨z, Subgroup.mem_zpowers z⟩
    have hgen : hyP⁻¹ * (az • hyP) ∈ commutatorAction (A := A) (G := P) := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨az, hyP, rfl⟩
    rw [hbot] at hgen
    have hgen_one : hyP⁻¹ * (az • hyP) = 1 := by simpa using hgen
    have hyfix : hyP = az • hyP := eq_of_inv_mul_eq_one hgen_one
    have hyfixX : y = y⁻¹ := by
      have hco := congrArg Subtype.val hyfix
      have hsmul :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe A P az hyP
      have hcoX : y = z * y * z⁻¹ := by
        simpa [hyP, az] using hco.trans hsmul
      exact hcoX.trans hzy
    have hy2 : y ^ 2 = 1 := by
      calc
        y ^ 2 = y * y := by rw [pow_two]
        _ = y * y⁻¹ := congrArg (fun q : X => y * q) hyfixX
        _ = 1 := by simp
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with horder | horder
    · exact hyne (orderOf_eq_one_iff.mp horder)
    · exact hyodd.not_two_dvd_nat (by simp [horder])
  have hcommAction_top : commutatorAction (A := A) (G := P) = ⊤ := by
    exact (commutatorAction (A := A) (G := P)).eq_bot_or_eq_top_of_prime_card
      |>.resolve_left hcommAction_ne_bot
  have hmap :
      (commutatorAction (A := A) (G := P)).map P.subtype =
        ⁅P, A⁆ := commutatorAction_subgroup_conj_map_eq_commutator P A hA_norm_P
  calc
    ⁅Subgroup.zpowers y, Subgroup.zpowers z⁆ = ⁅P, A⁆ := by rfl
    _ = (commutatorAction (A := A) (G := P)).map P.subtype := hmap.symm
    _ = P := by
      rw [hcommAction_top]
      apply le_antisymm
      · exact Subgroup.map_subtype_le ⊤
      · intro x hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩

/-- Failure of Theorem 4(b) yields the source's prime-order configuration
`(6A)`; the construction is internal and only the source hypotheses are
retained. -/
public theorem Theorem4bCounterexample.toSixA
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bCounterexample M) : Nonempty (Theorem4bSixA M) := by
  obtain ⟨x, hxW, hxne, hzx⟩ := d.exists_inverted
  obtain ⟨p, y, hp, hyorder, hyW, hyne, hzy⟩ :=
    exists_prime_order_inverted_of_mem_odd_subgroup hxW hxne hzx d.hWodd
  let P : Subgroup X := Subgroup.zpowers y
  have horder_dvd : orderOf y ∣ Nat.card d.W := by
    simpa using orderOf_dvd_natCard (⟨y, hyW⟩ : d.W)
  have hyodd : Odd (orderOf y) := d.hWodd.of_dvd_nat horder_dvd
  have hpOdd : Odd p := by simpa [hyorder] using hyodd
  have hPcard : Nat.card P = p := by
    simpa [P, Nat.card_zpowers] using hyorder
  have hPp : IsPGroup p P := by
    apply IsPGroup.of_card (n := 1)
    simp [hPcard]
  have hPleW : P ≤ d.W := by
    simpa [P] using Subgroup.zpowers_le.mpr hyW
  have hPleM : P ≤ M := hPleW.trans d.hWM
  have hzNormP : d.z ∈ Subgroup.normalizer (P : Set X) := by
    simpa [P] using theorem4b_mem_normalizer_zpowers_of_inverts d.hz hzy
  have hcommP : ⁅P, Subgroup.zpowers d.z⁆ = P := by
    simpa [P] using commutator_zpowers_eq_of_inverts_prime d.hz hyne hzy
      (by simpa [hyorder] using hp) hyodd
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hybot : y ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers y
    exact hyne (by simpa using hybot)
  let f : theorem4bFixedPoints M d.W → theorem4bFixedPoints M P :=
    fun omega => ⟨omega.1, fun w hw => omega.2 w (hPleW hw)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hab
  have hfixedP : 2 ≤ Nat.card (theorem4bFixedPoints M P) :=
    d.hfixed.trans (Nat.card_le_card_of_injective f hf)
  exact ⟨⟨p, hp, hpOdd, d.z, P, d.hz, d.hzM, hPp, hPleM,
    hzNormP, hcommP, hPne, hfixedP⟩⟩

/-- The honest negation of the dichotomy is equivalent to the existence of a
concrete counterexample package. -/
public theorem not_Theorem4bAtBase_iff_nonempty_counterexample
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} :
    ¬ Theorem4bAtBase M ↔ Nonempty (Theorem4bCounterexample M) := by
  constructor
  · intro h
    rw [Theorem4bAtBase] at h
    push Not at h
    rcases h with ⟨z, W, hz, hzM, hWodd, hWM, hzNorm, hnot, hcard⟩
    have hbase := theorem4b_baseCoset_mem_fixedPoints hWM
    let p : theorem4bFixedPoints M W := ⟨QuotientGroup.mk 1, hbase⟩
    letI : Nonempty (theorem4bFixedPoints M W) := ⟨p⟩
    have hpos : 0 < Nat.card (theorem4bFixedPoints M W) := Nat.card_pos
    have htwo : 2 ≤ Nat.card (theorem4bFixedPoints M W) := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨Nat.ne_of_gt hpos, hcard⟩
    exact ⟨⟨z, W, hz, hzM, hWodd, hWM, hzNorm, hnot, htwo⟩⟩
  · rintro ⟨d⟩ h4b
    rcases h4b d.z d.W d.hz d.hzM d.hWodd d.hWM d.hzNorm with hc | hcard
    · exact d.hnot hc
    · have : 2 ≤ 1 := hcard ▸ d.hfixed
      omega

/-- A `(6A)` witness is already a genuine counterexample to Theorem 4(b). -/
public theorem Theorem4bSixA.not_Theorem4bAtBase
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : ¬ Theorem4bAtBase M := by
  letI : Fact d.p.Prime := ⟨d.hp⟩
  obtain ⟨n, hcard⟩ := d.hWp.exists_card_eq
  have hWodd : Odd (Nat.card d.W) := by
    rw [hcard]
    exact d.hpOdd.pow
  have hnot : ¬ d.W ≤ Subgroup.centralizer ({d.z} : Set X) := by
    intro hcentral
    have hcentralA :
        d.W ≤ Subgroup.centralizer (Subgroup.zpowers d.z : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hcentral
    have hbot : ⁅d.W, Subgroup.zpowers d.z⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralA
    exact d.hWne (d.hcomm.symm.trans hbot)
  intro h4b
  rcases h4b d.z d.W d.hz d.hzM hWodd d.hWM d.hzNorm with hcentral | hcardOne
  · exact hnot hcentral
  · have : 2 ≤ 1 := hcardOne ▸ d.hfixed
    omega

/-- The checked first step of the source proof: failure of Theorem 4(b) is
equivalent to the prime-order configuration `(6A)`. -/
public theorem not_Theorem4bAtBase_iff_nonempty_sixA
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} :
    ¬ Theorem4bAtBase M ↔ Nonempty (Theorem4bSixA M) := by
  constructor
  · intro h
    exact (not_Theorem4bAtBase_iff_nonempty_counterexample.mp h).elim
      Theorem4bCounterexample.toSixA
  · rintro ⟨d⟩
    exact d.not_Theorem4bAtBase

/-- The set `K = I_W(z)` from `(6C)`: the elements of `W` inverted by `z`. -/
public def Theorem4bSixA.invertedSet
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : Set X :=
  {x : X | x ∈ d.W ∧ d.z * x * d.z⁻¹ = x⁻¹}

/-- The source fixed-point set `Omega_K`, where `K = I_W(z)` is a set rather
than a subgroup. -/
public def Theorem4bSixA.kFixedPoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : Set (conjugateCosetSpace M) :=
  {beta | ∀ k : X, k ∈ d.invertedSet → k • beta = beta}

/-- Membership in the source inverted set, exposed without unfolding its
definition across module boundaries. -/
public theorem Theorem4bSixA.mem_invertedSet_iff
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) (x : X) :
    x ∈ d.invertedSet ↔
      x ∈ d.W ∧ d.z * x * d.z⁻¹ = x⁻¹ :=
  Iff.rfl

/-- Membership in `Omega_K`, exposed without unfolding its definition across
module boundaries. -/
public theorem Theorem4bSixA.mem_kFixedPoints_iff
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) (beta : conjugateCosetSpace M) :
    beta ∈ d.kFixedPoints ↔
      ∀ k : X, k ∈ d.invertedSet → k • beta = beta :=
  Iff.rfl

/-- A `(6A)` witness has a fixed point distinct from the base point. -/
public theorem Theorem4bSixA.exists_nonbase_fixedPoint
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    ∃ beta : conjugateCosetSpace M,
      beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) d.W ∧
        beta ≠ QuotientGroup.mk 1 := by
  let alpha : theorem4bFixedPoints M d.W :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints d.hWM⟩
  by_contra h
  push Not at h
  have hcardOne : Nat.card (theorem4bFixedPoints M d.W) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨alpha, ?_⟩
    intro beta
    apply Subtype.ext
    exact h beta.1 beta.2
  have : 2 ≤ 1 := hcardOne ▸ d.hfixed
  omega

/-- Every point fixed by `W` is fixed by the source set `K = I_W(z)`. -/
public theorem Theorem4bSixA.fixedPoints_subset_kFixedPoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    fixedPointsOfSubgroup X (conjugateCosetSpace M) d.W ⊆
      d.kFixedPoints := by
  intro beta hbeta k hk
  exact hbeta k hk.1

/-- Every elementary action commutator belongs to `I_W(z)`. -/
public theorem Theorem4bSixA.actionCommutator_mem_invertedSet
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) (w : d.W) :
    (w : X)⁻¹ * (d.z * (w : X) * d.z⁻¹) ∈ d.invertedSet := by
  have hzwW : d.z * (w : X) * d.z⁻¹ ∈ d.W :=
    (Subgroup.mem_normalizer_iff.mp d.hzNorm (w : X)).mp w.property
  constructor
  · exact d.W.mul_mem (d.W.inv_mem w.property) hzwW
  · have hz2 : d.z * d.z = 1 := by
      simpa [pow_two] using d.hz.sq_eq_one
    rw [d.hz.inv_eq_self]
    calc
      d.z * ((w : X)⁻¹ * (d.z * (w : X) * d.z)) * d.z =
          d.z * (w : X)⁻¹ * d.z * (w : X) := by simp [mul_assoc, hz2]
      _ = (d.z * (w : X) * d.z)⁻¹ * (w : X) := by
        simp [d.hz.inv_eq_self, mul_assoc]
      _ = ((w : X)⁻¹ * (d.z * (w : X) * d.z))⁻¹ := by simp

/-- The equality `⟨K⟩ = [z,W] = W` from `(6C)`. -/
public theorem Theorem4bSixA.closure_invertedSet_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : Subgroup.closure d.invertedSet = d.W := by
  let A : Subgroup X := Subgroup.zpowers d.z
  have hA_norm_W : A ≤ Subgroup.normalizer (d.W : Set X) := by
    rw [Subgroup.zpowers_le]
    exact d.hzNorm
  letI : Subgroup.Normalizes A d.W := ⟨hA_norm_W⟩
  let az : A := ⟨d.z, Subgroup.mem_zpowers d.z⟩
  have horder : orderOf d.z = 2 :=
    (orderOf_eq_prime_iff).2 ⟨d.hz.sq_eq_one, d.hz.ne_one⟩
  have hAcard : Nat.card A = 2 := by simp [A, Nat.card_zpowers, horder]
  have hazne : az ≠ 1 := by
    intro h
    exact d.hz.ne_one (congrArg Subtype.val h)
  have haCases (a : A) : a = 1 ∨ a = az := by
    by_cases ha : a = 1
    · exact Or.inl ha
    · right
      obtain ⟨other, hother, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
      exact (huniq a ha).trans (huniq az hazne).symm
  have hmap :
      (commutatorAction (A := A) (G := d.W)).map d.W.subtype =
        ⁅d.W, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator d.W A hA_norm_W
  have haction : ∀ w : d.W,
      w ∈ commutatorAction (A := A) (G := d.W) →
        (w : X) ∈ Subgroup.closure d.invertedSet := by
    intro w hw
    rw [commutatorAction_eq_closure] at hw
    refine Subgroup.closure_induction
      (p := fun q : d.W => fun _hq =>
        (q : X) ∈ Subgroup.closure d.invertedSet)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨a, g, rfl⟩
      rcases haCases a with rfl | rfl
      · simp
      · apply Subgroup.subset_closure
        simpa [az, A,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            d.actionCommutator_mem_invertedSet g
    · exact Subgroup.one_mem _
    · intro a b _ha _hb ha hb
      exact (Subgroup.closure d.invertedSet).mul_mem ha hb
    · intro a _ha ha
      exact (Subgroup.closure d.invertedSet).inv_mem ha
  have hcomm_le : ⁅d.W, A⁆ ≤ Subgroup.closure d.invertedSet := by
    intro x hx
    rw [← hmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨w, hw, rfl⟩
    exact haction w hw
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun _ hx => hx.1
  · rw [← d.hcomm]
    simpa [A] using hcomm_le

/-- Since `W = ⟨K⟩`, the points fixed by the source set `K = I_W(z)` are
exactly the points fixed by `W`. -/
public theorem Theorem4bSixA.kFixedPoints_subset_fixedPoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    d.kFixedPoints ⊆
      fixedPointsOfSubgroup X (conjugateCosetSpace M) d.W := by
  intro beta hbeta
  have hKle : d.invertedSet ⊆ MulAction.stabilizer X beta := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mpr (hbeta k hk)
  have hclosure :
      Subgroup.closure d.invertedSet ≤ MulAction.stabilizer X beta := by
    rw [Subgroup.closure_le]
    exact hKle
  rw [d.closure_invertedSet_eq] at hclosure
  exact fun w hw => MulAction.mem_stabilizer_iff.mp (hclosure hw)

/-- The remaining assertion `|K| > 1` from `(6C)`. -/
public theorem Theorem4bSixA.two_le_card_invertedSet
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    2 ≤ Nat.card {x : X // x ∈ d.invertedSet} := by
  have hKone : (1 : X) ∈ d.invertedSet := by
    simp [Theorem4bSixA.invertedSet]
  have hKne : ∃ k : X, k ∈ d.invertedSet ∧ k ≠ 1 := by
    by_contra h
    push Not at h
    have hclosureBot : Subgroup.closure d.invertedSet = ⊥ :=
      Subgroup.closure_eq_bot_iff.mpr (fun k hk => by simp [h k hk])
    exact d.hWne (d.closure_invertedSet_eq.symm.trans hclosureBot)
  rcases hKne with ⟨k, hk, hkne⟩
  let oneK : {x : X // x ∈ d.invertedSet} := ⟨1, hKone⟩
  let kK : {x : X // x ∈ d.invertedSet} := ⟨k, hk⟩
  letI : Nonempty {x : X // x ∈ d.invertedSet} := ⟨oneK⟩
  have hcardPos : 0 < Nat.card {x : X // x ∈ d.invertedSet} := Nat.card_pos
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  refine ⟨Nat.ne_of_gt hcardPos, ?_⟩
  intro hcardOne
  rcases Nat.card_eq_one_iff_exists.mp hcardOne with ⟨a, ha⟩
  apply hkne
  exact congrArg Subtype.val ((ha kK).trans (ha oneK).symm)

/-- A nontrivial normalized inverted set inside a `p`-subgroup fixing two
points can be saturated to a `(6A)` witness without changing its inverted-set
cardinality.  The saturated subgroup is the coprime action commutator. -/
public theorem exists_theorem4bSixA_of_normalized_pSubgroup
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z : X} {p : ℕ} {beta : conjugateCosetSpace M} {P : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hp : Nat.Prime p) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPD : P ≤ M ⊓ MulAction.stabilizer X beta)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hzNormP : z ∈ Subgroup.normalizer (P : Set X))
    (htwo : 2 ≤ theorem4bInvertedCard z P) :
    ∃ e : Theorem4bSixA M,
      Nat.card {x : X // x ∈ e.invertedSet} =
        theorem4bInvertedCard z P := by
  letI : Fact p.Prime := ⟨hp⟩
  let I : Set X := {x : X | x ∈ P ∧ z * x * z⁻¹ = x⁻¹}
  let W : Subgroup X := Subgroup.closure I
  let A : Subgroup X := Subgroup.zpowers z
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact hpOdd.pow
  have hWP : W ≤ P := by
    change Subgroup.closure I ≤ P
    rw [Subgroup.closure_le]
    exact fun _ hx => hx.1
  have hA_normP : A ≤ Subgroup.normalizer (P : Set X) := by
    change Subgroup.zpowers z ≤ Subgroup.normalizer (P : Set X)
    rw [Subgroup.zpowers_le]
    exact hzNormP
  have hforward : ∀ x : X, x ∈ W → z * x * z⁻¹ ∈ W := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun q : X => fun _hq => z * q * z⁻¹ ∈ W)
      ?_ ?_ ?_ ?_ hx
    · intro q hq
      rw [hq.2]
      exact W.inv_mem (Subgroup.subset_closure hq)
    · simp
    · intro a b _ha _hb ha hb
      have hab : z * (a * b) * z⁻¹ =
          (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      rw [hab]
      exact W.mul_mem ha hb
    · intro a _ha ha
      have hainv : z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
      rw [hainv]
      exact W.inv_mem ha
  have hzNormW : z ∈ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (z * x * z⁻¹) hx
      have hzz : z * z = 1 := by
        simpa [pow_two] using hz.sq_eq_one
      have hcancel : z * (z * x * z⁻¹) * z⁻¹ = x := by
        rw [hz.inv_eq_self]
        calc
          z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzz]; simp
      simpa only [hcancel] using hback
  have hA_normW : A ≤ Subgroup.normalizer (W : Set X) := by
    change Subgroup.zpowers z ≤ Subgroup.normalizer (W : Set X)
    rw [Subgroup.zpowers_le]
    exact hzNormW
  have hcomm : ⁅W, A⁆ = W := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx a ha
      have hconj : a * x⁻¹ * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hA_normW ha) x⁻¹).1 (W.inv_mem hx)
      simpa [commutatorElement_def, mul_assoc] using W.mul_mem hx hconj
    · change Subgroup.closure I ≤ ⁅W, A⁆
      rw [Subgroup.closure_le]
      intro x hx
      have hxW : x ∈ W := Subgroup.subset_closure hx
      have hzA : z ∈ A := Subgroup.mem_zpowers z
      have hx2 : x ^ 2 ∈ ⁅W, A⁆ := by
        have hc := Subgroup.commutator_mem_commutator hxW hzA
        have hcx : ⁅x, z⁆ = x ^ 2 := by
          calc
            ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by
              simp [commutatorElement_def, mul_assoc]
            _ = x * (z * x * z⁻¹)⁻¹ := by group
            _ = x * (x⁻¹)⁻¹ := by rw [hx.2]
            _ = x ^ 2 := by simp [pow_two]
        rwa [hcx] at hc
      have hxOrderDvd : orderOf x ∣ Nat.card P := by
        simpa using orderOf_dvd_natCard (⟨x, hx.1⟩ : P)
      have hxOrderOdd : Odd (orderOf x) := hPodd.of_dvd_nat hxOrderDvd
      have hcop : Nat.Coprime 2 (orderOf x) := by
        simpa using hxOrderOdd.coprime_two_left
      obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hcop
      rw [← hn]
      exact (⁅W, A⁆).pow_mem hx2 n
  have hWsubp : IsPGroup p (W.subgroupOf P) := hPp.to_subgroup _
  have hWmap : (W.subgroupOf P).map P.subtype = W := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWP]
  have hWp : IsPGroup p W := by
    rw [← hWmap]
    exact hWsubp.map P.subtype
  have hInvCard : theorem4bInvertedCard z W = theorem4bInvertedCard z P := by
    let e : {x : X // x ∈ W ∧ z * x * z⁻¹ = x⁻¹} ≃
        {x : X // x ∈ P ∧ z * x * z⁻¹ = x⁻¹} :=
      { toFun := fun x => ⟨x, hWP x.property.1, x.property.2⟩
        invFun := fun x =>
          ⟨x, Subgroup.subset_closure (show (x : X) ∈ I from x.property),
            x.property.2⟩
        left_inv := fun x => by apply Subtype.ext; rfl
        right_inv := fun x => by apply Subtype.ext; rfl }
    simpa [theorem4bInvertedCard] using Nat.card_congr e
  have hWne : W ≠ ⊥ := by
    intro hWbot
    have htwoW : 2 ≤ theorem4bInvertedCard z W := by
      rw [hInvCard]
      exact htwo
    have hcardOne : theorem4bInvertedCard z W = 1 := by
      rw [theorem4bInvertedCard, hWbot]
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨1, by simp⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.property.1
    omega
  have hWM : W ≤ M := hWP.trans (hPD.trans inf_le_left)
  have hWbeta : W ≤ MulAction.stabilizer X beta :=
    hWP.trans (hPD.trans inf_le_right)
  have hbase := theorem4b_baseCoset_mem_fixedPoints hWM
  have hbetaFixed : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) W := by
    intro w hw
    exact MulAction.mem_stabilizer_iff.mp (hWbeta hw)
  let base : theorem4bFixedPoints M W := ⟨QuotientGroup.mk 1, hbase⟩
  let other : theorem4bFixedPoints M W := ⟨beta, hbetaFixed⟩
  let f : Bool → theorem4bFixedPoints M W :=
    fun b => if b then other else base
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · have hab' : other = base := by simpa [f] using hab.symm
      exact (hbeta (by
        simpa [other, base] using congrArg Subtype.val hab')).elim
    · have hab' : other = base := by simpa [f] using hab
      exact (hbeta (by
        simpa [other, base] using congrArg Subtype.val hab')).elim
    · rfl
  have hfixed : 2 ≤ Nat.card (theorem4bFixedPoints M W) := by
    simpa using Nat.card_le_card_of_injective f hf
  let e : Theorem4bSixA M :=
    ⟨p, hp, hpOdd, z, W, hz, hzM, hWp, hWM, hzNormW,
      by simpa [A] using hcomm, hWne, hfixed⟩
  refine ⟨e, ?_⟩
  simpa [e, Theorem4bSixA.invertedSet, theorem4bInvertedCard] using hInvCard

/-- Proposition 3.8(b), applied to a second fixed point, gives the upper bound
in `(6B)`. -/
public theorem Theorem4bSixA.card_inverted_le_primeShare
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixA M) :
    Nat.card {x : X // x ∈ d.invertedSet} ≤
      theorem4bPrimeShare M d.z d.p := by
  obtain ⟨beta, hbeta, hbetaNe⟩ := d.exists_nonbase_fixedPoint
  have hWbeta : d.W ≤ MulAction.stabilizer X beta := by
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hbeta w hw)
  have hbound := hM.theorem4b_invertedCard_le_primeShare_of_stabilizer
    d.hzM d.hz d.hp hbetaNe d.hWp (le_inf d.hWM hWbeta) d.hzNorm
  simpa [Theorem4bSixA.invertedSet, theorem4bInvertedCard] using hbound

/-- The maximal choice `(6D)`, retaining the complete `(6A--6C)` witness. -/
public structure Theorem4bSixD
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) where
  data : Theorem4bSixA M
  maximal : ∀ e : Theorem4bSixA M,
    Nat.card {x : X // x ∈ e.invertedSet} ≤
      Nat.card {x : X // x ∈ data.invertedSet}

/-- The maximal `(6D)` witness inherits the Proposition 3.8(b) upper bound. -/
public theorem Theorem4bSixD.card_inverted_le_primeShare
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M) :
    Nat.card {x : X // x ∈ d.data.invertedSet} ≤
      theorem4bPrimeShare M d.data.z d.data.p :=
  d.data.card_inverted_le_primeShare hM

/-- Lemma 6.2, with `Omega_K` represented by `kFixedPoints`: `z` normalizes a
Sylow `p`-subgroup of the two-point stabilizer exactly when `|K| = m_p`. -/
public theorem Theorem4bSixD.lemma62
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M) {gamma : conjugateCosetSpace M}
    (hgamma : gamma ∈ d.data.kFixedPoints)
    (hgammaNe : gamma ≠ QuotientGroup.mk 1) :
    (∃ Q : Subgroup X,
        theorem4bIsSylowSubgroupOf d.data.p Q
          (M ⊓ MulAction.stabilizer X gamma) ∧
        d.data.z ∈ Subgroup.normalizer (Q : Set X)) ↔
      Nat.card {x : X // x ∈ d.data.invertedSet} =
        theorem4bPrimeShare M d.data.z d.data.p := by
  have hWgamma : d.data.W ≤ MulAction.stabilizer X gamma := by
    have hfix := d.data.kFixedPoints_subset_fixedPoints hgamma
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hfix w hw)
  have hWD : d.data.W ≤ M ⊓ MulAction.stabilizer X gamma :=
    le_inf d.data.hWM hWgamma
  have h38c := hM.theorem4b_proposition38cAtBase
    d.data.z d.data.p gamma d.data.hz d.data.hzM d.data.hp hgammaNe
  constructor
  · intro hSylow
    rcases h38c.mp hSylow with ⟨P, hPp, hPD, hzNormP, hPinv⟩
    have hupper := d.card_inverted_le_primeShare hM
    have htwoPrime : 2 ≤ theorem4bPrimeShare M d.data.z d.data.p :=
      d.data.two_le_card_invertedSet.trans hupper
    have htwoP : 2 ≤ theorem4bInvertedCard d.data.z P := by
      rw [hPinv]
      exact htwoPrime
    obtain ⟨e, hecard⟩ := exists_theorem4bSixA_of_normalized_pSubgroup
      d.data.hz d.data.hzM d.data.hp d.data.hpOdd hPp hPD hgammaNe
        hzNormP htwoP
    have hlower : theorem4bPrimeShare M d.data.z d.data.p ≤
        Nat.card {x : X // x ∈ d.data.invertedSet} := by
      calc
        theorem4bPrimeShare M d.data.z d.data.p =
            theorem4bInvertedCard d.data.z P := hPinv.symm
        _ = Nat.card {x : X // x ∈ e.invertedSet} := hecard.symm
        _ ≤ Nat.card {x : X // x ∈ d.data.invertedSet} := d.maximal e
    exact Nat.le_antisymm hupper hlower
  · intro hcard
    apply h38c.mpr
    refine ⟨d.data.W, d.data.hWp, hWD, d.data.hzNorm, ?_⟩
    simpa [Theorem4bSixA.invertedSet, theorem4bInvertedCard] using hcard

/-! ## Proposition 6.3: residual and rank setup -/

/-- The source subgroup `Y = O²(M°)`: Hall's `2`-residual of the involution
core, mapped back into the base stabilizer. -/
public def theorem4bProposition63Residual
    {X : Type u} [Group X] (M : Subgroup X) : Subgroup M :=
  (External.hallPResidual 2 (involutionCore M)).map
    (involutionCore M).subtype

/-- The subgroup `Y = O²(M°)` is normal in `M`.  This uses characteristicity
of Hall's residual and normality of the involution core, rather than any
containment asserted later in Proposition 6.3. -/
public instance theorem4bProposition63Residual_normal
    {X : Type u} [Group X] (M : Subgroup X) :
    (theorem4bProposition63Residual M).Normal := by
  dsimp [theorem4bProposition63Residual]
  exact ConjAct.normal_of_characteristic_of_normal

/-- Transfer the source rank witness `m₂(M°) ≥ 2` into `M ∩ L`, once the
already-generated involution core is known to lie in `L`. -/
public theorem theorem4bProposition63_twoRank_comap
    {X : Type u} [Group X] {M L : Subgroup X}
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hcoreL : (involutionCore M).map M.subtype ≤ L) :
    TwoRankAtLeastTwo (M.comap L.subtype) := by
  let f : involutionCore M →* M.comap L.subtype :=
    { toFun := fun x =>
        ⟨⟨(x : M), hcoreL (Subgroup.mem_map_of_mem M.subtype x.property)⟩,
          (x : M).property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply hrank.map_of_injective f
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : M.comap L.subtype => ((q : L) : X)) hxy

/-- The canonical map from `M°` into `L / O_{2'}(L)`, defined once the
embedded copy of `M°` is known to lie in `L`. -/
public noncomputable def theorem4bProposition63CoreQuotientMap
    {X : Type u} [Group X] {M L : Subgroup X}
    (hcoreL : (involutionCore M).map M.subtype ≤ L) :
    involutionCore M →* L ⧸ twoPrimeCore L :=
  (QuotientGroup.mk' (twoPrimeCore L)).comp
    { toFun := fun x =>
        ⟨((x : M) : X), hcoreL
          (Subgroup.mem_map_of_mem M.subtype x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- Evaluation of the canonical involution-core quotient map. -/
@[simp] public theorem theorem4bProposition63CoreQuotientMap_apply
    {X : Type u} [Group X] {M L : Subgroup X}
    (hcoreL : (involutionCore M).map M.subtype ≤ L)
    (x : involutionCore M) :
    theorem4bProposition63CoreQuotientMap hcoreL x =
      QuotientGroup.mk' (twoPrimeCore L)
        ⟨((x : M) : X), hcoreL
          (Subgroup.mem_map_of_mem M.subtype x.property)⟩ := by
  rfl

/-- Checked quotient glue for `[II4; 3.2(b)]`: if the image of `M°` modulo
`O_{2'}(L)` is a `2`-group, then `Y = O²(M°)` lies in `O_{2'}(L)`. -/
public theorem theorem4bProposition63Residual_map_le_twoPrimeCore_of_image_isPGroup
    {X : Type u} [Group X] {M L : Subgroup X}
    (hcoreL : (involutionCore M).map M.subtype ≤ L)
    (himage : IsPGroup 2
      (theorem4bProposition63CoreQuotientMap hcoreL).range) :
    (theorem4bProposition63Residual M).map M.subtype ≤
      (twoPrimeCore L).map L.subtype := by
  let f := theorem4bProposition63CoreQuotientMap hcoreL
  let fr : involutionCore M →* f.range := f.rangeRestrict
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hresKer : External.hallPResidual 2 (involutionCore M) ≤ fr.ker :=
    External.hallPResidual_le_ker_of_isPGroup fr himage
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨ym, hymY, rfl⟩
  rcases Subgroup.mem_map.mp hymY with ⟨r, hrRes, hrym⟩
  have hrKer : r ∈ fr.ker := hresKer hrRes
  have hfrOne : fr r = 1 := hrKer
  have hfOne : f r = 1 := congrArg Subtype.val hfrOne
  let rL : L :=
    ⟨((r : M) : X), hcoreL
      (Subgroup.mem_map_of_mem M.subtype r.property)⟩
  have hrLO : rL ∈ twoPrimeCore L :=
    (QuotientGroup.eq_one_iff (N := twoPrimeCore L) rL).mp
      (by simpa [f, theorem4bProposition63CoreQuotientMap, rL] using hfOne)
  refine Subgroup.mem_map.mpr ⟨rL, hrLO, ?_⟩
  exact congrArg Subtype.val hrym

/-- Full source-facing interface of Theorem 2 for an odd prime.  The first
clause is its exact-two-fixed-points branch.  The second records both
normalizer transitivity and the normalizing involution through every fixed
point for a maximal subgroup fixing at least three points. -/
@[expose] public def Theorem4bProposition63Theorem2
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (Z : Set X) : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    (((∃ P : Subgroup X,
        IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2) →
        MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2) ∧
      ((¬ ∃ P : Subgroup X,
          IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2) →
        ∀ (beta : conjugateCosetSpace M) (P : Subgroup X),
          IsPGroup p P →
          P ≤ MulAction.stabilizer X beta →
          3 ≤ Nat.card (theorem4bFixedPoints M P) →
          (∀ Q : Subgroup X,
            IsPGroup p Q →
            Q ≤ MulAction.stabilizer X beta →
            3 ≤ Nat.card (theorem4bFixedPoints M Q) →
            P ≤ Q → Q = P) →
          (∀ ⦃gamma delta : conjugateCosetSpace M⦄,
            gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
            delta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
            ∃ n : Subgroup.normalizer (P : Set X),
              (n : X) • gamma = delta) ∧
          ∀ gamma : conjugateCosetSpace M,
            gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
            ∃ s : X, s ∈ Z ∧ IsInvolution s ∧
              s ∈ Subgroup.normalizer (P : Set X) ∧ s • gamma = gamma))

/-- Corollary 5.7 in the exact form needed for `(6B)`: in the
non-two-transitive branch, every prime admits a maximal `p`-subgroup fixing at
least three points, normalized by an involution in the base stabilizer and
Sylow in a suitable two-point stabilizer.  Proposition 3.8(b) then gives the
literal `m_p` equality.

The proof uses only the already formalized Theorem 2 interface.  In
particular, neither the Sylow property nor the `m_p` equality is assumed.
-/
public theorem theorem4bCorollary57_exists_normalized_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    {p : ℕ} (hp : Nat.Prime p) :
    ∃ (s : X) (beta : conjugateCosetSpace M) (Q : Subgroup X),
      s ∈ M ∧ IsInvolution s ∧
      IsPGroup p Q ∧
      Q ≤ M ⊓ MulAction.stabilizer X beta ∧
      beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
      theorem4bIsSylowSubgroupOf p Q
        (M ⊓ MulAction.stabilizer X beta) ∧
      s ∈ Subgroup.normalizer (Q : Set X) ∧
      theorem4bInvertedCard s Q = theorem4bPrimeShare M s p ∧
      3 ≤ Nat.card (theorem4bFixedPoints M Q) := by
  classical
  obtain ⟨t, ht, htM⟩ := hM.exists_involution_not_mem
  let beta0 : conjugateCosetSpace M := QuotientGroup.mk t
  have hbeta0Ne : beta0 ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    intro h
    apply htM
    simpa [beta0, ht.inv_eq_self] using QuotientGroup.eq.mp h
  let P : Subgroup X := ⊥
  have hPp : IsPGroup p P := by
    simpa [P] using (IsPGroup.of_bot (p := p) (G := X))
  have hPM : P ≤ M := by simp [P]
  have hPbase :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    theorem4b_baseCoset_mem_fixedPoints hPM
  have hPbeta : beta0 ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    simp [P, fixedPointsOfSubgroup]
  let base : theorem4bFixedPoints M P :=
    ⟨QuotientGroup.mk 1, hPbase⟩
  let other : theorem4bFixedPoints M P := ⟨beta0, hPbeta⟩
  let f : Bool → theorem4bFixedPoints M P :=
    fun b => if b then other else base
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · have hab' : other = base := by simpa [f] using hab.symm
      exact (hbeta0Ne (by
        simpa [other, base] using congrArg Subtype.val hab')).elim
    · have hab' : other = base := by simpa [f] using hab
      exact (hbeta0Ne (by
        simpa [other, base] using congrArg Subtype.val hab')).elim
    · rfl
  have hPfixed : 2 ≤ Nat.card (theorem4bFixedPoints M P) := by
    simpa using Nat.card_le_card_of_injective f hf
  let Good : Subgroup X → Prop := fun R =>
    IsPGroup p R ∧ R ≤ M ∧ 2 ≤ Nat.card (theorem4bFixedPoints M R)
  have hPgood : Good P := ⟨hPp, hPM, hPfixed⟩
  obtain ⟨R, _hPR, hRmax⟩ := Finite.exists_le_maximal hPgood
  have hRgood : Good R := hRmax.1
  have hnoTwo : ¬ ∃ Q : Subgroup X,
      IsPGroup p Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2 := by
    intro hexact
    exact hnot2 ((hT2 p hp).1 hexact)
  have hRneTwo : Nat.card (theorem4bFixedPoints M R) ≠ 2 := by
    intro hcard
    exact hnoTwo ⟨R, hRgood.1, hcard⟩
  have hRthree : 3 ≤ Nat.card (theorem4bFixedPoints M R) := by
    omega
  have hRbase : R ≤ MulAction.stabilizer X
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    simpa [baseCoset_stabilizer] using hRgood.2.1
  have hRmaxThree : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) →
      R ≤ Q → Q = R := by
    intro Q hQp hQbase hQthree hRQ
    have hQM : Q ≤ M := by
      simpa [baseCoset_stabilizer] using hQbase
    have hQgood : Good Q := ⟨hQp, hQM, by omega⟩
    exact (hRmax.eq_of_le hQgood hRQ).symm
  have hsource := (hT2 p hp).2 hnoTwo
    (QuotientGroup.mk 1 : conjugateCosetSpace M) R
    hRgood.1 hRbase hRthree hRmaxThree
  have hRbaseFixed :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) R :=
    theorem4b_baseCoset_mem_fixedPoints hRgood.2.1
  obtain ⟨s, _hsZ, hsInv, hsNormR, hsFix⟩ :=
    hsource.2 _ hRbaseFixed
  have hsM : s ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hsFix
  let rbase : theorem4bFixedPoints M R :=
    ⟨QuotientGroup.mk 1, hRbaseFixed⟩
  have hexistsOther : ∃ x : theorem4bFixedPoints M R, x ≠ rbase := by
    by_contra h
    push Not at h
    have hcardOne : Nat.card (theorem4bFixedPoints M R) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨rbase, fun x => h x⟩
    omega
  obtain ⟨otherR, hotherR⟩ := hexistsOther
  let beta : conjugateCosetSpace M := otherR
  have hbetaFixed : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) R :=
    otherR.property
  have hbetaNe : beta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    intro h
    apply hotherR
    apply Subtype.ext
    exact h
  have hRbeta : R ≤ MulAction.stabilizer X beta := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mpr (hbetaFixed r hr)
  let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
  have hRD : R ≤ D := le_inf hRgood.2.1 hRbeta
  have hRDp : IsPGroup p (R.subgroupOf D) := by
    exact hRgood.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRD).symm
  obtain ⟨Qd, hRQd⟩ := hRDp.exists_le_sylow
  let Q : Subgroup X := (Qd : Subgroup D).map D.subtype
  have hRQ : R ≤ Q := by
    intro r hr
    apply Subgroup.mem_map.mpr
    refine ⟨⟨r, hRD hr⟩, hRQd ?_, rfl⟩
    exact hr
  have hQD : Q ≤ D := by
    simpa [Q] using Subgroup.map_le_range D.subtype (Qd : Subgroup D)
  have hQp : IsPGroup p Q := Qd.isPGroup'.map D.subtype
  have hQbaseFixed :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) Q :=
    theorem4b_baseCoset_mem_fixedPoints (hQD.trans inf_le_left)
  have hQbetaFixed : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Q := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mp (hQD.trans inf_le_right hq)
  let qbase : theorem4bFixedPoints M Q :=
    ⟨QuotientGroup.mk 1, hQbaseFixed⟩
  let qother : theorem4bFixedPoints M Q := ⟨beta, hQbetaFixed⟩
  let qf : Bool → theorem4bFixedPoints M Q :=
    fun b => if b then qother else qbase
  have hqf : Function.Injective qf := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · have hab' : qother = qbase := by simpa [qf] using hab.symm
      exact (hbetaNe (by
        simpa [qother, qbase] using congrArg Subtype.val hab')).elim
    · have hab' : qother = qbase := by simpa [qf] using hab
      exact (hbetaNe (by
        simpa [qother, qbase] using congrArg Subtype.val hab')).elim
    · rfl
  have hQfixedTwo : 2 ≤ Nat.card (theorem4bFixedPoints M Q) := by
    simpa using Nat.card_le_card_of_injective qf hqf
  have hQneTwo : Nat.card (theorem4bFixedPoints M Q) ≠ 2 := by
    intro hcard
    exact hnoTwo ⟨Q, hQp, hcard⟩
  have hQthree : 3 ≤ Nat.card (theorem4bFixedPoints M Q) := by
    omega
  have hQgood : Good Q :=
    ⟨hQp, hQD.trans inf_le_left, hQfixedTwo⟩
  have hQR : Q = R := (hRmax.eq_of_le hQgood hRQ).symm
  have hRsyl : theorem4bIsSylowSubgroupOf p R D := by
    refine ⟨Qd, ?_⟩
    exact hQR ▸ rfl
  have hRinv := (hM.theorem4b_proposition38bAtBase
    s p beta R hsInv hsM hp hRgood.1 hRgood.2.1 hRbeta
      hbetaNe hsNormR).2 hRsyl
  exact ⟨s, beta, R, hsM, hsInv, hRgood.1, by simpa [D] using hRD,
    hbetaNe, by simpa [D] using hRsyl, hsNormR, hRinv, hRthree⟩

/-! ## The source equality branch of `(6B)` -/

/-- Corollary 5.7, transported to the fixed base involution.  The source
first obtains an involution `s` in the base stabilizer, then conjugates `s`
to the selected `z` inside `M`; the inverted-cardinality transport and the
fixed-point stabilizer transport are checked below.  The saturation helper
constructs the final `(6A)` package, so no field of `Theorem4bSixD` is
strengthened with the equality.
-/
public theorem exists_theorem4bSixA_card_eq_primeShare_of_not_twoTransitive
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    {z : X} (hz : IsInvolution z) (hzM : z ∈ M)
    {p : ℕ} (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (htwo : 2 ≤ theorem4bPrimeShare M z p) :
    ∃ e : Theorem4bSixA M,
      Nat.card {x : X // x ∈ e.invertedSet} =
        theorem4bPrimeShare M z p := by
  obtain ⟨s, beta, R, hsM, hsInv, hRp, hRD, hbetaNe, _hRsyl,
      hsNormR, hInvS, _hRthree⟩ :=
    theorem4bCorollary57_exists_normalized_sylow hM hT2 hnot2 hp
  obtain ⟨t, ht, htM⟩ := hM.exists_involution_not_mem
  have hsIdx := hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
    hsM hsInv ht htM
  have hzIdx := hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
    hzM hz ht htM
  have hmEq : theorem4bM M s = theorem4bM M z :=
    hsIdx.symm.trans hzIdx
  have hshare : theorem4bPrimeShare M s p =
      theorem4bPrimeShare M z p := by
    simp [theorem4bPrimeShare, hmEq]
  have htwoS : 2 ≤ theorem4bInvertedCard s R := by
    rw [hInvS, hshare]
    exact htwo
  obtain ⟨g, hgM, hsg⟩ := hM.involutions_conjugate_in hsM hsInv hzM hz
  let P : Subgroup X := R.conjBy g⁻¹
  let beta' : conjugateCosetSpace M := g⁻¹ • beta
  have hPp : IsPGroup p P := by
    exact hRp.map (MulAut.conj g⁻¹).toMonoidHom
  have hPM : P ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨r, hr, rfl⟩
    simpa [P, Subgroup.conjBy, MulAut.conj_apply] using
      M.mul_mem (M.mul_mem (M.inv_mem hgM) (hRD hr).1) hgM
  have hPbeta : P ≤ MulAction.stabilizer X beta' := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨r, hr, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hrFix : r • beta = beta :=
      MulAction.mem_stabilizer_iff.mp (hRD hr).2
    change (g⁻¹ * r * (g⁻¹)⁻¹) • (g⁻¹ • beta) = g⁻¹ • beta
    calc
      (g⁻¹ * r * (g⁻¹)⁻¹) • (g⁻¹ • beta) =
          g⁻¹ • (r • (g • (g⁻¹ • beta))) := by
            simp only [inv_inv, mul_smul]
      _ = g⁻¹ • (r • beta) := by rw [smul_inv_smul]
      _ = g⁻¹ • beta := by rw [hrFix]
  have hbeta'Ne : beta' ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    intro h
    have hgBase : g • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact hgM
    have h' := congrArg (fun q : conjugateCosetSpace M => g • q) h
    apply hbetaNe
    simpa [beta', hgBase] using h'
  have hzNormP : z ∈ Subgroup.normalizer (P : Set X) := by
    have hconjNorm : (Subgroup.zpowers s).conjBy g⁻¹ ≤
        Subgroup.normalizer (P : Set X) := by
      simpa [P] using
        section11_conjBy_le_normalizer_conjBy_of_le_normalizer
          (Subgroup.zpowers_le.mpr hsNormR) g⁻¹
    apply hconjNorm
    apply Subgroup.mem_map.mpr
    refine ⟨s, Subgroup.mem_zpowers s, ?_⟩
    simpa [Subgroup.conjBy, MulAut.conj_apply, rightConjugateElem] using hsg
  have hInvConj : theorem4bInvertedCard z P =
      theorem4bInvertedCard s R := by
    have hcard := theorem4bInvertedCard_conjBy s g R
    simpa [P, hsg] using hcard
  have htwoP : 2 ≤ theorem4bInvertedCard z P := by
    rw [hInvConj]
    exact htwoS
  obtain ⟨e, he⟩ := exists_theorem4bSixA_of_normalized_pSubgroup
    hz hzM hp hpOdd hPp (le_inf hPM hPbeta) hbeta'Ne hzNormP htwoP
  refine ⟨e, ?_⟩
  calc
    Nat.card {x : X // x ∈ e.invertedSet} =
        theorem4bInvertedCard z P := he
    _ = theorem4bInvertedCard s R := hInvConj
    _ = theorem4bPrimeShare M s p := hInvS
    _ = theorem4bPrimeShare M z p := hshare

/-- The maximal `(6D)` witness satisfies the equality half of `(6B)` in the
non-two-transitive branch.  This is derived from the Corollary 5.7 endpoint
above and `(6D)` maximality; it is not an additional field or theorem
assumption on `Theorem4bSixD`.
-/
public theorem Theorem4bSixD.card_eq_primeShare_of_not_twoTransitive
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Theorem4bSixD M) :
    Nat.card {x : X // x ∈ d.data.invertedSet} =
      theorem4bPrimeShare M d.data.z d.data.p := by
  have hupper :
      Nat.card {x : X // x ∈ d.data.invertedSet} ≤
        theorem4bPrimeShare M d.data.z d.data.p :=
    d.card_inverted_le_primeShare hM
  have hexists :=
    exists_theorem4bSixA_card_eq_primeShare_of_not_twoTransitive
      hM hT2 hnot2 d.data.hz d.data.hzM d.data.hp
        d.data.hpOdd (d.data.two_le_card_invertedSet.trans hupper)
  let e : Theorem4bSixA M := Classical.choose hexists
  have hecard : Nat.card {x : X // x ∈ e.invertedSet} =
      theorem4bPrimeShare M d.data.z d.data.p :=
    Classical.choose_spec hexists
  have hle :
      Nat.card {x : X // x ∈ e.invertedSet} ≤
        Nat.card {x : X // x ∈ d.data.invertedSet} :=
    d.maximal e
  have hlower :
      theorem4bPrimeShare M d.data.z d.data.p ≤
        Nat.card {x : X // x ∈ d.data.invertedSet} := by
    exact hecard.symm.trans_le hle
  exact Nat.le_antisymm hupper hlower

/-- Lemma 3.10 gives `M° ≤ L`: every involution generator of the base
stabilizer lies in the Proposition 6.3 subgroup. -/
public theorem IsStronglyEmbedded.theorem4bProposition63_involutionCore_le
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    (involutionCore M).map M.subtype ≤
      theorem4bProposition63Subgroup M z t := by
  let L : Subgroup X := theorem4bProposition63Subgroup M z t
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyCore, rfl⟩
  change (y : X) ∈ L
  rw [involutionCore_eq_closure] at hyCore
  refine Subgroup.closure_induction
    (p := fun y : M => fun _hy => (y : X) ∈ L) ?_ ?_ ?_ ?_ hyCore
  · intro y hy
    exact hM.involution_mem_theorem4bProposition63Subgroup
      hzM hz ht htM y.property
        (IsInvolution.map_of_injective hy M.subtype Subtype.val_injective)
  · exact L.one_mem
  · intro a b _ha _hb ha hb
    exact L.mul_mem ha hb
  · intro a _ha ha
    exact L.inv_mem ha

/-- Proposition 4.4 in the already-strongly-embedded setting: restriction to
the subgroup `L` remains strongly embedded because `z ∈ M ∩ L` while
`t ∈ L \ M`. -/
public theorem IsStronglyEmbedded.theorem4bProposition63_comap
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (_ht : IsInvolution t) (htM : t ∉ M) :
    IsStronglyEmbedded
      (M.comap (theorem4bProposition63Subgroup M z t).subtype) := by
  let L : Subgroup X := theorem4bProposition63Subgroup M z t
  have hzL : z ∈ L :=
    by
      change z ∈ theorem4bProposition63Subgroup M z t
      exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have htL : t ∈ L :=
    by
      change t ∈ theorem4bProposition63Subgroup M z t
      exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  let zL : L := ⟨z, hzL⟩
  have hzLInv : IsInvolution zL := IsInvolution.subtype hz hzL
  have hzML : zL ∈ M.comap L.subtype := hzM
  have hproper : M.comap L.subtype ≠ ⊤ := by
    intro htop
    let tL : L := ⟨t, htL⟩
    have htTop : tL ∈ (⊤ : Subgroup L) := Subgroup.mem_top tL
    rw [← htop] at htTop
    exact htM htTop
  exact hM.comap_of_injective L.subtype Subtype.val_injective
    hproper ⟨zL, hzML, hzLInv⟩

/-- Lemma 3.13 plus normality: `O_{2'}(L)` lies in both `M` and `M^t`,
hence in the two-point stabilizer `D`. -/
public theorem IsStronglyEmbedded.theorem4bProposition63_twoPrimeCore_le_D
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    let L := theorem4bProposition63Subgroup M z t
    (twoPrimeCore L).map L.subtype ≤ M ⊓ rightConjugate M t := by
  let L : Subgroup X := theorem4bProposition63Subgroup M z t
  let O : Subgroup X := (twoPrimeCore L).map L.subtype
  have hcoreL : (involutionCore M).map M.subtype ≤ L :=
    hM.theorem4bProposition63_involutionCore_le hzM hz ht htM
  have hrankML : TwoRankAtLeastTwo (M.comap L.subtype) :=
    theorem4bProposition63_twoRank_comap hrank hcoreL
  have hOM : O ≤ M := by
    exact oddCore_map_le_stronglyEmbedded_of_twoRank_intersection
      M L hM hrankML
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hOsub : O.subgroupOf L = twoPrimeCore L := by
    change O.comap L.subtype = twoPrimeCore L
    dsimp [O]
    exact Subgroup.comap_map_eq_self_of_injective
      Subtype.val_injective (twoPrimeCore L)
  have hOnormalL : (O.subgroupOf L).Normal := by
    rw [hOsub]
    infer_instance
  have hLnormO : L ≤ Subgroup.normalizer O :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOL).mp hOnormalL
  have htL : t ∈ L :=
    by
      change t ∈ theorem4bProposition63Subgroup M z t
      exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have htNormO : t ∈ Subgroup.normalizer O := hLnormO htL
  refine le_inf hOM ?_
  intro x hxO
  have hxtO : rightConjugateElem x t ∈ O := by
    have hconj := (Subgroup.mem_normalizer_iff.mp htNormO x).1 hxO
    simpa [rightConjugateElem, ht.inv_eq_self] using hconj
  have hxtM : rightConjugateElem x t ∈ M := hOM hxtO
  have hmem := rightConjugateElem_mem_rightConjugate (g := t) hxtM
  simpa [rightConjugateElem_rightConjugateElem ht.inv_eq_self] using hmem

/-- Every odd-order element of `M` inverted by an involution of `M` lies in
`Y = O²(M°)`.  It is a product of two square-one elements of `M°`, then is one
of the canonical odd-order generators of Hall's residual. -/
public theorem mem_theorem4bProposition63Residual_of_odd_order_inverted
    {X : Type u} [Group X] {M : Subgroup X} {x s : X}
    (hxM : x ∈ M) (hxOdd : Odd (orderOf x))
    (hsM : s ∈ M) (hs : IsInvolution s)
    (hsx : s * x * s⁻¹ = x⁻¹) :
    (⟨x, hxM⟩ : M) ∈ theorem4bProposition63Residual M := by
  let xM : M := ⟨x, hxM⟩
  let sM : M := ⟨s, hsM⟩
  let sxM : M := sM * xM
  have hsMInv : IsInvolution sM := IsInvolution.subtype hs hsM
  have hsxSq : sxM ^ 2 = 1 := by
    apply Subtype.ext
    change (s * x) ^ 2 = 1
    rw [pow_two]
    calc
      s * x * (s * x) = (s * x * s⁻¹) * x := by rw [hs.inv_eq_self]; group
      _ = x⁻¹ * x := by rw [hsx]
      _ = 1 := by simp
  have sq_mem_core {a : M} (haSq : a ^ 2 = 1) : a ∈ involutionCore M := by
    by_cases haOne : a = 1
    · simpa [haOne] using (involutionCore M).one_mem
    · rw [involutionCore_eq_closure]
      exact Subgroup.subset_closure ⟨haOne, haSq⟩
  have hsCore : sM ∈ involutionCore M := by
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure hsMInv
  have hsxCore : sxM ∈ involutionCore M := sq_mem_core hsxSq
  have hxCore : xM ∈ involutionCore M := by
    have hprod : sM * sxM = xM := by
      apply Subtype.ext
      change s * (s * x) = x
      rw [← mul_assoc, show s * s = 1 by simpa [pow_two] using hs.sq_eq_one]
      simp
    rw [← hprod]
    exact (involutionCore M).mul_mem hsCore hsxCore
  let xc : involutionCore M := ⟨xM, hxCore⟩
  have hxcOdd : Odd (orderOf xc) := by
    simpa [xc, xM, Subgroup.orderOf_coe] using hxOdd
  have hxcResidual :
      xc ∈ External.hallPResidual 2 (involutionCore M) := by
    apply Subgroup.subset_closure
    exact hxcOdd.coprime_two_left
  exact Subgroup.mem_map.mpr ⟨xc, hxcResidual, rfl⟩

/-- The source inverted set `K = I_W(z)` is contained in `Y = O²(M°)`. -/
public theorem Theorem4bSixA.invertedSet_subset_theorem4bProposition63Residual
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    d.invertedSet ⊆
      ((theorem4bProposition63Residual M).map M.subtype : Set X) := by
  intro x hx
  letI : Fact d.p.Prime := ⟨d.hp⟩
  have hWodd : Odd (Nat.card d.W) := by
    obtain ⟨n, hn⟩ := d.hWp.exists_card_eq
    rw [hn]
    exact d.hpOdd.pow
  have hxOrderDvd : orderOf x ∣ Nat.card d.W := by
    simpa using orderOf_dvd_natCard (⟨x, hx.1⟩ : d.W)
  have hxOdd : Odd (orderOf x) := hWodd.of_dvd_nat hxOrderDvd
  have hxResidual :
      (⟨x, d.hWM hx.1⟩ : M) ∈ theorem4bProposition63Residual M :=
    mem_theorem4bProposition63Residual_of_odd_order_inverted
      (d.hWM hx.1) hxOdd d.hzM d.hz hx.2
  exact Subgroup.mem_map.mpr ⟨⟨x, d.hWM hx.1⟩, hxResidual, rfl⟩

/-- Since `K` generates the nontrivial subgroup `W`, the residual
`Y = O²(M°)` is nontrivial. -/
public theorem Theorem4bSixA.theorem4bProposition63Residual_ne_bot
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : theorem4bProposition63Residual M ≠ ⊥ := by
  intro hbot
  have hmapBot :
      (theorem4bProposition63Residual M).map M.subtype =
        (⊥ : Subgroup X) := by
    rw [hbot]
    simp
  have hclosureLe : Subgroup.closure d.invertedSet ≤
      (theorem4bProposition63Residual M).map M.subtype := by
    rw [Subgroup.closure_le]
    exact d.invertedSet_subset_theorem4bProposition63Residual
  have hWbot : d.W = ⊥ := by
    rw [← d.closure_invertedSet_eq]
    exact eq_bot_iff.mpr (by simpa [hmapBot] using hclosureLe)
  exact d.hWne hWbot

/-- The two-transitive branch of Proposition 6.3 is impossible.  Normality
of the nontrivial residual `Y` makes one additional fixed point propagate to
every point under the base stabilizer; simplicity then makes the action core
trivial, contradicting `Y ≠ 1`. -/
public theorem IsStronglyEmbedded.theorem4bProposition63_not_twoTransitive
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixA M) {t : X} (ht : IsInvolution t)
    (hbetaNe :
      (QuotientGroup.mk t : conjugateCosetSpace M) ≠ QuotientGroup.mk 1)
    (hYleD : (theorem4bProposition63Residual M).map M.subtype ≤
      M ⊓ rightConjugate M t) :
    ¬ MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  intro htwo
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  let Y : Subgroup M := theorem4bProposition63Residual M
  let YX : Subgroup X := Y.map M.subtype
  have hYX_M : YX ≤ M := Subgroup.map_subtype_le _
  have hYX_beta : YX ≤ MulAction.stabilizer X beta := by
    rw [show MulAction.stabilizer X beta = rightConjugate M t from by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    exact hYleD.trans inf_le_right
  have hYX_fixes : ∀ omega : conjugateCosetSpace M,
      YX ≤ MulAction.stabilizer X omega := by
    intro omega
    by_cases homega : omega = alpha
    · subst omega
      simpa [alpha, baseCoset_stabilizer] using hYX_M
    · have halphaBeta : alpha ≠ beta := by
        exact hbetaNe.symm
      have htwo' : ∀ {a b c d : conjugateCosetSpace M},
          a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d :=
        MulAction.is_two_pretransitive_iff.mp htwo
      obtain ⟨m, hmAlpha, hmBeta⟩ :=
        htwo' (a := alpha) (b := beta) (c := alpha) (d := omega)
          halphaBeta (fun h => homega h.symm)
      have hmM : m ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact MulAction.mem_stabilizer_iff.mpr hmAlpha
      intro y hyYX
      apply MulAction.mem_stabilizer_iff.mpr
      rcases Subgroup.mem_map.mp hyYX with ⟨yM, hyY, rfl⟩
      let mM : M := ⟨m, hmM⟩
      have hconjY : mM⁻¹ * yM * mM ∈ Y := by
        simpa using
          (inferInstance : Y.Normal).conj_mem yM hyY mM⁻¹
      have hconjFix : ((mM⁻¹ * yM * mM : M) : X) • beta = beta :=
        MulAction.mem_stabilizer_iff.mp
          (hYX_beta (Subgroup.mem_map_of_mem M.subtype hconjY))
      calc
        (yM : X) • omega = (yM : X) • (m • beta) := by rw [hmBeta]
        _ = m • (((mM⁻¹ * yM * mM : M) : X) • beta) := by
          simp [mM, mul_smul]
        _ = m • beta := by rw [hconjFix]
        _ = omega := hmBeta
  have hYXcore : YX ≤ pointStabilizerCore X (conjugateCosetSpace M) :=
    (le_pointStabilizerCore_iff).2 hYX_fixes
  let C : Subgroup X := pointStabilizerCore X (conjugateCosetSpace M)
  have hCnormal : C.Normal :=
    PFchapter1section1.proposition_4_c_pointStabilizerCore_normal
  rcases (haveI := hCnormal; hX.eq_bot_or_eq_top_of_normal C) with hCbot | hCtop
  · have hYXbot : YX = ⊥ :=
      eq_bot_iff.mpr (by simpa [C, hCbot] using hYXcore)
    have hYbot : Y = ⊥ := by
      apply Subgroup.map_injective (f := M.subtype) Subtype.val_injective
      simp [YX, hYXbot]
    exact d.theorem4bProposition63Residual_ne_bot hYbot
  · apply hM.1
    apply top_unique
    have hCleM : C ≤ M := by
      rw [show M = MulAction.stabilizer X alpha by
        simpa [alpha] using (baseCoset_stabilizer M).symm]
      exact (le_pointStabilizerCore_iff.mp le_rfl) alpha
    simpa [C, hCtop] using hCleM

/-! ## Proposition 6.3: the prime-by-prime branch -/

/-- An element of the normal `p`-core that normalizes a `q`-subgroup for a
different prime centralizes that subgroup. -/
public theorem mem_centralizer_of_mem_pCore_of_mem_normalizer
    {G : Type u} [Group G] [Finite G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {x : G} {R : Subgroup G}
    (hxCore : x ∈ pCore p G) (hRp : IsPGroup q R)
    (hxNorm : x ∈ Subgroup.normalizer (R : Set G)) :
    x ∈ Subgroup.centralizer (R : Set G) := by
  let A : Subgroup G := Subgroup.zpowers x
  have hAcore : A ≤ pCore p G := by
    exact Subgroup.zpowers_le.mpr hxCore
  have hcommCore : ⁅A, R⁆ ≤ pCore p G := by
    exact (Subgroup.commutator_mono hAcore le_rfl).trans
      (Subgroup.commutator_le_left (pCore p G) R)
  have hcommR : ⁅A, R⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha r hr
    have haNorm : a ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.zpowers_le.mpr hxNorm) ha
    have har : a * r * a⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp haNorm r).mp hr
    simpa [commutatorElement_def, mul_assoc] using
      R.mul_mem har (R.inv_mem hr)
  have hdisj : Disjoint (pCore p G) R :=
    IsPGroup.disjoint_of_ne p q hpq (pCore p G) R
      (pCore_isPGroup (p := p) (G := G)) hRp
  have hcommbot : ⁅A, R⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    intro c hc
    exact hdisj.le_bot ⟨hcommCore hc, hcommR hc⟩
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot)
    (Subgroup.mem_zpowers x)

/-- The image of an involution of `M` in `M / O²(M°)` belongs to the
normal `2`-core of the quotient. -/
public theorem theorem4bProposition63_involution_image_mem_twoCore
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} {z : X}
    (hzM : z ∈ M) (hz : IsInvolution z) :
    QuotientGroup.mk' (theorem4bProposition63Residual M) ⟨z, hzM⟩ ∈
      pCore 2 (M ⧸ theorem4bProposition63Residual M) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup M := involutionCore M
  let Y : Subgroup M := theorem4bProposition63Residual M
  let q : M →* M ⧸ Y := QuotientGroup.mk' Y
  let H : Subgroup K := External.hallPResidual 2 K
  let qK : K →* M ⧸ Y := q.comp K.subtype
  have hHker : H ≤ qK.ker := by
    intro x hxH
    apply (QuotientGroup.eq_one_iff (N := Y) (x : M)).mpr
    dsimp [Y, theorem4bProposition63Residual, H, K]
    exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  letI : H.Normal := External.hallPResidual_normal 2 K
  let f : (K ⧸ H) →* (M ⧸ Y) :=
    QuotientGroup.lift H qK hHker
  have hquot : IsPGroup 2 (K ⧸ H) :=
    External.hallPResidual_quotient_isPGroup 2
  have hfrangeP : IsPGroup 2 f.range :=
    hquot.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfrange : f.range = K.map q := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨a, rfl⟩
      refine QuotientGroup.induction_on a ?_
      intro x
      exact Subgroup.mem_map.mpr ⟨x, x.property, by simp [f, qK]⟩
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxK, rfl⟩
      refine ⟨QuotientGroup.mk' H ⟨x, hxK⟩, ?_⟩
      simp [f, qK]
  have hC : IsPGroup 2 (K.map q) := by
    rw [← hfrange]
    exact hfrangeP
  have hCnormal : (K.map q).Normal := by
    exact Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective Y)
  have hCcore : K.map q ≤ pCore 2 (M ⧸ Y) := by
    exact le_sSup ⟨hCnormal, hC⟩
  have hzK : (⟨z, hzM⟩ : M) ∈ K := by
    change (⟨z, hzM⟩ : M) ∈ involutionCore M
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure (IsInvolution.subtype hz hzM)
  have hmemC : q ⟨z, hzM⟩ ∈ K.map q := by
    exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, hzK, rfl⟩
  exact hCcore hmemC

/-- Quotient centralization modulo `Y = O²(M°)` lifts to normalization of
`P Y` for every subgroup `P` of a normalized odd-prime subgroup `R`. -/
public theorem theorem4bProposition63_normalizes_sup_residual
    {X : Type u} [Group X] [Finite X] {M P R : Subgroup X} {z : X}
    {q : ℕ} (hq : q.Prime) (hqOdd : Odd q)
    (hzM : z ∈ M) (hz : IsInvolution z)
    (hRp : IsPGroup q R) (hRM : R ≤ M) (hPR : P ≤ R)
    (hzNormR : z ∈ Subgroup.normalizer (R : Set X)) :
    z ∈ Subgroup.normalizer
      ((P ⊔ (theorem4bProposition63Residual M).map M.subtype :
        Subgroup X) : Set X) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup M := theorem4bProposition63Residual M
  let qM : M →* M ⧸ Y := QuotientGroup.mk' Y
  let RM : Subgroup M := R.subgroupOf M
  let PM : Subgroup M := P.subgroupOf M
  let Rbar : Subgroup (M ⧸ Y) := RM.map qM
  let Pbar : Subgroup (M ⧸ Y) := PM.map qM
  have hPM : P ≤ M := hPR.trans hRM
  have hRMp : IsPGroup q RM := by
    exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
  have hzMNormR : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer (RM : Set M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRM]
    exact hzNormR
  have hzbarNormR : qM ⟨z, hzM⟩ ∈
      Subgroup.normalizer (Rbar : Set (M ⧸ Y)) := by
    apply Subgroup.le_normalizer_map qM
    exact Subgroup.mem_map_of_mem qM hzMNormR
  have hzbarCore : qM ⟨z, hzM⟩ ∈ pCore 2 (M ⧸ Y) := by
    exact theorem4bProposition63_involution_image_mem_twoCore hzM hz
  have htwoNeQ : 2 ≠ q := by
    intro hqTwo
    subst q
    exact (by decide : ¬ Odd 2) hqOdd
  have hzbarCentralR : qM ⟨z, hzM⟩ ∈
      Subgroup.centralizer (Rbar : Set (M ⧸ Y)) := by
    apply mem_centralizer_of_mem_pCore_of_mem_normalizer htwoNeQ
      hzbarCore
    · exact hRMp.map qM
    · exact hzbarNormR
  have hPMRM : PM ≤ RM := Subgroup.subgroupOf_mono M hPR
  have hPbarRbar : Pbar ≤ Rbar := Subgroup.map_mono hPMRM
  have hzbarCentralP : qM ⟨z, hzM⟩ ∈
      Subgroup.centralizer (Pbar : Set (M ⧸ Y)) :=
    (Subgroup.centralizer_le hPbarRbar) hzbarCentralR
  have hzbarNormP : qM ⟨z, hzM⟩ ∈
      Subgroup.normalizer (Pbar : Set (M ⧸ Y)) :=
    centralizer_le_normalizer Pbar hzbarCentralP
  have hzMNormComap : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer ((Pbar.comap qM : Subgroup M) : Set M) := by
    have hzComap : (⟨z, hzM⟩ : M) ∈
        (Subgroup.normalizer (Pbar : Set (M ⧸ Y))).comap qM :=
      hzbarNormP
    rw [Subgroup.comap_normalizer_eq_of_surjective Pbar
      (QuotientGroup.mk'_surjective Y)] at hzComap
    exact hzComap
  have hcomap : Pbar.comap qM = PM ⊔ Y := by
    dsimp [Pbar]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hzMNormSup : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer ((PM ⊔ Y : Subgroup M) : Set M) := by
    rw [← hcomap]
    exact hzMNormComap
  have hzNormMap : z ∈ Subgroup.normalizer
      ((((PM ⊔ Y : Subgroup M).map M.subtype) : Subgroup X) : Set X) := by
    apply Subgroup.le_normalizer_map M.subtype
    exact Subgroup.mem_map_of_mem M.subtype hzMNormSup
  simpa [PM, Y, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPM] using hzNormMap

/-- Theorem 2 supplies a maximal `q`-subgroup fixing at least three points,
together with an involution fixing the base point and normalizing it. -/
public theorem theorem4bProposition63_exists_maximal_pSubgroup
    {X : Type u} [Group X] [Finite X]
    (M D : Subgroup X) (beta : conjugateCosetSpace M)
    (q : ℕ) (hq : q.Prime)
    (hDM : D ≤ M) (hDbeta : D ≤ MulAction.stabilizer X beta)
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    ∃ (P₀ : Sylow q (twoPrimeCore D)) (R : Subgroup X) (s : X),
      let P : Subgroup X :=
        (((P₀ : Subgroup (twoPrimeCore D)).map
          (twoPrimeCore D).subtype).map D.subtype)
      P ≤ R ∧ IsPGroup q R ∧ R ≤ M ∧
        s ∈ involutionsSet X ∧ IsInvolution s ∧
        s ∈ Subgroup.normalizer (R : Set X) ∧
        s • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1 := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let O : Subgroup D := twoPrimeCore D
  let P₀ : Sylow q O := default
  let PD : Subgroup D := (P₀ : Subgroup O).map O.subtype
  let P : Subgroup X := PD.map D.subtype
  have hPp : IsPGroup q P := by
    exact (P₀.2.map O.subtype).map D.subtype
  have hPD : P ≤ D := by
    exact Subgroup.map_subtype_le PD
  have hPM : P ≤ M := hPD.trans hDM
  have hPbeta : P ≤ MulAction.stabilizer X beta := hPD.trans hDbeta
  have hPbase :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    theorem4b_baseCoset_mem_fixedPoints hPM
  have hPbetaFixed :
      beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPbeta hxP)
  let base : theorem4bFixedPoints M P :=
    ⟨QuotientGroup.mk 1, hPbase⟩
  let other : theorem4bFixedPoints M P := ⟨beta, hPbetaFixed⟩
  let f : Bool → theorem4bFixedPoints M P := fun b => cond b other base
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      apply hbetaNe
      simpa [f, base, other] using (congrArg Subtype.val hab).symm
    · exfalso
      apply hbetaNe
      simpa [f, base, other] using congrArg Subtype.val hab
    · rfl
  have hPfixed : 2 ≤ Nat.card (theorem4bFixedPoints M P) := by
    simpa using Nat.card_le_card_of_injective f hf
  let Good : Subgroup X → Prop := fun Q =>
    IsPGroup q Q ∧ Q ≤ M ∧ 2 ≤ Nat.card (theorem4bFixedPoints M Q)
  have hPgood : Good P := ⟨hPp, hPM, hPfixed⟩
  obtain ⟨R, hPR, hRmax⟩ := Finite.exists_le_maximal hPgood
  have hRgood : Good R := hRmax.1
  have hnoTwo : ¬ ∃ Q : Subgroup X,
      IsPGroup q Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2 := by
    intro hexact
    exact hnot2 ((hT2 q hq).1 hexact)
  have hRneTwo : Nat.card (theorem4bFixedPoints M R) ≠ 2 := by
    intro hcard
    exact hnoTwo ⟨R, hRgood.1, hcard⟩
  have hRthree : 3 ≤ Nat.card (theorem4bFixedPoints M R) := by
    omega
  have hRbase : R ≤ MulAction.stabilizer X
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    simpa [baseCoset_stabilizer] using hRgood.2.1
  have hRmaxThree : ∀ Q : Subgroup X,
      IsPGroup q Q →
      Q ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) →
      R ≤ Q → Q = R := by
    intro Q hQp hQbase hQthree hRQ
    have hQM : Q ≤ M := by
      simpa [baseCoset_stabilizer] using hQbase
    have hQgood : Good Q := ⟨hQp, hQM, by omega⟩
    exact (hRmax.eq_of_le hQgood hRQ).symm
  have hsource := (hT2 q hq).2 hnoTwo
    (QuotientGroup.mk 1 : conjugateCosetSpace M) R
    hRgood.1 hRbase hRthree hRmaxThree
  have hRbaseFixed :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) R :=
    theorem4b_baseCoset_mem_fixedPoints hRgood.2.1
  obtain ⟨s, hsZ, hsInv, hsNorm, hsFix⟩ :=
    hsource.2 _ hRbaseFixed
  refine ⟨P₀, R, s, ?_⟩
  change P ≤ R ∧ IsPGroup q R ∧ R ≤ M ∧
    s ∈ involutionsSet X ∧ IsInvolution s ∧
    s ∈ Subgroup.normalizer (R : Set X) ∧
    s • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk 1
  exact ⟨hPR, hRgood.1, hRgood.2.1, hsZ, hsInv, hsNorm, hsFix⟩

/-- For each odd prime, the non-two-transitive branch produces a Sylow
subgroup of `O₂'(D)` whose product with `Y` is normalized by `z`. -/
public theorem IsStronglyEmbedded.theorem4bProposition63_exists_sylow_normalized
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (q : ℕ) (hq : q.Prime) (hqOdd : Odd q) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    ∃ P₀ : Sylow q (twoPrimeCore D),
      z ∈ Subgroup.normalizer
        (((((P₀ : Subgroup (twoPrimeCore D)).map
            (twoPrimeCore D).subtype).map D.subtype) ⊔
          (theorem4bProposition63Residual M).map M.subtype :
          Subgroup X) : Set X) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let D : Subgroup X := M ⊓ rightConjugate M t
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hDM : D ≤ M := inf_le_left
  have hDbeta : D ≤ MulAction.stabilizer X beta := by
    rw [show MulAction.stabilizer X beta = rightConjugate M t from by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    exact inf_le_right
  have hbetaNe : beta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    intro h
    apply htM
    simpa [beta, ht.inv_eq_self] using QuotientGroup.eq.mp h
  obtain ⟨P₀, R, s, hPR, hRp, hRM, _hsZ, hsInv, hsNorm, hsFix⟩ :=
    theorem4bProposition63_exists_maximal_pSubgroup
      M D beta q hq hDM hDbeta hbetaNe hT2 hnot2
  have hsM : s ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hsFix
  obtain ⟨d, hdD, hsd⟩ :=
    hM.involutions_conjugate_by_inf_rightConjugate
      ht htM hsM hsInv hzM hz
  let dD : D := ⟨d, hdD⟩
  let O : Subgroup D := twoPrimeCore D
  let φ : MulAut O := MulAut.conjNormal (H := O) dD⁻¹
  have hφsurj : Function.Surjective (φ : O →* O) := by
    exact φ.surjective
  let P₀' : Sylow q O :=
    P₀.mapSurjective (f := (φ : O →* O)) hφsurj
  let P : Subgroup X :=
    (((P₀ : Subgroup O).map O.subtype).map D.subtype)
  let P' : Subgroup X :=
    (((P₀' : Subgroup O).map O.subtype).map D.subtype)
  let R' : Subgroup X := R.conjBy d⁻¹
  have hPconj : P' = P.conjBy d⁻¹ := by
    have hhom :
        (D.subtype.comp O.subtype).comp (φ : O →* O) =
          ((MulAut.conj d⁻¹).toMonoidHom.comp D.subtype).comp
            O.subtype := by
      ext a
      simp [φ, dD]
    change
      (((P₀' : Subgroup O).map O.subtype).map D.subtype) =
        ((((P₀ : Subgroup O).map O.subtype).map D.subtype).conjBy d⁻¹)
    dsimp [P₀', Sylow.mapSurjective]
    rw [Subgroup.map_map, Subgroup.map_map]
    simpa only [Subgroup.conjBy, Subgroup.map_map, MonoidHom.comp_assoc] using
      congrArg (fun f : O →* X => (P₀ : Subgroup O).map f) hhom
  have hPR' : P' ≤ R' := by
    rw [hPconj]
    exact Subgroup.map_mono hPR
  have hRp' : IsPGroup q R' := by
    exact hRp.map (MulAut.conj d⁻¹).toMonoidHom
  have hRM' : R' ≤ M := by
    have hdInvNormM : d⁻¹ ∈ Subgroup.normalizer (M : Set X) :=
      Subgroup.le_normalizer (M.inv_mem hdD.1)
    have hMconj : M.conjBy d⁻¹ = M :=
      section11_conjBy_eq_of_mem_normalizer hdInvNormM
    change R.conjBy d⁻¹ ≤ M
    rw [← hMconj]
    exact Subgroup.map_mono hRM
  have hzNormR' : z ∈ Subgroup.normalizer (R' : Set X) := by
    have hsZpowNorm : Subgroup.zpowers s ≤
        Subgroup.normalizer (R : Set X) :=
      Subgroup.zpowers_le.mpr hsNorm
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        hsZpowNorm d⁻¹
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨s, Subgroup.mem_zpowers s, ?_⟩
    simpa [MulAut.conj_apply, rightConjugateElem] using hsd
  have hzNormSup := theorem4bProposition63_normalizes_sup_residual
    hq hqOdd hzM hz hRp' hRM' hPR' hzNormR'
  refine ⟨P₀', ?_⟩
  simpa [O, P'] using hzNormSup

/-- Choosing one Sylow subgroup for each prime divisor of a finite group's
order still generates the whole group. -/
public theorem iSup_selected_sylow_eq_top
    {G : Type u} [Group G] [Finite G]
    (P : ∀ p : (Nat.card G).primeFactors.attach, Sylow p.1 G) :
    (⨆ p, ((P p : Sylow p.1 G) : Subgroup G)) = ⊤ := by
  set S := ⨆ p, ((P p : Sylow p.1 G) : Subgroup G)
  rw [← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · by_cases hd : p ∈ (Nat.card G).primeFactors
    · let q : (Nat.card G).primeFactors.attach :=
        ⟨⟨p, hd⟩, Finset.mem_attach _ _⟩
      letI : Fact p.Prime := ⟨hp⟩
      let Q : Sylow p G := P q
      have hQle : (Q : Subgroup G) ≤ S := by
        exact le_iSup (fun r : (Nat.card G).primeFactors.attach =>
          ((P r : Sylow r.1 G) : Subgroup G)) q
      refine le_antisymm ?_ ?_
      · suffices (Nat.card S).factorization ≤
            (Nat.card G).factorization by
          exact String.Pos.Raw.mk_le_mk.mp (this p)
        rw [Nat.factorization_le_iff_dvd Nat.card_pos.ne'
          Nat.card_pos.ne']
        exact Subgroup.card_subgroup_dvd_card S
      rw [← pow_le_pow_iff_right₀ (Nat.Prime.one_lt hp),
        ← Sylow.card_eq_multiplicity Q]
      have hcard : Nat.card Q = Nat.card (Q.subgroupOf S) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).symm
      have hpQ : IsPGroup p (Q.subgroupOf S) := by
        refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_
        rw [← hcard, ← Sylow.card_eq_multiplicity Q]
      rcases IsPGroup.exists_le_sylow hpQ with ⟨Q', hQ'⟩
      rw [← Sylow.card_eq_multiplicity Q', hcard]
      exact Subgroup.card_le_of_le hQ'
    · have hnG : ¬ p ∣ Nat.card G := by
        have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
        rw [Nat.mem_primeFactors_of_ne_zero hGne] at hd
        simp_all only [true_and, not_false_eq_true]
      have hnS : ¬ p ∣ Nat.card S :=
        (flip dvd_trans (Subgroup.card_subgroup_dvd_card S)).mt hnG
      rw [Nat.factorization_eq_zero_of_not_dvd hnG,
        Nat.factorization_eq_zero_of_not_dvd hnS]
  · simp_all only [not_false_eq_true,
      Nat.factorization_eq_zero_of_not_prime]

/-- An odd subgroup extended by one normalizing involution has no four-group. -/
public theorem not_twoRankAtLeastTwo_sup_odd_involution
    {X : Type u} [Group X] [Finite X] (O : Subgroup X) {z : X}
    (hOodd : Odd (Nat.card O)) (hz : IsInvolution z)
    (hzNorm : z ∈ Subgroup.normalizer (O : Set X)) :
    ¬ TwoRankAtLeastTwo (O ⊔ Subgroup.zpowers z : Subgroup X) := by
  let Z : Subgroup X := Subgroup.zpowers z
  let H : Subgroup X := O ⊔ Z
  have hzOrder : orderOf z = 2 :=
    (orderOf_eq_prime_iff).2 ⟨hz.sq_eq_one, hz.ne_one⟩
  have hZcard : Nat.card Z = 2 := by
    simpa [Z] using (Nat.card_zpowers z).trans hzOrder
  have hZNormO : Z ≤ Subgroup.normalizer (O : Set X) := by
    exact Subgroup.zpowers_le.mpr hzNorm
  have hcop : Nat.Coprime (Nat.card O) (Nat.card Z) := by
    rw [hZcard]
    exact hOodd.coprime_two_left.symm
  have hinf : O ⊓ Z = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hHcard : Nat.card H = Nat.card O * 2 := by
    simpa [H, hZcard] using
      appendixC_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer
        hZNormO hinf
  intro hrank
  obtain ⟨E, hEcard, _hEsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrank
  have hfourDvd : 4 ∣ Nat.card H := by
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  rw [hHcard] at hfourDvd
  rcases hOodd with ⟨k, hk⟩
  rcases hfourDvd with ⟨m, hm⟩
  omega

/-- Since every inverted set is a finite subset of `X`, a witness maximizing
its cardinality exists. -/
public theorem exists_theorem4bSixD
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h : Nonempty (Theorem4bSixA M)) : Nonempty (Theorem4bSixD M) := by
  classical
  let score : Theorem4bSixA M → ℕ :=
    fun d => Nat.card {x : X // x ∈ d.invertedSet}
  let deficit : Theorem4bSixA M → ℕ := fun d => Nat.card X - score d
  let P : ℕ → Prop := fun n => ∃ d : Theorem4bSixA M, n = deficit d
  have hP : ∃ n, P n := by
    rcases h with ⟨d⟩
    exact ⟨deficit d, d, rfl⟩
  obtain ⟨d, hd⟩ := Nat.find_spec hP
  refine ⟨⟨d, ?_⟩⟩
  intro e
  have hmin : Nat.find hP ≤ deficit e :=
    Nat.find_min' hP ⟨e, rfl⟩
  have hscoreE : score e ≤ Nat.card X :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hscoreD : score d ≤ Nat.card X :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  change score e ≤ score d
  dsimp only [P] at hd
  rw [hd] at hmin
  dsimp only [deficit] at hmin
  omega

/-- The checked source setup `(6A--6D)` follows directly from the denial of
Theorem 4(b). -/
public theorem exists_theorem4bSixD_of_not_Theorem4bAtBase
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h : ¬ Theorem4bAtBase M) : Nonempty (Theorem4bSixD M) :=
  exists_theorem4bSixD (not_Theorem4bAtBase_iff_nonempty_sixA.mp h)

/-- Cardinality one of the fixed-point subtype is equivalent to the literal
source statement that `W` fixes a unique point. -/
public theorem theorem4b_fixedPoints_card_eq_one_iff_existsUnique
    {X : Type u} [Group X] [Finite X] {M W : Subgroup X} :
    Nat.card (theorem4bFixedPoints M W) = 1 ↔
      ∃! omega : conjugateCosetSpace M,
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) W := by
  constructor
  · intro hcard
    rcases Nat.card_eq_one_iff_exists.mp hcard with ⟨omega, homega⟩
    refine ⟨omega.1, omega.2, ?_⟩
    intro eta heta
    have hsub :
        (⟨eta, heta⟩ : theorem4bFixedPoints M W) = omega :=
      homega ⟨eta, heta⟩
    exact congrArg Subtype.val hsub
  · rintro ⟨omega, homega, hunique⟩
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨omega, homega⟩, ?_⟩
    intro eta
    apply Subtype.ext
    exact hunique eta.1 eta.2

/-- Checked application theorem, avoiding downstream dependence on the body of
the contract definition. -/
public theorem Theorem4bAtBase.centralizes_or_fixedPoints_card_eq_one
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W) :
    W ≤ Subgroup.centralizer ({z} : Set X) ∨
      Nat.card (theorem4bFixedPoints M W) = 1 := by
  exact h4b z W hz hzM hWodd hWM hzNorm

/-- Literal source-language form of the contract conclusion. -/
public theorem Theorem4bAtBase.centralizes_or_existsUnique_fixedPoint
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W) :
    W ≤ Subgroup.centralizer ({z} : Set X) ∨
      ∃! omega : conjugateCosetSpace M,
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) W := by
  rcases h4b.centralizes_or_fixedPoints_card_eq_one
      hz hzM hWodd hWM hzNorm with hcentral | hfixed
  · exact Or.inl hcentral
  · exact Or.inr
      (theorem4b_fixedPoints_card_eq_one_iff_existsUnique.mp hfixed)

/-- If the fixed-point set is not a singleton, Theorem 4(b) forces `z` to
centralize `W`. -/
public theorem Theorem4bAtBase.centralizes_of_fixedPoints_card_ne_one
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hcard : Nat.card (theorem4bFixedPoints M W) ≠ 1) :
    W ≤ Subgroup.centralizer ({z} : Set X) := by
  rcases h4b.centralizes_or_fixedPoints_card_eq_one
      hz hzM hWodd hWM hzNorm with hcentral | hfixed
  · exact hcentral
  · exact (hcard hfixed).elim

/-- The common `|Omega_W| > 1` use of Theorem 4(b). -/
public theorem Theorem4bAtBase.centralizes_of_two_le_fixedPoints_card
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hcard : 2 ≤ Nat.card (theorem4bFixedPoints M W)) :
    W ≤ Subgroup.centralizer ({z} : Set X) := by
  apply h4b.centralizes_of_fixedPoints_card_ne_one
    hz hzM hWodd hWM hzNorm
  omega

/-- The common `|Omega_W| ≥ 3` use of Theorem 4(b). -/
public theorem Theorem4bAtBase.centralizes_of_three_le_fixedPoints_card
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hcard : 3 ≤ Nat.card (theorem4bFixedPoints M W)) :
    W ≤ Subgroup.centralizer ({z} : Set X) := by
  apply h4b.centralizes_of_fixedPoints_card_ne_one
    hz hzM hWodd hWM hzNorm
  omega

/-- The contrapositive-facing eliminator: a noncentral action forces the
fixed-point set to have cardinality one. -/
public theorem Theorem4bAtBase.fixedPoints_card_eq_one_of_not_centralizes
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set X)) :
    Nat.card (theorem4bFixedPoints M W) = 1 := by
  exact (h4b.centralizes_or_fixedPoints_card_eq_one
    hz hzM hWodd hWM hzNorm).resolve_left hnot

/-- Literal unique-fixed-point form of the noncentral conclusion. -/
public theorem Theorem4bAtBase.existsUnique_fixedPoint_of_not_centralizes
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set X)) :
    ∃! omega : conjugateCosetSpace M,
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) W := by
  apply theorem4b_fixedPoints_card_eq_one_iff_existsUnique.mp
  exact h4b.fixedPoints_card_eq_one_of_not_centralizes
    hz hzM hWodd hWM hzNorm hnot

/-- Since `W ≤ M`, the unique fixed point in the noncentral case is exactly
the distinguished base coset. -/
public theorem Theorem4bAtBase.fixedPoint_eq_base_of_not_centralizes
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h4b : Theorem4bAtBase M) {z : X} {W : Subgroup X}
    (hz : IsInvolution z) (hzM : z ∈ M)
    (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer W)
    (hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set X))
    {omega : conjugateCosetSpace M}
    (homega : omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) W) :
    omega = QuotientGroup.mk 1 := by
  obtain ⟨eta, heta, hunique⟩ :=
    h4b.existsUnique_fixedPoint_of_not_centralizes
      hz hzM hWodd hWM hzNorm hnot
  have hbase := theorem4b_baseCoset_mem_fixedPoints hWM
  exact (hunique omega homega).trans (hunique _ hbase).symm

end CFSG.BenderSuzuki
