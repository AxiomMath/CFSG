module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition53
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Final

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 2 and Proposition 5.3

This module continues the source proof after Lemma 5.1.  It is placed above
Section 7 because the currently available generic invariant-Sylow theorem
[II1; 4.1] is exported from `SE.Section7Final`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

open PFAppendixIII PFchapter1section1

private theorem fixedPoints_card_even_of_fixedPoint_free_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega] {P : Subgroup G} {s : G}
    (hs : IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set G))
    (hfree : ∀ omega : Omega,
      omega ∈ fixedPointsOfSubgroup G Omega P → s • omega ≠ omega) :
    Even (Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P}) := by
  classical
  let C : Subgroup G := Subgroup.zpowers s
  have hCNorm : C ≤ Subgroup.normalizer (P : Set G) := by
    exact Subgroup.zpowers_le.mpr hsNorm
  let FixedP : SubMulAction C Omega :=
    { carrier := fixedPointsOfSubgroup G Omega P
      smul_mem' := fun c omega homega =>
        fixedPoints_smul_of_mem_normalizer (hCNorm c.property) homega }
  have hCp : IsPGroup 2 C := by
    apply IsPGroup.of_card (p := 2) (G := C) (n := 1)
    simp [C, Nat.card_zpowers,
      orderOf_eq_prime hs.sq_eq_one hs.ne_one]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixedZero : Nat.card (MulAction.fixedPoints C FixedP) = 0 := by
    rw [Finite.card_eq_zero_iff]
    refine ⟨fun omega => ?_⟩
    have hsFix := MulAction.mem_fixedPoints.mp omega.property
      (⟨s, Subgroup.mem_zpowers s⟩ : C)
    have hsFixVal : s • (omega : Omega) = omega :=
      congrArg Subtype.val hsFix
    exact hfree omega omega.1.property hsFixVal
  have hmod := hCp.card_modEq_card_fixedPoints FixedP
  rw [hfixedZero] at hmod
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod)

/-- Proposition 3.7(d), transported from the base/intersection coordinates
to an arbitrary ordered pair of distinct points.  A swapping involution that
normalizes a Sylow subgroup of the two-point stabilizer has exactly `m_p`
inverted elements. -/
public theorem IsStronglyEmbedded.theorem4b_twoPoint_sylow_invertedCard_eq_primeShare
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X} {p : ℕ} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z) (hp : Nat.Prime p)
    {beta gamma : conjugateCosetSpace M}
    (hbetaGamma : beta ≠ gamma)
    (hPSylow : theorem4bIsSylowSubgroupOf p P
      (MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma))
    (ht : IsInvolution t)
    (htNormP : t ∈ Subgroup.normalizer (P : Set X))
    (htBeta : t • beta = gamma) :
    theorem4bInvertedCard t P = theorem4bPrimeShare M z p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let base : conjugateCosetSpace M := QuotientGroup.mk 1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X beta base
  let gamma' : conjugateCosetSpace M := g • gamma
  let t' : X := rightConjugateElem t g⁻¹
  let P' : Subgroup X := P.conjBy g
  let D : Subgroup X :=
    MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma
  let D' : Subgroup X := M ⊓ rightConjugate M t'
  have hgamma'Base : gamma' ≠ base := by
    intro h
    apply hbetaGamma
    apply MulAction.injective g
    exact hg.trans h.symm
  have ht' : IsInvolution t' := isInvolution_rightConjugateElem ht
  have ht'Base : t' • base = gamma' := by
    calc
      t' • base = t' • (g • beta) := by rw [hg]
      _ = g • (t • beta) := by
        simp [t', rightConjugateElem, mul_smul]
      _ = gamma' := by rw [htBeta]
  have ht'M : t' ∉ M := by
    intro htM
    have htFix : t' • base = base := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa [base, baseCoset_stabilizer] using htM
    exact hgamma'Base (ht'Base.symm.trans htFix)
  have hDconj : D.conjBy g = D' := by
    have hpair : D.conjBy g =
        MulAction.stabilizer X base ⊓
          MulAction.stabilizer X gamma' := by
      change (MulAction.stabilizer X beta ⊓
          MulAction.stabilizer X gamma).conjBy g = _
      rw [Subgroup.conjBy,
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      rw [hg]
    have hstabGamma : MulAction.stabilizer X gamma' =
        rightConjugate M t' := by
      rw [← ht'Base]
      simpa [base, MulAction.Quotient.smul_mk, smul_eq_mul,
        ht'.inv_eq_self] using conjugateCoset_stabilizer M t'
    rw [hpair, baseCoset_stabilizer, hstabGamma]
  have hPD : P ≤ D := by
    rcases hPSylow with ⟨S, hPeq⟩
    rw [hPeq]
    simpa [D] using
      (Subgroup.map_le_range D.subtype (S : Subgroup D))
  have hP'D' : P' ≤ D' := by
    rw [← hDconj]
    exact Subgroup.map_mono hPD
  have hPp : IsPGroup p P := by
    rcases hPSylow with ⟨S, hPeq⟩
    rw [hPeq]
    exact S.isPGroup'.map D.subtype
  have hP'p : IsPGroup p P' := by
    exact hPp.map (MulAut.conj g).toMonoidHom
  have hPcard : Nat.card P = p ^ (Nat.card D).factorization p := by
    rcases hPSylow with ⟨S, hPeq⟩
    rw [hPeq, Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  have hDcard : Nat.card D' = Nat.card D := by
    rw [← hDconj]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hP'card : Nat.card P' = p ^ (Nat.card D').factorization p := by
    calc
      Nat.card P' = Nat.card P :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = p ^ (Nat.card D).factorization p := hPcard
      _ = p ^ (Nat.card D').factorization p := by rw [hDcard]
  have hP'D'p : IsPGroup p (P'.subgroupOf D') := by
    exact hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'D').symm
  obtain ⟨S', hP'S'⟩ := hP'D'p.exists_le_sylow
  let Q : Subgroup X := (S' : Subgroup D').map D'.subtype
  have hP'Q : P' ≤ Q := by
    intro x hxP'
    let xD : D' := ⟨x, hP'D' hxP'⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hP'S' (show xD ∈ P'.subgroupOf D' from hxP'), rfl⟩
  have hQcard : Nat.card Q = p ^ (Nat.card D').factorization p := by
    change Nat.card ((S' : Subgroup D').map D'.subtype) = _
    rw [Subgroup.card_map_of_injective D'.subtype_injective]
    exact Sylow.card_eq_multiplicity S'
  have hQP' : Q = P' := by
    exact (Subgroup.eq_of_le_of_card_ge hP'Q (by
      rw [hQcard, hP'card])).symm
  have hP'Sylow : theorem4bIsSylowSubgroupOf p P' D' := by
    exact ⟨S', hQP'.symm⟩
  have ht'NormP' : t' ∈ Subgroup.normalizer (P' : Set X) := by
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (Subgroup.zpowers_le.mpr htNormP) g
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨t, Subgroup.mem_zpowers t, ?_⟩
    simp [t', rightConjugateElem, MulAut.conj_apply]
  have hexact :=
    hM.theorem4b_inf_rightConjugate_invertedCard_eq_primeShare_of_sylow
      hzM hz ht' ht'M hp (by simpa [D'] using hP'Sylow) ht'NormP'
  have hcard := theorem4bInvertedCard_conjBy t g⁻¹ P
  rw [← hcard]
  simpa [t', P'] using hexact

private theorem involution_mem_normalizer_twoPointStabilizer_of_swap
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {t : G} {beta gamma : Omega}
    (ht : IsInvolution t) (htBeta : t • beta = gamma) :
    t ∈ Subgroup.normalizer
      ((MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have htGamma : t • gamma = beta := by
    rw [← htBeta, ← mul_smul, htt, one_smul]
  have hforward : ∀ {x : G},
      x ∈ (MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) →
      t * x * t⁻¹ ∈ (MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) := by
    intro x hx
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_,
      MulAction.mem_stabilizer_iff.mpr ?_⟩
    · calc
        (t * x * t⁻¹) • beta = t • (x • (t⁻¹ • beta)) := by
          simp [mul_smul, mul_assoc]
        _ = t • (x • gamma) := by rw [ht.inv_eq_self, htBeta]
        _ = t • gamma := by rw [MulAction.mem_stabilizer_iff.mp hx.2]
        _ = beta := htGamma
    · calc
        (t * x * t⁻¹) • gamma = t • (x • (t⁻¹ • gamma)) := by
          simp [mul_smul, mul_assoc]
        _ = t • (x • beta) := by rw [ht.inv_eq_self, htGamma]
        _ = t • beta := by rw [MulAction.mem_stabilizer_iff.mp hx.1]
        _ = gamma := htBeta
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward
  · intro hx
    have hback := hforward hx
    have hcancel : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [ht.inv_eq_self]
      calc
        t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [htt]; simp
    rwa [hcancel] at hback

/-- Proposition 3.7(c), in arbitrary two-point coordinates. -/
public theorem IsStronglyEmbedded.theorem4b_twoPoint_invertedCard_le_primeShare
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X} {p : ℕ} {P : Subgroup X}
    (hzM : z ∈ M) (hz : IsInvolution z) (hp : Nat.Prime p)
    {beta gamma : conjugateCosetSpace M}
    (hbetaGamma : beta ≠ gamma)
    (hPp : IsPGroup p P)
    (hPD : P ≤ MulAction.stabilizer X beta ⊓
      MulAction.stabilizer X gamma)
    (ht : IsInvolution t)
    (htNormP : t ∈ Subgroup.normalizer (P : Set X))
    (htBeta : t • beta = gamma) :
    theorem4bInvertedCard t P ≤ theorem4bPrimeShare M z p := by
  let D : Subgroup X := MulAction.stabilizer X beta ⊓
    MulAction.stabilizer X gamma
  have hDodd : Odd (Nat.card D) := by
    apply twoPointStabilizer_card_odd
      (hunique := fun {u} hu {a b} ha hb =>
        (hM.involution_fixed_coset_unique hu).unique ha hb)
    exact hbetaGamma
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using
      involution_mem_normalizer_twoPointStabilizer_of_swap ht htBeta
  obtain ⟨Q, hQSylow, hPQ, htNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hDodd ht htNormD hp hPp (by simpa [D] using hPD) htNormP
  have hQexact :=
    hM.theorem4b_twoPoint_sylow_invertedCard_eq_primeShare
      hzM hz hp hbetaGamma (by simpa [D] using hQSylow)
        ht htNormQ htBeta
  exact (theorem4bInvertedCard_mono hPQ).trans_eq hQexact

private theorem mem_of_mem_inverted_of_card_eq_of_le
    {G : Type*} [Group G] [Finite G] {s : G} {P B : Subgroup G}
    (hPB : P ≤ B)
    (hcard : theorem4bInvertedCard s P = theorem4bInvertedCard s B)
    {x : G} (hxB : x ∈ B) (hxInv : s * x * s⁻¹ = x⁻¹) :
    x ∈ P := by
  let f : {y : G // y ∈ P ∧ s * y * s⁻¹ = y⁻¹} →
      {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} :=
    fun y => ⟨y, hPB y.property.1, y.property.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg
      (fun q : {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} => (q : G)) hab
    simpa [f] using hval
  have hcardTypes :
      Nat.card {y : G // y ∈ P ∧ s * y * s⁻¹ = y⁻¹} =
        Nat.card {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} := by
    simpa [theorem4bInvertedCard] using hcard
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).2
      ⟨hf, hcardTypes⟩).2
  obtain ⟨y, hy⟩ := hsurj ⟨x, hxB, hxInv⟩
  have hyval : (y : G) = x := congrArg Subtype.val hy
  simpa [hyval] using y.property.1

/-- The elementwise form of the Lemma 5.6 commutator argument: if the
inverted sets in nested subgroups `P ≤ A ≤ B` have the same cardinality,
then an involution normalizing `B` also normalizes `A`. -/
private theorem mem_normalizer_of_invertedCard_eq_of_le
    {G : Type*} [Group G] [Finite G] {s : G}
    {P A B : Subgroup G}
    (hs : IsInvolution s)
    (hPA : P ≤ A) (hAB : A ≤ B)
    (hsNormB : s ∈ Subgroup.normalizer (B : Set G))
    (hcard : theorem4bInvertedCard s P = theorem4bInvertedCard s B) :
    s ∈ Subgroup.normalizer (A : Set G) := by
  have hPB : P ≤ B := hPA.trans hAB
  have hss : s * s = 1 := by
    simpa [pow_two] using hs.sq_eq_one
  have hforward : ∀ {a : G}, a ∈ A → s * a * s⁻¹ ∈ A := by
    intro a haA
    have hconjB : s * a * s⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hsNormB a).1 (hAB haA)
    let c : G := s * a * s⁻¹ * a⁻¹
    have hcB : c ∈ B := B.mul_mem hconjB (B.inv_mem (hAB haA))
    have hcInv : s * c * s⁻¹ = c⁻¹ := by
      dsimp [c]
      rw [hs.inv_eq_self]
      calc
        s * (s * a * s * a⁻¹) * s =
            (s * s) * a * s * a⁻¹ * s := by group
        _ = a * s * a⁻¹ * s := by rw [hss]; simp
        _ = (s * a * s * a⁻¹)⁻¹ := by
          simp only [mul_inv_rev, inv_inv, hs.inv_eq_self]
          group
    have hcP := mem_of_mem_inverted_of_card_eq_of_le
      hPB hcard hcB hcInv
    have hconjEq : s * a * s⁻¹ = c * a := by
      simp [c]
    rw [hconjEq]
    exact A.mul_mem (hPA hcP) haA
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hforward
  · intro ha
    have hback := hforward ha
    have hcancel : s * (s * a * s⁻¹) * s⁻¹ = a := by
      rw [hs.inv_eq_self]
      calc
        s * (s * a * s) * s = (s * s) * a * (s * s) := by group
        _ = a := by rw [hss]; simp
    rwa [hcancel] at hback

private def theorem4bFixedPointsConjByEquiv
    {G : Type*} [Group G] {M P : Subgroup G} (g : G) :
    theorem4bFixedPoints M P ≃ theorem4bFixedPoints M (P.conjBy g) where
  toFun omega := ⟨g • (omega : conjugateCosetSpace M), by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyP, rfl⟩
    calc
      (g * y * g⁻¹) • (g • (omega : conjugateCosetSpace M)) =
          g • (y • (omega : conjugateCosetSpace M)) := by
            simp [mul_smul, mul_assoc]
      _ = g • (omega : conjugateCosetSpace M) := by
        rw [omega.property y hyP]⟩
  invFun omega := ⟨g⁻¹ • (omega : conjugateCosetSpace M), by
    intro y hyP
    have hyConj : g * y * g⁻¹ ∈ P.conjBy g := by
      exact Subgroup.mem_map.mpr ⟨y, hyP, rfl⟩
    calc
      y • (g⁻¹ • (omega : conjugateCosetSpace M)) =
          g⁻¹ • ((g * y * g⁻¹) •
            (omega : conjugateCosetSpace M)) := by
              simp [mul_smul, mul_assoc]
      _ = g⁻¹ • (omega : conjugateCosetSpace M) := by
        rw [omega.property _ hyConj]⟩
  left_inv omega := by
    apply Subtype.ext
    simp
  right_inv omega := by
    apply Subtype.ext
    simp

private theorem theorem4bFixedPoints_card_conjBy
    {G : Type*} [Group G] [Finite G] {M P : Subgroup G} (g : G) :
    Nat.card (theorem4bFixedPoints M (P.conjBy g)) =
      Nat.card (theorem4bFixedPoints M P) :=
  (Nat.card_congr (theorem4bFixedPointsConjByEquiv g)).symm

/-- The first paragraph of Lemma 5.8: maximality among `p`-subgroups of one
point stabilizer fixing at least two points makes the ambient normalizer
transitive on the fixed-point set, and then upgrades that maximality to the
corresponding global condition. -/
private theorem local_maximal_two_fixed_transitive_and_global
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ} (hp : Nat.Prime p)
    {beta : conjugateCosetSpace M}
    (hPp : IsPGroup p P)
    (hPbeta : P ≤ MulAction.stabilizer X beta)
    (hPtwo : 2 ≤ Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P})
    (hmax : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X beta →
      2 ≤ Nat.card {omega : conjugateCosetSpace M //
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q} →
      P ≤ Q → Q = P) :
    IsTransitiveOn (Subgroup.normalizer (P : Set X))
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) P) ∧
      Maximal (fun Q : Subgroup X =>
        IsPGroup p Q ∧
          1 < Nat.card {omega : conjugateCosetSpace M //
            omega ∈ fixedPointsOfSubgroup X
              (conjugateCosetSpace M) Q}) P := by
  classical
  let Omega := conjugateCosetSpace M
  have hbeta : beta ∈ fixedPointsOfSubgroup X Omega P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPbeta hxP)
  have hreach : ∀ gamma : Omega,
      gamma ∈ fixedPointsOfSubgroup X Omega P →
      ∃ n : Subgroup.normalizer (P : Set X),
        (n : X) • beta = gamma := by
    intro gamma hgamma
    by_cases hbetaGamma : beta = gamma
    · exact ⟨1, by simp [hbetaGamma]⟩
    let D : Subgroup X :=
      MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma
    have hPD : P ≤ D := by
      intro x hxP
      exact ⟨hPbeta hxP,
        MulAction.mem_stabilizer_iff.mpr (hgamma x hxP)⟩
    let PD : Subgroup D := P.subgroupOf D
    have hPDp : IsPGroup p PD :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
    obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
    let Q : Subgroup X := (S : Subgroup D).map D.subtype
    have hPQ : P ≤ Q := by
      intro x hxP
      let xD : D := ⟨x, hPD hxP⟩
      exact Subgroup.mem_map.mpr
        ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
    have hQp : IsPGroup p Q := S.isPGroup'.map D.subtype
    have hQD : Q ≤ D := by
      simpa [Q] using Subgroup.map_le_range D.subtype (S : Subgroup D)
    have hQbeta : beta ∈ fixedPointsOfSubgroup X Omega Q := by
      intro x hxQ
      exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).1
    have hQgamma : gamma ∈ fixedPointsOfSubgroup X Omega Q := by
      intro x hxQ
      exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).2
    have hQtwo : 2 ≤ Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup X Omega Q} := by
      let f : Fin 2 → {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega Q} :=
        fun i => if i = 0 then ⟨beta, hQbeta⟩ else ⟨gamma, hQgamma⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaGamma
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaGamma
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
    have hQP : Q = P :=
      hmax Q hQp (hQD.trans inf_le_left) hQtwo hPQ
    have hPsyl : theorem4bIsSylowSubgroupOf p P D :=
      ⟨S, by simpa [Q] using hQP.symm⟩
    obtain ⟨t, _ht, htNorm, htBeta, _htGamma⟩ :=
      exists_involution_normalizing_of_sylow_twoPoint
        hM hp hbetaGamma hPsyl
    exact ⟨⟨t, htNorm⟩, htBeta⟩
  have htrans : IsTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X Omega P) := by
    intro gamma delta hgamma hdelta
    obtain ⟨ngamma, hngamma⟩ := hreach gamma hgamma
    obtain ⟨ndelta, hndelta⟩ := hreach delta hdelta
    let n : Subgroup.normalizer (P : Set X) := ndelta * ngamma⁻¹
    refine ⟨n, ?_⟩
    change ((ndelta : X) * (ngamma : X)⁻¹) • gamma = delta
    rw [mul_smul, ← hngamma]
    simp [hndelta]
  refine ⟨htrans, ⟨⟨hPp, by omega⟩, ?_⟩⟩
  intro Q hQgood hPQ
  let FixedQ := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega Q}
  have hFixedQpos : 0 < Nat.card FixedQ := by
    exact lt_trans (by decide) hQgood.2
  letI : Nonempty FixedQ := (Nat.card_pos_iff.mp hFixedQpos).1
  let deltaQ : FixedQ := Classical.choice inferInstance
  let delta : Omega := deltaQ
  have hdeltaQ : delta ∈ fixedPointsOfSubgroup X Omega Q :=
    deltaQ.property
  have hdeltaP : delta ∈ fixedPointsOfSubgroup X Omega P := by
    intro x hxP
    exact hdeltaQ x (hPQ hxP)
  obtain ⟨n, hn⟩ := htrans hdeltaP hbeta
  let Qn : Subgroup X := Q.conjBy (n : X)
  have hQnp : IsPGroup p Qn := by
    exact hQgood.1.map (MulAut.conj (n : X)).toMonoidHom
  have hPconj : P.conjBy (n : X) = P :=
    section11_conjBy_eq_of_mem_normalizer n.property
  have hPQn : P ≤ Qn := by
    rw [← hPconj]
    exact Subgroup.map_mono hPQ
  have hnInvBeta : (n : X)⁻¹ • beta = delta := by
    rw [← hn]
    exact inv_smul_smul (n : X) delta
  have hQnBeta : Qn ≤ MulAction.stabilizer X beta := by
    intro x hxQn
    change x ∈ Q.conjBy (n : X) at hxQn
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
    rcases hxQn with ⟨y, hyQ, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    calc
      ((n : X) * y * (n : X)⁻¹) • beta =
          (n : X) • (y • ((n : X)⁻¹ • beta)) := by
            simp [mul_smul, mul_assoc]
      _ = (n : X) • (y • delta) := by rw [hnInvBeta]
      _ = (n : X) • delta := by rw [hdeltaQ y hyQ]
      _ = beta := hn
  have hQntwo : 2 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega Qn} := by
    let f : FixedQ → {omega : Omega //
        omega ∈ fixedPointsOfSubgroup X Omega Qn} := fun omega =>
      ⟨(n : X) • (omega : Omega), by
        intro x hxQn
        change x ∈ Q.conjBy (n : X) at hxQn
        rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
        rcases hxQn with ⟨y, hyQ, rfl⟩
        calc
          ((n : X) * y * (n : X)⁻¹) •
              ((n : X) • (omega : Omega)) =
                (n : X) • (y • (omega : Omega)) := by
                  simp [mul_smul, mul_assoc]
          _ = (n : X) • (omega : Omega) := by
            rw [omega.property y hyQ]⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply MulAction.injective (n : X)
      exact congrArg Subtype.val hab
    have hFixedQtwo : 2 ≤ Nat.card FixedQ := by
      have hQgood' : 1 < Nat.card FixedQ := by
        simpa only [FixedQ] using hQgood.2
      omega
    exact hFixedQtwo.trans (Nat.card_le_card_of_injective f hf)
  have hQnP : Qn = P := hmax Qn hQnp hQnBeta hQntwo hPQn
  have hnInvNorm : (n : X)⁻¹ ∈
      Subgroup.normalizer (P : Set X) :=
    (Subgroup.normalizer (P : Set X)).inv_mem n.property
  have hQnP' : Q.conjBy (n : X) = P := by
    simpa [Qn] using hQnP
  have hQP : Q = P := by
    calc
      Q = (Q.conjBy (n : X)).conjBy (n : X)⁻¹ :=
        (Subgroup.conjBy_inv Q (n : X)).symm
      _ = P.conjBy (n : X)⁻¹ := by rw [hQnP']
      _ = P := section11_conjBy_eq_of_mem_normalizer hnInvNorm
  exact hQP.le

/-- Chapter 1, Lemma 2.1 in the form used by Lemma 5.8: an odd-prime
Sylow subgroup of a two-point stabilizer which fixes exactly those two points
is already an ambient Sylow subgroup. -/
public theorem chapter1_two_fixed_local_sylow_is_ambient
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega] {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    {P : Subgroup G} {alpha beta : Omega}
    (hPp : IsPGroup p P)
    (halphaBeta : alpha ≠ beta)
    (hPalpha : alpha ∈ fixedPointsOfSubgroup G Omega P)
    (hPbeta : beta ∈ fixedPointsOfSubgroup G Omega P)
    (hPcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P} = 2)
    (hPsyl : theorem4bIsSylowSubgroupOf p P
      (MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta)) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  classical
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  let Q : Subgroup G := (S : Subgroup G)
  have hPQ : P ≤ Q := hPS
  have hQP : Q = P := by
    by_contra hne
    have hPQlt : P < Q := lt_of_le_of_ne hPQ (Ne.symm hne)
    obtain ⟨A, hAp, hPA, hAQ, hAN⟩ :=
      exists_larger_normalizer_pSubgroup hp S.isPGroup' hPQlt
    have hAD : A ≤
        MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta :=
      odd_pSubgroup_le_pairStabilizer_of_normalizes
        hp hpOdd hAp hAN halphaBeta hPalpha hPbeta hPcard
    have hAP : A = P :=
      eq_of_isPGroup_of_le_of_sylow hp hPsyl hAp hPA.le hAD
    exact hPA.ne hAP.symm
  exact ⟨S, hQP⟩

/-- Chapter 1, Lemma 2.2 (Bender's criterion), in fixed-point-cardinality
form. -/
public theorem chapter1_bender_criterion
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega]
    (hpre : MulAction.IsPretransitive G Omega)
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    (hfixed : ∀ {alpha beta : Omega}, alpha ≠ beta →
      ∀ P : Subgroup G,
        theorem4bIsSylowSubgroupOf p P
          (MulAction.stabilizer G alpha ⊓
            MulAction.stabilizer G beta) →
        Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega P} = 2) :
    MulAction.IsMultiplyPretransitive G Omega 2 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : MulAction.IsPretransitive G Omega := hpre
  rw [MulAction.is_two_pretransitive_iff]
  intro alpha beta gamma delta halphaBeta hgammaDelta
  obtain ⟨g, hgAlpha⟩ := MulAction.exists_smul_eq G alpha gamma
  let beta' : Omega := g • beta
  have hgammaBeta' : gamma ≠ beta' := by
    intro h
    apply halphaBeta
    apply MulAction.injective g
    exact hgAlpha.trans h
  let Dβ : Subgroup G :=
    MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G beta'
  let Dδ : Subgroup G :=
    MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G delta
  let Sβ : Sylow p Dβ := default
  let Sδ : Sylow p Dδ := default
  let P : Subgroup G := (Sβ : Subgroup Dβ).map Dβ.subtype
  let Q : Subgroup G := (Sδ : Subgroup Dδ).map Dδ.subtype
  have hPp : IsPGroup p P := Sβ.isPGroup'.map Dβ.subtype
  have hQp : IsPGroup p Q := Sδ.isPGroup'.map Dδ.subtype
  have hPDβ : P ≤ Dβ := by
    simpa [P] using Subgroup.map_le_range Dβ.subtype (Sβ : Subgroup Dβ)
  have hQDδ : Q ≤ Dδ := by
    simpa [Q] using Subgroup.map_le_range Dδ.subtype (Sδ : Subgroup Dδ)
  have hPgamma : gamma ∈ fixedPointsOfSubgroup G Omega P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPDβ hxP).1
  have hPbeta : beta' ∈ fixedPointsOfSubgroup G Omega P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPDβ hxP).2
  have hQgamma : gamma ∈ fixedPointsOfSubgroup G Omega Q := by
    intro x hxQ
    exact MulAction.mem_stabilizer_iff.mp (hQDδ hxQ).1
  have hQdelta : delta ∈ fixedPointsOfSubgroup G Omega Q := by
    intro x hxQ
    exact MulAction.mem_stabilizer_iff.mp (hQDδ hxQ).2
  have hPcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P} = 2 := by
    apply hfixed hgammaBeta' P
    change theorem4bIsSylowSubgroupOf p P Dβ
    exact ⟨Sβ, rfl⟩
  have hQcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega Q} = 2 := by
    apply hfixed hgammaDelta Q
    change theorem4bIsSylowSubgroupOf p Q Dδ
    exact ⟨Sδ, rfl⟩
  obtain ⟨Tβ, hTβP⟩ := chapter1_two_fixed_local_sylow_is_ambient
    hp hpOdd hPp hgammaBeta' hPgamma hPbeta hPcard ⟨Sβ, rfl⟩
  obtain ⟨Tδ, hTδQ⟩ := chapter1_two_fixed_local_sylow_is_ambient
    hp hpOdd hQp hgammaDelta hQgamma hQdelta hQcard ⟨Sδ, rfl⟩
  let A : Subgroup G := MulAction.stabilizer G gamma
  have hTβA : (Tβ : Subgroup G) ≤ A := by
    rw [hTβP]
    exact hPDβ.trans inf_le_left
  have hTδA : (Tδ : Subgroup G) ≤ A := by
    rw [hTδQ]
    exact hQDδ.trans inf_le_left
  let TβA : Sylow p A := Tβ.subtype hTβA
  let TδA : Sylow p A := Tδ.subtype hTδA
  have hTβAmap : (TβA : Subgroup A).map A.subtype = P := by
    rw [show (TβA : Subgroup A) =
      (Tβ : Subgroup G).subgroupOf A by rfl,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTβA, hTβP]
  have hTδAmap : (TδA : Subgroup A).map A.subtype = Q := by
    rw [show (TδA : Subgroup A) =
      (Tδ : Subgroup G).subgroupOf A by rfl,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTδA, hTδQ]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq A TβA TδA
  have hkGamma : (k : G) • gamma = gamma :=
    MulAction.mem_stabilizer_iff.mp k.property
  have hkBetaFixed : (k : G) • beta' ∈
      fixedPointsOfSubgroup G Omega Q := by
    intro q hqQ
    have hqMap : q ∈ (TδA : Subgroup A).map A.subtype := by
      rw [hTδAmap]
      exact hqQ
    rcases Subgroup.mem_map.mp hqMap with ⟨qA, hqTδ, rfl⟩
    have hqSmul : qA ∈ (k • TβA : Sylow p A) := by
      rw [hk]
      exact hqTδ
    have hqSmul' : qA ∈
        ((k • TβA : Sylow p A) : Subgroup A) := hqSmul
    rw [Sylow.coe_subgroup_smul] at hqSmul'
    rcases Subgroup.mem_map.mp hqSmul' with ⟨rA, hrTβ, hrq⟩
    have hrP : (rA : G) ∈ P := by
      rw [← hTβAmap]
      exact Subgroup.mem_map_of_mem A.subtype hrTβ
    have hrFix : (rA : G) • beta' = beta' := hPbeta _ hrP
    have hrqG : (MulAut.conj k rA : A) = qA := hrq
    calc
      (qA : G) • ((k : G) • beta') =
          ((MulAut.conj k rA : A) : G) •
            ((k : G) • beta') := by rw [hrqG]
      _ = (k : G) • ((rA : G) • beta') := by
        simp [MulAut.conj_apply, mul_smul, mul_assoc]
      _ = (k : G) • beta' := by rw [hrFix]
  let FixedQ := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup G Omega Q}
  let gammaQ : FixedQ := ⟨gamma, hQgamma⟩
  let deltaQ : FixedQ := ⟨delta, hQdelta⟩
  let kbetaQ : FixedQ := ⟨(k : G) • beta', hkBetaFixed⟩
  obtain ⟨otherQ, _hotherQ, hotherQUnique⟩ :=
    (Nat.card_eq_two_iff' gammaQ).mp hQcard
  have hdeltaOther : deltaQ = otherQ := by
    apply hotherQUnique deltaQ
    intro h
    exact hgammaDelta (congrArg Subtype.val h).symm
  have hkbetaNeGamma : kbetaQ ≠ gammaQ := by
    intro h
    apply hgammaBeta'
    apply MulAction.injective (k : G)
    exact hkGamma.trans (congrArg Subtype.val h).symm
  have hkBeta : (k : G) • beta' = delta :=
    congrArg Subtype.val
      ((hotherQUnique kbetaQ hkbetaNeGamma).trans hdeltaOther.symm)
  refine ⟨(k : G) * g, ?_, ?_⟩
  · rw [mul_smul, hgAlpha, hkGamma]
  · calc
      ((k : G) * g) • beta = (k : G) • (g • beta) := mul_smul _ _ _
      _ = (k : G) • beta' := rfl
      _ = delta := hkBeta

private theorem normalizer_involution_at_of_transitive
    {X Omega : Type*} [Group X] [MulAction X Omega]
    {P : Subgroup X}
    (htrans : IsTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X Omega P))
    {s : X} (hs : IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set X))
    {alpha : Omega} (hsAlpha : s • alpha = alpha)
    (halpha : alpha ∈ fixedPointsOfSubgroup X Omega P)
    {gamma : Omega}
    (hgamma : gamma ∈ fixedPointsOfSubgroup X Omega P) :
    ∃ u : X, u ∈ involutionsSet X ∧ IsInvolution u ∧
      u ∈ Subgroup.normalizer (P : Set X) ∧ u • gamma = gamma := by
  obtain ⟨n, hnAlpha⟩ := htrans halpha hgamma
  let u : X := rightConjugateElem s (n : X)⁻¹
  have hu : IsInvolution u :=
    isInvolution_rightConjugateElem hs
  have huNorm : u ∈ Subgroup.normalizer (P : Set X) := by
    have hmem := (Subgroup.normalizer (P : Set X)).mul_mem
      ((Subgroup.normalizer (P : Set X)).mul_mem n.property hsNorm)
      ((Subgroup.normalizer (P : Set X)).inv_mem n.property)
    simpa [u, rightConjugateElem] using hmem
  have hnInvGamma : (n : X)⁻¹ • gamma = alpha := by
    rw [← hnAlpha]
    exact inv_smul_smul (n : X) alpha
  have huGamma : u • gamma = gamma := by
    calc
      u • gamma = (n : X) •
          (s • ((n : X)⁻¹ • gamma)) := by
            simp [u, rightConjugateElem, mul_smul]
      _ = (n : X) • (s • alpha) := by rw [hnInvGamma]
      _ = (n : X) • alpha := by rw [hsAlpha]
      _ = gamma := hnAlpha
  exact ⟨u, hu, hu, huNorm, huGamma⟩

/-- Proposition 5.2(a), in the form used by Corollary 5.7.  The maximality
predicate retains both `|Omega_P| ≥ 3` and the exact Proposition 3.7(d)
inverted-cardinality equality. -/
public theorem proposition_5_2_fixes_involution_fixedPoint
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X}
    (hzM : z ∈ M) (hz : IsInvolution z) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hmax : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q} ∧
        ∃ u : X, IsInvolution u ∧
          u ∈ Subgroup.normalizer (Q : Set X) ∧
          theorem4bInvertedCard u Q = theorem4bPrimeShare M z p) P)
    {s : X} (hs : IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set X))
    (hsCard : theorem4bInvertedCard s P = theorem4bPrimeShare M z p)
    {alpha : conjugateCosetSpace M} (hsAlpha : s • alpha = alpha) :
    alpha ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
  classical
  by_contra hPAlpha
  have hrank := normalizer_not_twoRank_of_not_fixed
    hM hp hpOdd hmax.1.1 hs hsNorm hsAlpha (by
      intro hPstab
      apply hPAlpha
      intro x hxP
      exact MulAction.mem_stabilizer_iff.mp (hPstab hxP))
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  let FixedP : SubMulAction N (conjugateCosetSpace M) :=
    { carrier := fixedPointsOfSubgroup X (conjugateCosetSpace M) P
      smul_mem' := fun n omega homega =>
        fixedPoints_smul_of_mem_normalizer n.property homega }
  let sN : N := ⟨s, hsNorm⟩
  have hsN : IsInvolution sN := IsInvolution.subtype hs hsNorm
  have hfree : ∀ omega : conjugateCosetSpace M,
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
      s • omega ≠ omega := by
    intro omega homega hsOmega
    have hEq := (hM.involution_fixed_coset_unique hs).unique hsAlpha hsOmega
    apply hPAlpha
    simpa [hEq] using homega
  have hEven : Even (Nat.card FixedP) := by
    change Even (Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P})
    exact fixedPoints_card_even_of_fixedPoint_free_involution
      hs hsNorm hfree
  have hFixedPpos : 0 < Nat.card FixedP := by
    change 0 < Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P}
    exact lt_trans (by decide) hmax.1.2.1
  letI : Nonempty FixedP := (Nat.card_pos_iff.mp hFixedPpos).1
  have hbadPair : ∃ beta delta : FixedP, beta ≠ delta ∧
      ∀ t : N, IsInvolution t →
        (t : X) • (beta : conjugateCosetSpace M) ≠
          (delta : conjugateCosetSpace M) := by
    by_contra hno
    push_neg at hno
    have hpair : ∀ beta delta : FixedP, beta ≠ delta →
        ∃ t : N, IsInvolution t ∧ t • beta = delta := by
      intro beta delta hne
      obtain ⟨t, ht, htMove⟩ := hno beta delta hne
      exact ⟨t, ht, by
        apply Subtype.ext
        exact htMove⟩
    have hcardTwo := chapter1_rank_one_pair_involutions_card_eq_two
      hrank hEven hpair
    have hthree : 2 < Nat.card FixedP := hmax.1.2.1
    omega
  obtain ⟨betaP, deltaP, hbetaDeltaP, hbad⟩ := hbadPair
  let beta : conjugateCosetSpace M := betaP
  let delta : conjugateCosetSpace M := deltaP
  have hbeta : beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    betaP.property
  have hdelta : delta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    deltaP.property
  have hbetaDelta : beta ≠ delta := by
    intro h
    exact hbetaDeltaP (Subtype.ext h)
  let D : Subgroup X :=
    MulAction.stabilizer X beta ⊓ MulAction.stabilizer X delta
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hbeta x hxP),
      MulAction.mem_stabilizer_iff.mpr (hdelta x hxP)⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let R : Subgroup X := (S : Subgroup D).map D.subtype
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hRD : R ≤ D := by
    simpa [R] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hRsyl : theorem4bIsSylowSubgroupOf p R D := ⟨S, rfl⟩
  obtain ⟨t, ht, htNormR, htBeta, _htDelta⟩ :=
    exists_involution_normalizing_of_sylow_twoPoint
      hM hp hbetaDelta hRsyl
  have hPRlt : P < R := by
    apply lt_of_le_of_ne hPR
    intro hEq
    have htNormP : t ∈ Subgroup.normalizer (P : Set X) := by
      rw [hEq]
      exact htNormR
    let tN : N := ⟨t, htNormP⟩
    have htN : IsInvolution tN := IsInvolution.subtype ht tN.property
    exact hbad tN htN htBeta
  have hRbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).1
  have hRdelta : delta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).2
  have hRcard : Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} = 2 := by
    apply Nat.le_antisymm
    · by_contra hle
      have hthree : 2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} := by
        omega
      have hRexact :=
        hM.theorem4b_twoPoint_sylow_invertedCard_eq_primeShare
          hzM hz hp hbetaDelta hRsyl ht htNormR htBeta
      have hRleP := hmax.2
        ⟨hRp, hthree, ⟨t, ht, htNormR, hRexact⟩⟩ hPR
      exact (not_le_of_gt hPRlt) hRleP
    · let f : Fin 2 → {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} :=
        fun i => if i = 0 then ⟨beta, hRbeta⟩ else ⟨delta, hRdelta⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaDelta
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaDelta
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hOmegaMod : Nat.card (conjugateCosetSpace M) ≡ 2 [MOD p] := by
    have hRcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hRp
    rwa [hRcard] at hRcong
  obtain ⟨A, hAp, hPA, hAR, hAN⟩ :=
    exists_larger_normalizer_pSubgroup hp hRp hPRlt
  let AN : Subgroup N := A.subgroupOf N
  have hANp : IsPGroup p AN :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨B, hANB⟩ := hANp.exists_le_sylow
  let BN : Subgroup N := (B : Subgroup N)
  let BX : Subgroup X := BN.map N.subtype
  have hABX : A ≤ BX := by
    intro a haA
    let aN : N := ⟨a, hAN haA⟩
    exact Subgroup.mem_map.mpr
      ⟨aN, hANB (show aN ∈ AN from haA), rfl⟩
  have hPBX : P ≤ BX := hPA.le.trans hABX
  have hBXp : IsPGroup p BX := B.isPGroup'.map N.subtype
  have hfactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({sN} : Set N) = ⊤ :=
    PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      hrank hsN
  have hbotp : IsPGroup p (⊥ : Subgroup N) := IsPGroup.of_bot
  obtain ⟨S₀, _hbotS₀, hsNormS₀⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      hsN hp hpOdd hbotp (by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp) hfactor
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S₀ B
  have hBconj : (B : Subgroup N) =
      (S₀ : Subgroup N).conjBy (g : N) := by
    rw [← hg]
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.conjBy]
    congr 1
  let vN : N := rightConjugateElem sN (g : N)⁻¹
  have hvN : IsInvolution vN := isInvolution_rightConjugateElem hsN
  have hvNormBN : vN ∈ Subgroup.normalizer ((B : Subgroup N) : Set N) := by
    rw [hBconj]
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (Subgroup.zpowers_le.mpr hsNormS₀) (g : N)
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨sN, Subgroup.mem_zpowers sN, ?_⟩
    simp [vN, rightConjugateElem]
  let v : X := (vN : X)
  have hv : IsInvolution v :=
    IsInvolution.map_of_injective hvN N.subtype Subtype.val_injective
  have hvNormBX : v ∈ Subgroup.normalizer (BX : Set X) := by
    have hvMapMem : v ∈
        (Subgroup.normalizer ((B : Subgroup N) : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hvNormBN
    exact (Subgroup.le_normalizer_map (H := (B : Subgroup N)) N.subtype)
      hvMapMem
  have hPconj : P.conjBy (g : X) = P :=
    section11_conjBy_eq_of_mem_normalizer g.property
  have hvEq : v = rightConjugateElem s (g : X)⁻¹ := by
    simp [v, vN, sN, rightConjugateElem]
  have hPconj' : P.conjBy (((g : X)⁻¹)⁻¹) = P := by
    simpa using hPconj
  have hInvPv : theorem4bInvertedCard v P =
      theorem4bPrimeShare M z p := by
    have hcard := theorem4bInvertedCard_conjBy s (g : X)⁻¹ P
    rw [hvEq, ← hPconj']
    exact hcard.trans hsCard
  let FixedB := {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) BX}
  have hBmod : Nat.card FixedB ≡ 2 [MOD p] := by
    have hBXcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hBXp
    exact hBXcong.symm.trans hOmegaMod
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    exact hpOdd.not_two_dvd_nat (dvd_refl 2)
  have hpGtTwo : 2 < p := by
    have hpTwo := hp.two_le
    omega
  have hBcardTwo : 2 ≤ Nat.card FixedB := by
    by_contra hnot
    have hlt : Nat.card FixedB < 2 := by omega
    change Nat.card FixedB % p = 2 % p at hBmod
    rw [Nat.mod_eq_of_lt (lt_trans hlt hpGtTwo),
      Nat.mod_eq_of_lt hpGtTwo] at hBmod
    omega
  letI : Nontrivial FixedB :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let lambda₀ : FixedB := Classical.choice inferInstance
  obtain ⟨eta₀, heta₀⟩ := exists_ne lambda₀
  have hexistsMoved : ∃ lambdaB : FixedB,
      v • (lambdaB : conjugateCosetSpace M) ≠ lambdaB := by
    by_cases hlambda₀ : v • (lambda₀ : conjugateCosetSpace M) = lambda₀
    · refine ⟨eta₀, ?_⟩
      intro hetaFix
      apply heta₀
      apply Subtype.ext
      exact (hM.involution_fixed_coset_unique hv).unique
        hetaFix hlambda₀
    · exact ⟨lambda₀, hlambda₀⟩
  obtain ⟨lambdaB, hlambdaMove⟩ := hexistsMoved
  let lambda : conjugateCosetSpace M := lambdaB
  let mu : conjugateCosetSpace M := v • lambda
  have hlambdaB : lambda ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) BX := lambdaB.property
  have hmuB : mu ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) BX :=
    fixedPoints_smul_of_mem_normalizer hvNormBX hlambdaB
  have hlambdaMu : lambda ≠ mu := by
    exact Ne.symm hlambdaMove
  have hvLambda : v • lambda = mu := rfl
  have hvMu : v • mu = lambda := by
    change v • (v • lambda) = lambda
    rw [← mul_smul, show v * v = 1 by
      simpa [pow_two] using hv.sq_eq_one]
    simp
  have hAcardThree : 3 ≤ Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) A} := by
    let FixedA := {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) A}
    let betaA : FixedA := ⟨beta, fun x hxA => hRbeta x (hAR hxA)⟩
    let deltaA : FixedA := ⟨delta, fun x hxA => hRdelta x (hAR hxA)⟩
    have hbetaDeltaA : betaA ≠ deltaA := by
      intro h
      apply hbetaDelta
      simpa [betaA, deltaA] using
        congrArg (fun q : FixedA =>
          (q : conjugateCosetSpace M)) h
    by_contra hnot
    have hnot' : ¬ 3 ≤ Nat.card FixedA := by
      simpa [FixedA] using hnot
    have hAcardLe : Nat.card FixedA ≤ 2 := by omega
    letI : Nontrivial FixedA := ⟨⟨betaA, deltaA, hbetaDeltaA⟩⟩
    have hAcardGtOne : 1 < Nat.card FixedA :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hAcard : Nat.card FixedA = 2 := by omega
    obtain ⟨otherA, _hotherA, hotherAUnique⟩ :=
      (Nat.card_eq_two_iff' betaA).mp hAcard
    have hdeltaOtherA : deltaA = otherA := by
      apply hotherAUnique deltaA
      exact Ne.symm hbetaDeltaA
    have hFixedAEq : ∀ omega : FixedA,
        omega = betaA ∨ omega = deltaA := by
      intro omega
      by_cases homega : omega = betaA
      · exact Or.inl homega
      · exact Or.inr ((hotherAUnique omega homega).trans
          hdeltaOtherA.symm)
    let lambdaA : FixedA := ⟨lambda, fun x hxA =>
      hlambdaB x (hABX hxA)⟩
    let muA : FixedA := ⟨mu, fun x hxA =>
      hmuB x (hABX hxA)⟩
    have hlambdaMuA : lambdaA ≠ muA := by
      intro h
      exact hlambdaMu (congrArg Subtype.val h)
    have hvBetaDelta : v • beta = delta := by
      rcases hFixedAEq lambdaA with hlambdaBetaA | hlambdaDeltaA
      · have hmuDeltaA : muA = deltaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaBetaA.trans hmuBetaA.symm
          · exact hmuDeltaA
        have hlambdaBeta : lambda = beta := by
          simpa [lambdaA, betaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hlambdaBetaA
        have hmuDelta : mu = delta := by
          simpa [muA, deltaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hmuDeltaA
        rw [← hlambdaBeta, hvLambda, hmuDelta]
      · have hmuBetaA : muA = betaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exact hmuBetaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaDeltaA.trans hmuDeltaA.symm
        have hlambdaDelta : lambda = delta := by
          simpa [lambdaA, deltaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hlambdaDeltaA
        have hmuBeta : mu = beta := by
          simpa [muA, betaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hmuBetaA
        rw [← hmuBeta, hvMu, hlambdaDelta]
    exact hbad vN hvN (by
      simpa [v] using hvBetaDelta)
  have hBpair : BX ≤ MulAction.stabilizer X lambda ⊓
      MulAction.stabilizer X mu := by
    intro x hxB
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hlambdaB x hxB),
      MulAction.mem_stabilizer_iff.mpr (hmuB x hxB)⟩
  have hInvBXUpper : theorem4bInvertedCard v BX ≤
      theorem4bPrimeShare M z p :=
    hM.theorem4b_twoPoint_invertedCard_le_primeShare
      hzM hz hp hlambdaMu hBXp hBpair hv hvNormBX hvLambda
  have hInvBX : theorem4bInvertedCard v BX =
      theorem4bPrimeShare M z p := by
    apply Nat.le_antisymm hInvBXUpper
    exact hInvPv.symm.trans_le (theorem4bInvertedCard_mono hPBX)
  have hInvPBX : theorem4bInvertedCard v P =
      theorem4bInvertedCard v BX := hInvPv.trans hInvBX.symm
  have hvNormA : v ∈ Subgroup.normalizer (A : Set X) :=
    mem_normalizer_of_invertedCard_eq_of_le
      hv hPA.le hABX hvNormBX hInvPBX
  have hInvA : theorem4bInvertedCard v A =
      theorem4bPrimeShare M z p := by
    apply Nat.le_antisymm
    · exact (theorem4bInvertedCard_mono hABX).trans_eq hInvBX
    · exact hInvPv.symm.trans_le
        (theorem4bInvertedCard_mono hPA.le)
  have hAleP := hmax.2
    ⟨hAp, by omega, ⟨v, hv, hvNormA, hInvA⟩⟩ hPA.le
  exact (not_le_of_gt hPA) hAleP

/-- Corollary 5.7(a--c) for an odd prime in the non-two-transitive branch. -/
public theorem corollary_5_7_normalized_fixedPoint_pair
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    ∃ (z : X) (Q : Subgroup X) (s : X)
        (alpha : conjugateCosetSpace M),
      z ∈ M ∧ IsInvolution z ∧ IsPGroup p Q ∧
      3 ≤ Nat.card (theorem4bFixedPoints M Q) ∧
      IsInvolution s ∧ s ∈ Subgroup.normalizer (Q : Set X) ∧
      theorem4bInvertedCard s Q = theorem4bPrimeShare M z p ∧
      s • alpha = alpha ∧
      alpha ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q := by
  classical
  obtain ⟨z, hzM, hz⟩ := hM.exists_involution
  have hnotFixed : ¬ ∀ {beta gamma : conjugateCosetSpace M},
      beta ≠ gamma →
      ∀ Q : Subgroup X,
        theorem4bIsSylowSubgroupOf p Q
          (MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma) →
        Nat.card (theorem4bFixedPoints M Q) = 2 := by
    intro hfixed
    exact hnot2 (chapter1_bender_criterion
      (conjugateCosetSpace_isPretransitive M) hp hpOdd hfixed)
  push_neg at hnotFixed
  obtain ⟨beta, gamma, hbetaGamma, Q, hQSylow, hQneTwo⟩ := hnotFixed
  have hQp : IsPGroup p Q := by
    rcases hQSylow with ⟨S, hQeq⟩
    rw [hQeq]
    exact S.isPGroup'.map
      (MulAction.stabilizer X beta ⊓
        MulAction.stabilizer X gamma).subtype
  have hQD : Q ≤ MulAction.stabilizer X beta ⊓
      MulAction.stabilizer X gamma := by
    rcases hQSylow with ⟨S, hQeq⟩
    rw [hQeq]
    simpa using Subgroup.map_le_range
      (MulAction.stabilizer X beta ⊓
        MulAction.stabilizer X gamma).subtype (S : Subgroup _)
  have hQbeta : beta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) Q := by
    intro x hxQ
    exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).1
  have hQgamma : gamma ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) Q := by
    intro x hxQ
    exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).2
  have hQtwo : 2 ≤ Nat.card (theorem4bFixedPoints M Q) := by
    let f : Fin 2 → theorem4bFixedPoints M Q :=
      fun i => if i = 0 then ⟨beta, hQbeta⟩ else ⟨gamma, hQgamma⟩
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply hbetaGamma
        simpa [f] using congrArg Subtype.val hij
      · exfalso
        apply hbetaGamma
        simpa [f] using (congrArg Subtype.val hij).symm
      · rfl
    simpa using Nat.card_le_card_of_injective f hf
  have hQthree : 3 ≤ Nat.card (theorem4bFixedPoints M Q) := by omega
  obtain ⟨t, ht, htNormQ, htBeta, _htGamma⟩ :=
    exists_involution_normalizing_of_sylow_twoPoint
      hM hp hbetaGamma hQSylow
  have hQexact :=
    hM.theorem4b_twoPoint_sylow_invertedCard_eq_primeShare
      hzM hz hp hbetaGamma hQSylow ht htNormQ htBeta
  let Good : Subgroup X → Prop := fun R =>
    IsPGroup p R ∧ 2 < Nat.card (theorem4bFixedPoints M R) ∧
      ∃ u : X, IsInvolution u ∧
        u ∈ Subgroup.normalizer (R : Set X) ∧
        theorem4bInvertedCard u R = theorem4bPrimeShare M z p
  have hQgood : Good Q :=
    ⟨hQp, by omega, ⟨t, ht, htNormQ, hQexact⟩⟩
  obtain ⟨R, _hQR, hRmax⟩ := Finite.exists_le_maximal hQgood
  obtain ⟨s, hs, hsNormR, hsCard⟩ := hRmax.1.2.2
  obtain ⟨alpha, hsAlpha⟩ :=
    (hM.involution_fixed_coset_unique hs).exists
  have hRalpha : alpha ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) R :=
    proposition_5_2_fixes_involution_fixedPoint
      hM hzM hz hp hpOdd hRmax hs hsNormR hsCard hsAlpha
  exact ⟨z, R, s, alpha, hzM, hz, hRmax.1.1, hRmax.1.2.1,
    hs, hsNormR, hsCard, hsAlpha, hRalpha⟩

/-- The Lemma 5.8 Sylow conclusion in the exact-two branch. -/
private theorem exists_ambient_sylow_fixedPoints_card_two
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    (hexact : ∃ E : Subgroup X,
      IsPGroup p E ∧ Nat.card (theorem4bFixedPoints M E) = 2) :
    ∃ P : Subgroup X,
      IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2 ∧
        ∃ T : Sylow p X, (T : Subgroup X) = P := by
  classical
  obtain ⟨E, hEp, hEcard⟩ := hexact
  have hEpos : 0 < Nat.card (theorem4bFixedPoints M E) := by omega
  letI : Nonempty (theorem4bFixedPoints M E) :=
    (Nat.card_pos_iff.mp hEpos).1
  let betaE : theorem4bFixedPoints M E := Classical.choice inferInstance
  let beta : conjugateCosetSpace M := betaE
  have hEbeta : E ≤ MulAction.stabilizer X beta := by
    intro x hxE
    exact MulAction.mem_stabilizer_iff.mpr (betaE.property x hxE)
  let Good : Subgroup X → Prop := fun Q =>
    IsPGroup p Q ∧ Q ≤ MulAction.stabilizer X beta ∧
      2 ≤ Nat.card (theorem4bFixedPoints M Q)
  have hEgood : Good E := ⟨hEp, hEbeta, by omega⟩
  obtain ⟨P, hEP, hPmax⟩ := Finite.exists_le_maximal hEgood
  have hPcardLe : Nat.card (theorem4bFixedPoints M P) ≤
      Nat.card (theorem4bFixedPoints M E) := by
    let f : theorem4bFixedPoints M P → theorem4bFixedPoints M E :=
      fun omega => ⟨omega, fun x hxE => omega.property x (hEP hxE)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hval := congrArg
        (fun q : theorem4bFixedPoints M E =>
          (q : conjugateCosetSpace M)) hab
      simpa [f] using hval
    exact Nat.card_le_card_of_injective f hf
  have hPcard : Nat.card (theorem4bFixedPoints M P) = 2 := by
    apply Nat.le_antisymm
    · exact hPcardLe.trans_eq hEcard
    · exact hPmax.1.2.2
  have hPbeta : beta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPmax.1.2.1 hxP)
  let betaP : theorem4bFixedPoints M P := ⟨beta, hPbeta⟩
  obtain ⟨gammaP, hgammaNe, _hgammaUnique⟩ :=
    (Nat.card_eq_two_iff' betaP).mp hPcard
  let gamma : conjugateCosetSpace M := gammaP
  have hgamma : gamma ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P := gammaP.property
  have hbetaGamma : beta ≠ gamma := by
    intro h
    exact hgammaNe (Subtype.ext h.symm)
  let D : Subgroup X := MulAction.stabilizer X beta ⊓
    MulAction.stabilizer X gamma
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨hPmax.1.2.1 hxP,
      MulAction.mem_stabilizer_iff.mpr (hgamma x hxP)⟩
  have hPDp : IsPGroup p (P.subgroupOf D) :=
    hPmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let R : Subgroup X := (S : Subgroup D).map D.subtype
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ P.subgroupOf D from hxP), rfl⟩
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hRD : R ≤ D := by
    simpa [R] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hRbeta : beta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).1
  have hRgamma : gamma ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).2
  have hRtwo : 2 ≤ Nat.card (theorem4bFixedPoints M R) := by
    let f : Fin 2 → theorem4bFixedPoints M R :=
      fun i => if i = 0 then ⟨beta, hRbeta⟩ else ⟨gamma, hRgamma⟩
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply hbetaGamma
        simpa [f] using congrArg Subtype.val hij
      · exfalso
        apply hbetaGamma
        simpa [f] using (congrArg Subtype.val hij).symm
      · rfl
    simpa using Nat.card_le_card_of_injective f hf
  have hRgood : Good R :=
    ⟨hRp, hRD.trans inf_le_left, hRtwo⟩
  have hPR_eq : P = R := hPmax.eq_of_le hRgood hPR
  have hPsyl : theorem4bIsSylowSubgroupOf p P D :=
    ⟨S, hPR_eq⟩
  obtain ⟨T, hTP⟩ := chapter1_two_fixed_local_sylow_is_ambient
    hp hpOdd hPmax.1.1 hbetaGamma hPbeta hgamma hPcard
      (by simpa [D] using hPsyl)
  exact ⟨P, hPmax.1.1, hPcard, T, hTP⟩

private theorem fixedPoints_card_two_of_sylow_pointStabilizer
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    {p : ℕ} (hp : Nat.Prime p)
    (T : Sylow p X) (hTP : (T : Subgroup X) = P)
    {beta : conjugateCosetSpace M}
    (hPbeta : beta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P)
    (hPcard : Nat.card (theorem4bFixedPoints M P) = 2)
    (alpha : conjugateCosetSpace M)
    (Ralpha : Sylow p (MulAction.stabilizer X alpha)) :
    Nat.card (theorem4bFixedPoints M
        ((Ralpha : Subgroup (MulAction.stabilizer X alpha)).map
          (MulAction.stabilizer X alpha).subtype)) = 2 ∧
      ∃ U : Sylow p X,
        (U : Subgroup X) =
          (Ralpha : Subgroup (MulAction.stabilizer X alpha)).map
            (MulAction.stabilizer X alpha).subtype := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let A : Subgroup X := MulAction.stabilizer X alpha
  let R : Subgroup X :=
    (Ralpha : Subgroup (MulAction.stabilizer X alpha)).map
      (MulAction.stabilizer X alpha).subtype
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X beta alpha
  let Tg : Sylow p X := g • T
  have hTgA : (Tg : Subgroup X) ≤ A := by
    intro x hxTg
    rw [show (Tg : Subgroup X) = P.conjBy g by
      calc
        (Tg : Subgroup X) = ((g • T : Sylow p X) : Subgroup X) := rfl
        _ = (T : Subgroup X).conjBy g := by
          simp only [Sylow.coe_subgroup_smul,
            Subgroup.pointwise_smul_def]
          rfl
        _ = P.conjBy g := by rw [hTP]] at hxTg
    rcases Subgroup.mem_map.mp hxTg with ⟨y, hyP, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    calc
      (g * y * g⁻¹) • alpha =
          g • (y • (g⁻¹ • alpha)) := by
            simp [mul_smul, mul_assoc]
      _ = g • (y • beta) := by
        rw [← hg]
        simp
      _ = g • beta := by rw [hPbeta y hyP]
      _ = alpha := hg
  let TgA : Sylow p A := Tg.subtype hTgA
  have hRcard : Nat.card R = p ^ (Nat.card A).factorization p := by
    change Nat.card
      ((Ralpha : Subgroup (MulAction.stabilizer X alpha)).map
        (MulAction.stabilizer X alpha).subtype) = _
    rw [Subgroup.card_map_of_injective
      (MulAction.stabilizer X alpha).subtype_injective]
    simpa [A] using Sylow.card_eq_multiplicity Ralpha
  have hTgcard : Nat.card (Tg : Subgroup X) =
      p ^ (Nat.card A).factorization p := by
    have hmap : (TgA : Subgroup A).map A.subtype =
        (Tg : Subgroup X) := by
      rw [show (TgA : Subgroup A) =
        (Tg : Subgroup X).subgroupOf A by rfl,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTgA]
    rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective]
    exact Sylow.card_eq_multiplicity TgA
  have hRp : IsPGroup p R := by
    exact Ralpha.isPGroup'.map
      (MulAction.stabilizer X alpha).subtype
  obtain ⟨U, hRU⟩ := hRp.exists_le_sylow
  have hUcard : Nat.card (U : Subgroup X) = Nat.card (Tg : Subgroup X) := by
    rw [Sylow.card_eq_multiplicity U, Sylow.card_eq_multiplicity Tg]
  have hRUeq : R = (U : Subgroup X) := by
    apply Subgroup.eq_of_le_of_card_ge hRU
    rw [hUcard, hTgcard, hRcard]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X T U
  have hUeq : (U : Subgroup X) = P.conjBy k := by
    calc
      (U : Subgroup X) = ((k • T : Sylow p X) : Subgroup X) := by rw [hk]
      _ = (T : Subgroup X).conjBy k := by
        simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
      _ = P.conjBy k := by rw [hTP]
  refine ⟨?_, U, hRUeq.symm⟩
  calc
    Nat.card (theorem4bFixedPoints M R) =
        Nat.card (theorem4bFixedPoints M (U : Subgroup X)) := by rw [hRUeq]
    _ = Nat.card (theorem4bFixedPoints M (P.conjBy k)) := by rw [hUeq]
    _ = Nat.card (theorem4bFixedPoints M P) :=
      theorem4bFixedPoints_card_conjBy k
    _ = 2 := hPcard

public theorem proposition_5_3_fixes_involution_fixedPoint
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hmax : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q}) P)
    {s : X} (hs : IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set X))
    {alpha : conjugateCosetSpace M} (hsAlpha : s • alpha = alpha) :
    alpha ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
  classical
  by_contra hPAlpha
  have hrank := normalizer_not_twoRank_of_not_fixed
    hM hp hpOdd hmax.1.1 hs hsNorm hsAlpha (by
      intro hPstab
      apply hPAlpha
      intro x hxP
      exact MulAction.mem_stabilizer_iff.mp (hPstab hxP))
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  let FixedP : SubMulAction N (conjugateCosetSpace M) :=
    { carrier := fixedPointsOfSubgroup X (conjugateCosetSpace M) P
      smul_mem' := fun n omega homega =>
        fixedPoints_smul_of_mem_normalizer n.property homega }
  let sN : N := ⟨s, hsNorm⟩
  have hsN : IsInvolution sN := IsInvolution.subtype hs hsNorm
  have hfree : ∀ omega : conjugateCosetSpace M,
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
      s • omega ≠ omega := by
    intro omega homega hsOmega
    have hEq := (hM.involution_fixed_coset_unique hs).unique hsAlpha hsOmega
    apply hPAlpha
    simpa [hEq] using homega
  have hEven : Even (Nat.card FixedP) := by
    change Even (Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P})
    exact fixedPoints_card_even_of_fixedPoint_free_involution
      hs hsNorm hfree
  have hFixedPpos : 0 < Nat.card FixedP := by
    change 0 < Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P}
    exact lt_trans (by decide) hmax.1.2
  letI : Nonempty FixedP := (Nat.card_pos_iff.mp hFixedPpos).1
  have hbadPair : ∃ beta delta : FixedP, beta ≠ delta ∧
      ∀ t : N, IsInvolution t →
        (t : X) • (beta : conjugateCosetSpace M) ≠
          (delta : conjugateCosetSpace M) := by
    by_contra hno
    push_neg at hno
    have hpair : ∀ beta delta : FixedP, beta ≠ delta →
        ∃ t : N, IsInvolution t ∧ t • beta = delta := by
      intro beta delta hne
      obtain ⟨t, ht, htMove⟩ := hno beta delta hne
      exact ⟨t, ht, by
        apply Subtype.ext
        exact htMove⟩
    have hcardTwo := chapter1_rank_one_pair_involutions_card_eq_two
      hrank hEven hpair
    have hthree : 2 < Nat.card FixedP := hmax.1.2
    omega
  obtain ⟨betaP, deltaP, hbetaDeltaP, hbad⟩ := hbadPair
  let beta : conjugateCosetSpace M := betaP
  let delta : conjugateCosetSpace M := deltaP
  have hbeta : beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    betaP.property
  have hdelta : delta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    deltaP.property
  have hbetaDelta : beta ≠ delta := by
    intro h
    exact hbetaDeltaP (Subtype.ext h)
  let D : Subgroup X :=
    MulAction.stabilizer X beta ⊓ MulAction.stabilizer X delta
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hbeta x hxP),
      MulAction.mem_stabilizer_iff.mpr (hdelta x hxP)⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let R : Subgroup X := (S : Subgroup D).map D.subtype
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hRD : R ≤ D := by
    simpa [R] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hRsyl : theorem4bIsSylowSubgroupOf p R D := ⟨S, rfl⟩
  obtain ⟨t, ht, htNormR, htBeta, htDelta⟩ :=
    exists_involution_normalizing_of_sylow_twoPoint
      hM hp hbetaDelta hRsyl
  have hPRlt : P < R := by
    apply lt_of_le_of_ne hPR
    intro hEq
    have htNormP : t ∈ Subgroup.normalizer (P : Set X) := by
      rw [hEq]
      exact htNormR
    let tN : N := ⟨t, htNormP⟩
    have htN : IsInvolution tN := IsInvolution.subtype ht tN.property
    exact hbad tN htN htBeta
  have hRbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).1
  have hRdelta : delta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).2
  have hRcard : Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} = 2 := by
    apply Nat.le_antisymm
    · by_contra hle
      have hthree : 2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} := by
        omega
      have hRleP := hmax.2 ⟨hRp, hthree⟩ hPR
      exact (not_le_of_gt hPRlt) hRleP
    · let f : Fin 2 → {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) R} :=
        fun i => if i = 0 then ⟨beta, hRbeta⟩ else ⟨delta, hRdelta⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaDelta
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaDelta
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hPmod : Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P} ≡ 2 [MOD p] := by
    have hPcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hmax.1.1
    have hRcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hRp
    have h := hPcong.symm.trans hRcong
    rwa [hRcard] at h
  have hOmegaMod : Nat.card (conjugateCosetSpace M) ≡ 2 [MOD p] := by
    have hRcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hRp
    rwa [hRcard] at hRcong
  obtain ⟨A, hAp, hPA, hAR, hAN⟩ :=
    exists_larger_normalizer_pSubgroup hp hRp hPRlt
  let AN : Subgroup N := A.subgroupOf N
  have hANp : IsPGroup p AN :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨B, hANB⟩ := hANp.exists_le_sylow
  let BN : Subgroup N := (B : Subgroup N)
  let BX : Subgroup X := BN.map N.subtype
  have hABX : A ≤ BX := by
    intro a haA
    let aN : N := ⟨a, hAN haA⟩
    exact Subgroup.mem_map.mpr
      ⟨aN, hANB (show aN ∈ AN from haA), rfl⟩
  have hBXp : IsPGroup p BX := B.isPGroup'.map N.subtype
  have hfactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({sN} : Set N) = ⊤ :=
    PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      hrank hsN
  have hbotp : IsPGroup p (⊥ : Subgroup N) := IsPGroup.of_bot
  obtain ⟨S₀, _hbotS₀, hsNormS₀⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      hsN hp hpOdd hbotp (by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp) hfactor
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S₀ B
  have hBconj : (B : Subgroup N) =
      (S₀ : Subgroup N).conjBy (g : N) := by
    rw [← hg]
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.conjBy]
    congr 1
  let vN : N := rightConjugateElem sN (g : N)⁻¹
  have hvN : IsInvolution vN := isInvolution_rightConjugateElem hsN
  have hvNormBN : vN ∈ Subgroup.normalizer ((B : Subgroup N) : Set N) := by
    rw [hBconj]
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (Subgroup.zpowers_le.mpr hsNormS₀) (g : N)
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨sN, Subgroup.mem_zpowers sN, ?_⟩
    simp [vN, rightConjugateElem]
  let v : X := (vN : X)
  have hv : IsInvolution v :=
    IsInvolution.map_of_injective hvN N.subtype Subtype.val_injective
  have hvNormBX : v ∈ Subgroup.normalizer (BX : Set X) := by
    have hvMapMem : v ∈
        (Subgroup.normalizer ((B : Subgroup N) : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hvNormBN
    exact (Subgroup.le_normalizer_map (H := (B : Subgroup N)) N.subtype)
      hvMapMem
  let FixedB := {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) BX}
  have hBmod : Nat.card FixedB ≡ 2 [MOD p] := by
    have hBXcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hBXp
    exact hBXcong.symm.trans hOmegaMod
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    exact hpOdd.not_two_dvd_nat (dvd_refl 2)
  have hpGtTwo : 2 < p := by
    have hpTwo := hp.two_le
    omega
  have hBcardTwo : 2 ≤ Nat.card FixedB := by
    by_contra hnot
    have hlt : Nat.card FixedB < 2 := by omega
    change Nat.card FixedB % p = 2 % p at hBmod
    rw [Nat.mod_eq_of_lt (lt_trans hlt hpGtTwo),
      Nat.mod_eq_of_lt hpGtTwo] at hBmod
    omega
  letI : Nontrivial FixedB :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let lambda₀ : FixedB := Classical.choice inferInstance
  obtain ⟨eta₀, heta₀⟩ := exists_ne lambda₀
  have hexistsMoved : ∃ lambdaB : FixedB,
      v • (lambdaB : conjugateCosetSpace M) ≠ lambdaB := by
    by_cases hlambda₀ : v • (lambda₀ : conjugateCosetSpace M) = lambda₀
    · refine ⟨eta₀, ?_⟩
      intro hetaFix
      apply heta₀
      apply Subtype.ext
      exact (hM.involution_fixed_coset_unique hv).unique
        hetaFix hlambda₀
    · exact ⟨lambda₀, hlambda₀⟩
  obtain ⟨lambdaB, hlambdaMove⟩ := hexistsMoved
  let lambda : conjugateCosetSpace M := lambdaB
  let mu : conjugateCosetSpace M := v • lambda
  have hlambdaB : lambda ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) BX := lambdaB.property
  have hmuB : mu ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) BX :=
    fixedPoints_smul_of_mem_normalizer hvNormBX hlambdaB
  have hlambdaMu : lambda ≠ mu := by
    exact Ne.symm hlambdaMove
  have hvLambda : v • lambda = mu := rfl
  have hvMu : v • mu = lambda := by
    change v • (v • lambda) = lambda
    rw [← mul_smul, show v * v = 1 by
      simpa [pow_two] using hv.sq_eq_one]
    simp
  have hAcardThree : 3 ≤ Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) A} := by
    let FixedA := {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) A}
    let betaA : FixedA := ⟨beta, fun x hxA => hRbeta x (hAR hxA)⟩
    let deltaA : FixedA := ⟨delta, fun x hxA => hRdelta x (hAR hxA)⟩
    have hbetaDeltaA : betaA ≠ deltaA := by
      intro h
      apply hbetaDelta
      simpa [betaA, deltaA] using
        congrArg (fun z : FixedA =>
          (z : conjugateCosetSpace M)) h
    by_contra hnot
    have hnot' : ¬ 3 ≤ Nat.card FixedA := by
      simpa [FixedA] using hnot
    have hAcardLe : Nat.card FixedA ≤ 2 := by omega
    letI : Nontrivial FixedA := ⟨⟨betaA, deltaA, hbetaDeltaA⟩⟩
    have hAcardGtOne : 1 < Nat.card FixedA :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hAcard : Nat.card FixedA = 2 := by omega
    obtain ⟨otherA, _hotherA, hotherAUnique⟩ :=
      (Nat.card_eq_two_iff' betaA).mp hAcard
    have hdeltaOtherA : deltaA = otherA := by
      apply hotherAUnique deltaA
      exact Ne.symm hbetaDeltaA
    have hFixedAEq : ∀ omega : FixedA,
        omega = betaA ∨ omega = deltaA := by
      intro omega
      by_cases homega : omega = betaA
      · exact Or.inl homega
      · exact Or.inr ((hotherAUnique omega homega).trans
          hdeltaOtherA.symm)
    let lambdaA : FixedA := ⟨lambda, fun x hxA =>
      hlambdaB x (hABX hxA)⟩
    let muA : FixedA := ⟨mu, fun x hxA =>
      hmuB x (hABX hxA)⟩
    have hlambdaMuA : lambdaA ≠ muA := by
      intro h
      exact hlambdaMu (congrArg Subtype.val h)
    have hvBetaDelta : v • beta = delta := by
      rcases hFixedAEq lambdaA with hlambdaBetaA | hlambdaDeltaA
      · have hmuDeltaA : muA = deltaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaBetaA.trans hmuBetaA.symm
          · exact hmuDeltaA
        have hlambdaBeta : lambda = beta := by
          simpa [lambdaA, betaA] using
            congrArg (fun z : FixedA =>
              (z : conjugateCosetSpace M)) hlambdaBetaA
        have hmuDelta : mu = delta := by
          simpa [muA, deltaA] using
            congrArg (fun z : FixedA =>
              (z : conjugateCosetSpace M)) hmuDeltaA
        rw [← hlambdaBeta, hvLambda, hmuDelta]
      · have hmuBetaA : muA = betaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exact hmuBetaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaDeltaA.trans hmuDeltaA.symm
        have hlambdaDelta : lambda = delta := by
          simpa [lambdaA, deltaA] using
            congrArg (fun z : FixedA =>
              (z : conjugateCosetSpace M)) hlambdaDeltaA
        have hmuBeta : mu = beta := by
          simpa [muA, betaA] using
            congrArg (fun z : FixedA =>
              (z : conjugateCosetSpace M)) hmuBetaA
        rw [← hmuBeta, hvMu, hlambdaDelta]
    exact hbad vN hvN (by
      simpa [v] using hvBetaDelta)
  have hAleP := hmax.2 ⟨hAp, by omega⟩ hPA.le
  exact (not_le_of_gt hPA) hAleP

/-- Proposition 5.3(b): under ambient double transitivity, every fixed point
of the maximal `p`-subgroup is fixed by an involution in its normalizer. -/
public theorem proposition_5_3_normalizer_involution
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hmax : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q}) P)
    {gamma : conjugateCosetSpace M}
    (hgamma : gamma ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P) :
    ∃ s : X, s ∈ involutionsSet X ∧ IsInvolution s ∧
      s ∈ Subgroup.normalizer (P : Set X) ∧ s • gamma = gamma := by
  classical
  obtain ⟨s, hs, hsNorm⟩ :=
    lemma_5_1_normalizer_involution hM hp hpOdd hmax
  obtain ⟨alpha, hsAlpha⟩ :=
    (hM.involution_fixed_coset_unique hs).exists
  have halpha : alpha ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P :=
    proposition_5_3_fixes_involution_fixedPoint
      hM hp hpOdd hmax hs hsNorm hsAlpha
  have htwoNorm := chapter1_bender_normalizer_two_pretransitive
    hp htwo P hmax
  have htrans : IsTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) P) := by
    intro a b ha hb
    by_cases hab : a = b
    · exact ⟨1, by simp [hab]⟩
    obtain ⟨n, hn, _⟩ :=
      htwoNorm ha hb hb ha hab (Ne.symm hab)
    exact ⟨n, hn⟩
  exact normalizer_involution_at_of_transitive
    htrans hs hsNorm hsAlpha halpha hgamma

/-- The second branch of Theorem 2 for an odd prime.  The absence of a
two-fixed-point `p`-subgroup converts the source maximality-at-`beta`
hypothesis into maximality with at least two fixed points; Lemma 5.8 then
gives normalizer transitivity, and Proposition 5.3 supplies the involutions. -/
public theorem theorem_2_normalizer_of_no_exact_two
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hnoTwo : ¬ ∃ Q : Subgroup X,
      IsPGroup p Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2)
    (beta : conjugateCosetSpace M) (P : Subgroup X)
    (hPp : IsPGroup p P)
    (hPbeta : P ≤ MulAction.stabilizer X beta)
    (hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P))
    (hmaxThree : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X beta →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) →
      P ≤ Q → Q = P) :
    (∀ gamma delta : conjugateCosetSpace M,
      gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
      delta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
      ∃ n : Subgroup.normalizer (P : Set X),
        (n : X) • gamma = delta) ∧
      ∀ gamma : conjugateCosetSpace M,
        gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P →
        ∃ s : X, s ∈ involutionsSet X ∧ IsInvolution s ∧
          s ∈ Subgroup.normalizer (P : Set X) ∧ s • gamma = gamma := by
  classical
  have hPtwo : 2 ≤ Nat.card (theorem4bFixedPoints M P) := by omega
  have hmaxTwo : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X beta →
      2 ≤ Nat.card (theorem4bFixedPoints M Q) →
      P ≤ Q → Q = P := by
    intro Q hQp hQbeta hQtwo hPQ
    have hQneTwo : Nat.card (theorem4bFixedPoints M Q) ≠ 2 := by
      intro hQcard
      exact hnoTwo ⟨Q, hQp, hQcard⟩
    have hQthree : 3 ≤ Nat.card (theorem4bFixedPoints M Q) := by
      omega
    exact hmaxThree Q hQp hQbeta hQthree hPQ
  obtain ⟨htrans, hglobalTwo⟩ :=
    local_maximal_two_fixed_transitive_and_global
      hM hp hPp hPbeta hPtwo hmaxTwo
  have hglobalThree : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card (theorem4bFixedPoints M Q)) P := by
    refine ⟨⟨hPp, by omega⟩, ?_⟩
    intro Q hQgood hPQ
    have hQthreeDirect : 2 < Nat.card
        {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q} := by
      change 2 < Nat.card (theorem4bFixedPoints M Q)
      exact hQgood.2
    have hQtwoDirect : 1 < Nat.card
        {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q} := by
      omega
    exact hglobalTwo.2 ⟨hQgood.1, hQtwoDirect⟩ hPQ
  refine ⟨htrans, ?_⟩
  intro gamma hgamma
  obtain ⟨s, hs, hsNorm⟩ :=
    lemma_5_1_normalizer_involution hM hp hpOdd hglobalThree
  obtain ⟨alpha, hsAlpha⟩ :=
    (hM.involution_fixed_coset_unique hs).exists
  have halpha : alpha ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P :=
    proposition_5_3_fixes_involution_fixedPoint
      hM hp hpOdd hglobalThree hs hsNorm hsAlpha
  exact normalizer_involution_at_of_transitive
    htrans hs hsNorm hsAlpha halpha hgamma

/-- The exact-two-fixed-points branch of Theorem 2 for an odd prime. -/
public theorem theorem_2_two_pretransitive_of_exact_two
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hexact : ∃ P : Subgroup X,
      IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2) :
    MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra hnot2
  obtain ⟨z, Q, s, alpha, hzM, hz, hQp, hQthree,
      hs, hsNormQ, hQexact, hsAlpha, hQalpha⟩ :=
    corollary_5_7_normalized_fixedPoint_pair hM hp hpOdd hnot2
  let base : conjugateCosetSpace M := QuotientGroup.mk 1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X alpha base
  let Q' : Subgroup X := Q.conjBy g
  let s' : X := rightConjugateElem s g⁻¹
  have hs' : IsInvolution s' := isInvolution_rightConjugateElem hs
  have hs'Base : s' • base = base := by
    calc
      s' • base = s' • (g • alpha) := by rw [hg]
      _ = g • (s • alpha) := by
        simp [s', rightConjugateElem, mul_smul]
      _ = g • alpha := by rw [hsAlpha]
      _ = base := hg
  have hs'M : s' ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hs'Base
  have hQ'p : IsPGroup p Q' :=
    hQp.map (MulAut.conj g).toMonoidHom
  have hQ'card : Nat.card (theorem4bFixedPoints M Q') =
      Nat.card (theorem4bFixedPoints M Q) :=
    theorem4bFixedPoints_card_conjBy g
  have hQ'three : 3 ≤ Nat.card (theorem4bFixedPoints M Q') := by
    rw [hQ'card]
    exact hQthree
  have hQ'base : base ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) Q' := by
    have htransport :=
      (theorem4bFixedPointsConjByEquiv g
        (⟨alpha, hQalpha⟩ : theorem4bFixedPoints M Q)).property
    change ∀ x ∈ Q.conjBy g,
      x • (g • alpha) = g • alpha at htransport
    change ∀ x ∈ Q.conjBy g, x • base = base
    simpa only [hg] using htransport
  have hQ'M : Q' ≤ M := by
    rw [← baseCoset_stabilizer M]
    intro x hxQ'
    exact MulAction.mem_stabilizer_iff.mpr (hQ'base x hxQ')
  have hs'NormQ' : s' ∈ Subgroup.normalizer (Q' : Set X) := by
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (Subgroup.zpowers_le.mpr hsNormQ) g
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨s, Subgroup.mem_zpowers s, ?_⟩
    simp [s', rightConjugateElem, MulAut.conj_apply]
  have hInvConj : theorem4bInvertedCard s' Q' =
      theorem4bInvertedCard s Q := by
    have hcard := theorem4bInvertedCard_conjBy s g⁻¹ Q
    simpa [s', Q'] using hcard
  obtain ⟨t, ht, htM⟩ := hM.exists_involution_not_mem
  have hsIdx :=
    hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
      hs'M hs' ht htM
  have hzIdx :=
    hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
      hzM hz ht htM
  have hmEq : theorem4bM M s' = theorem4bM M z :=
    hsIdx.symm.trans hzIdx
  have hshare : theorem4bPrimeShare M s' p =
      theorem4bPrimeShare M z p := by
    simp [theorem4bPrimeShare, hmEq]
  have hQ'exact : theorem4bInvertedCard s' Q' =
      theorem4bPrimeShare M s' p := by
    rw [hInvConj, hQexact, hshare]
  obtain ⟨P, _hPp, hPcard, T, hTP⟩ :=
    exists_ambient_sylow_fixedPoints_card_two hp hpOdd hexact
  have hPpos : 0 < Nat.card (theorem4bFixedPoints M P) := by omega
  letI : Nonempty (theorem4bFixedPoints M P) :=
    (Nat.card_pos_iff.mp hPpos).1
  let betaP : theorem4bFixedPoints M P := Classical.choice inferInstance
  let beta : conjugateCosetSpace M := betaP
  have hPbeta : beta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) P := betaP.property
  let A : Subgroup X := MulAction.stabilizer X base
  have hQ'A : Q' ≤ A := by
    intro x hxQ'
    exact MulAction.mem_stabilizer_iff.mpr (hQ'base x hxQ')
  have hQ'Ap : IsPGroup p (Q'.subgroupOf A) :=
    hQ'p.of_equiv (Subgroup.subgroupOfEquivOfLe hQ'A).symm
  obtain ⟨Ralpha, hQ'Ralpha⟩ := hQ'Ap.exists_le_sylow
  let R : Subgroup X := (Ralpha : Subgroup A).map A.subtype
  have hQ'R : Q' ≤ R := by
    intro x hxQ'
    let xA : A := ⟨x, hQ'A hxQ'⟩
    exact Subgroup.mem_map.mpr
      ⟨xA, hQ'Ralpha (show xA ∈ Q'.subgroupOf A from hxQ'), rfl⟩
  have hRA : R ≤ A := by
    simpa [R] using Subgroup.map_le_range A.subtype (Ralpha : Subgroup A)
  have hRp : IsPGroup p R := Ralpha.isPGroup'.map A.subtype
  obtain ⟨hRcard, U, hUR⟩ :=
    fixedPoints_card_two_of_sylow_pointStabilizer
      hp T hTP hPbeta hPcard base
        (by simpa [A] using Ralpha)
  have hRbase : base ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRA hxR)
  let baseR : theorem4bFixedPoints M R := ⟨base, hRbase⟩
  obtain ⟨deltaR, hdeltaNe, hdeltaUnique⟩ :=
    (Nat.card_eq_two_iff' baseR).mp hRcard
  let delta : conjugateCosetSpace M := deltaR
  have hRdelta : delta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) R := deltaR.property
  have hbaseDelta : base ≠ delta := by
    intro h
    exact hdeltaNe (Subtype.ext h.symm)
  have hQ'delta : delta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) Q' := by
    intro x hxQ'
    exact hRdelta x (hQ'R hxQ')
  have hs'DeltaNe : s' • delta ≠ delta := by
    intro hfix
    exact hbaseDelta
      ((hM.involution_fixed_coset_unique hs').unique hs'Base hfix)
  have hs'DeltaNeBase : s' • delta ≠ base := by
    intro hEq
    apply hbaseDelta
    apply MulAction.injective s'
    exact hs'Base.trans hEq.symm
  have hQ'sdelta : s' • delta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) Q' :=
    fixedPoints_smul_of_mem_normalizer hs'NormQ' hQ'delta
  let D : Subgroup X := M ⊓ MulAction.stabilizer X delta
  let E : Subgroup X := D ⊓ MulAction.stabilizer X (s' • delta)
  have hdeltaBase : delta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    simpa [base] using hbaseDelta.symm
  have hQ'E : Q' ≤ E := by
    intro x hxQ'
    exact ⟨⟨hQ'M hxQ',
      MulAction.mem_stabilizer_iff.mpr (hQ'delta x hxQ')⟩,
      MulAction.mem_stabilizer_iff.mpr (hQ'sdelta x hxQ')⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.base_inf_stabilizer_card_odd hdeltaBase
  have hEodd : Odd (Nat.card E) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le inf_le_left)
  have hs'NormE : s' ∈ Subgroup.normalizer (E : Set X) := by
    simpa [E, D] using
      theorem4b_mem_normalizer_tripleStabilizer hs' hs'M
  obtain ⟨W, hWSylowE, hQ'W, hs'NormW⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hEodd hs' hs'NormE hp hQ'p hQ'E hs'NormQ'
  have hWE : W ≤ E := by
    rcases hWSylowE with ⟨We, hWeq⟩
    rw [hWeq]
    simpa using Subgroup.map_le_range E.subtype (We : Subgroup E)
  have hWp : IsPGroup p W := by
    rcases hWSylowE with ⟨We, hWeq⟩
    rw [hWeq]
    exact We.isPGroup'.map E.subtype
  have hWD : W ≤ D := hWE.trans inf_le_left
  have hWupper : theorem4bInvertedCard s' W ≤
      theorem4bPrimeShare M s' p :=
    hM.theorem4b_invertedCard_le_primeShare_of_stabilizer
      hs'M hs' hp hdeltaBase hWp hWD hs'NormW
  have hWexact : theorem4bInvertedCard s' W =
      theorem4bPrimeShare M s' p := by
    apply Nat.le_antisymm hWupper
    exact hQ'exact.symm.trans_le (theorem4bInvertedCard_mono hQ'W)
  have h38c :=
    (hM.theorem4b_proposition38cAtBase
      s' p delta hs' hs'M hp hdeltaBase).2
      ⟨W, hWp, hWD, hs'NormW, hWexact⟩
  obtain ⟨V, hVSylowD, hs'NormV⟩ := h38c
  have hRM : R ≤ M := by
    simpa [A, base, baseCoset_stabilizer] using hRA
  have hRD : R ≤ D := by
    intro x hxR
    exact ⟨hRM hxR,
      MulAction.mem_stabilizer_iff.mpr (hRdelta x hxR)⟩
  have hRSylowD : theorem4bIsSylowSubgroupOf p R D := by
    have hUR' : (U : Subgroup X) = R := by
      simpa [R] using hUR
    let UD : Sylow p D := U.subtype (by
      rw [hUR']
      exact hRD)
    refine ⟨UD, ?_⟩
    rw [show (UD : Subgroup D) = R.subgroupOf D by
      simp [UD, hUR']]
    exact (Subgroup.map_subgroupOf_eq_of_le (G := X) hRD).symm
  have hVp : IsPGroup p V := by
    rcases hVSylowD with ⟨Vd, hVeq⟩
    rw [hVeq]
    exact Vd.isPGroup'.map D.subtype
  have hVD : V ≤ D := by
    rcases hVSylowD with ⟨Vd, hVeq⟩
    rw [hVeq]
    simpa using Subgroup.map_le_range D.subtype (Vd : Subgroup D)
  have hVRcard : Nat.card V = Nat.card R := by
    rcases hVSylowD with ⟨Vd, hVeq⟩
    rcases hRSylowD with ⟨Rd, hReq⟩
    rw [hVeq, hReq,
      Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.card_map_of_injective D.subtype_injective,
      Sylow.card_eq_multiplicity Vd, Sylow.card_eq_multiplicity Rd]
  obtain ⟨UV, hVUV⟩ := hVp.exists_le_sylow
  have hUVUcard : Nat.card (UV : Subgroup X) = Nat.card (U : Subgroup X) := by
    rw [Sylow.card_eq_multiplicity UV, Sylow.card_eq_multiplicity U]
  have hVUVeq : V = (UV : Subgroup X) := by
    apply Subgroup.eq_of_le_of_card_ge hVUV
    rw [hUVUcard, hUR, hVRcard]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X T UV
  have hUVeq : (UV : Subgroup X) = P.conjBy k := by
    calc
      (UV : Subgroup X) = ((k • T : Sylow p X) : Subgroup X) := by rw [hk]
      _ = (T : Subgroup X).conjBy k := by
        simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
      _ = P.conjBy k := by rw [hTP]
  have hVcard : Nat.card (theorem4bFixedPoints M V) = 2 := by
    calc
      Nat.card (theorem4bFixedPoints M V) =
          Nat.card (theorem4bFixedPoints M (UV : Subgroup X)) := by
            rw [hVUVeq]
      _ = Nat.card (theorem4bFixedPoints M (P.conjBy k)) := by rw [hUVeq]
      _ = Nat.card (theorem4bFixedPoints M P) :=
        theorem4bFixedPoints_card_conjBy k
      _ = 2 := hPcard
  have hVbase : base ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) V := by
    intro x hxV
    apply MulAction.mem_stabilizer_iff.mp
    simpa [base, baseCoset_stabilizer] using (hVD hxV).1
  have hVdelta : delta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) V := by
    intro x hxV
    exact MulAction.mem_stabilizer_iff.mp (hVD hxV).2
  have hVsdelta : s' • delta ∈ fixedPointsOfSubgroup X
      (conjugateCosetSpace M) V :=
    fixedPoints_smul_of_mem_normalizer hs'NormV hVdelta
  let baseV : theorem4bFixedPoints M V := ⟨base, hVbase⟩
  let deltaV : theorem4bFixedPoints M V := ⟨delta, hVdelta⟩
  let sdeltaV : theorem4bFixedPoints M V := ⟨s' • delta, hVsdelta⟩
  obtain ⟨otherV, _hotherV, hotherUnique⟩ :=
    (Nat.card_eq_two_iff' baseV).mp hVcard
  have hdeltaOther : deltaV = otherV := by
    apply hotherUnique deltaV
    intro h
    exact hbaseDelta (congrArg Subtype.val h).symm
  have hsdeltaOther : sdeltaV = otherV := by
    apply hotherUnique sdeltaV
    intro h
    exact hs'DeltaNeBase (congrArg Subtype.val h)
  have hsdeltaEq : s' • delta = delta := by
    exact congrArg Subtype.val (hsdeltaOther.trans hdeltaOther.symm)
  exact hs'DeltaNe hsdeltaEq

/-- A `2`-subgroup fixing two conjugate cosets is trivial.  Otherwise its
even order supplies an involution fixing both cosets, contrary to strong
embedding. -/
private theorem eq_bot_of_isPGroup_two_of_two_le_fixedPoints
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hPp : IsPGroup 2 P)
    (hPtwo : 2 ≤ Nat.card (theorem4bFixedPoints M P)) :
    P = ⊥ := by
  classical
  by_contra hPne
  have htwoDvd : 2 ∣ Nat.card P := by
    rcases hPp.card_eq_or_dvd with hcard | hdvd
    · exact (hPne (Subgroup.card_eq_one.mp hcard)).elim
    · exact hdvd
  obtain ⟨u, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := P) 2 htwoDvd
  have huP : IsInvolution u :=
    (orderOf_eq_prime_iff.mp huOrder).symm
  have hu : IsInvolution (u : X) := by
    constructor
    · intro huOne
      exact huP.ne_one (Subtype.ext huOne)
    · exact congrArg Subtype.val huP.sq_eq_one
  letI : Nontrivial (theorem4bFixedPoints M P) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨alpha, beta, hab⟩ :=
    exists_pair_ne (theorem4bFixedPoints M P)
  apply hab
  apply Subtype.ext
  exact (hM.involution_fixed_coset_unique hu).unique
    (alpha.property u u.property) (beta.property u u.property)

/-- A transitive action on a two-element type is doubly transitive. -/
private theorem isMultiplyPretransitive_two_of_card_eq_two
    {G Omega : Type*} [Group G] [MulAction G Omega] [Finite Omega]
    (htrans : MulAction.IsPretransitive G Omega)
    (hcard : Nat.card Omega = 2) :
    MulAction.IsMultiplyPretransitive G Omega 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq a c
  obtain ⟨other, _hother, hotherUnique⟩ :=
    (Nat.card_eq_two_iff' c).mp hcard
  refine ⟨g, hg, ?_⟩
  have hgb : g • b ≠ c := by
    intro h
    apply hab
    apply MulAction.injective g
    exact hg.trans h.symm
  exact (hotherUnique (g • b) hgb).trans
    (hotherUnique d hcd.symm).symm

/-- The full Theorem 2 interface used by Proposition 6.3 and Section 8.
The source odd-prime theorem handles `p ≠ 2`; the two-prime case follows
directly from uniqueness of fixed cosets for involutions. -/
public theorem IsStronglyEmbedded.theorem4bProposition63Theorem2
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) :
    Theorem4bProposition63Theorem2 M (involutionsSet X) := by
  classical
  intro p hp
  by_cases hpTwo : p = 2
  · subst p
    constructor
    · rintro ⟨P, hPp, hPcard⟩
      have hPbot := eq_bot_of_isPGroup_two_of_two_le_fixedPoints
        hM hPp (by omega)
      have hOmegaCard : Nat.card (conjugateCosetSpace M) = 2 := by
        simpa [hPbot, fixedPointsOfSubgroup] using hPcard
      exact isMultiplyPretransitive_two_of_card_eq_two
        (conjugateCosetSpace_isPretransitive M) hOmegaCard
    · intro _hnoTwo beta P hPp _hPbeta hPthree _hmax
      have hPbot := eq_bot_of_isPGroup_two_of_two_le_fixedPoints
        hM hPp (by omega)
      constructor
      · intro gamma delta _hgamma _hdelta
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X gamma delta
        refine ⟨⟨g, ?_⟩, hg⟩
        rw [hPbot, Subgroup.mem_normalizer_iff]
        intro x
        simp
      · intro gamma _hgamma
        obtain ⟨z, hzM, hz⟩ := hM.exists_involution
        let base : conjugateCosetSpace M := QuotientGroup.mk 1
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X base gamma
        let s : X := rightConjugateElem z g⁻¹
        have hs : IsInvolution s := isInvolution_rightConjugateElem hz
        have hzBase : z • base = base := by
          apply MulAction.mem_stabilizer_iff.mp
          simpa [base, baseCoset_stabilizer] using hzM
        refine ⟨s, ?_, hs, ?_, ?_⟩
        · exact hs
        · rw [hPbot, Subgroup.mem_normalizer_iff]
          intro x
          simp
        · calc
            s • gamma = s • (g • base) := by rw [hg]
            _ = g • (z • base) := by
              simp [s, rightConjugateElem, mul_smul]
            _ = g • base := by rw [hzBase]
            _ = gamma := hg
  · have hpOdd : Odd p := hp.odd_of_ne_two hpTwo
    exact ⟨theorem_2_two_pretransitive_of_exact_two hM hp hpOdd,
      theorem_2_normalizer_of_no_exact_two hM hp hpOdd⟩

end CFSG.BenderSuzuki
