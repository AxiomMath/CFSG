module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary713
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# The local normalizer step in Proposition 8.2

This file isolates the chosen-point normalizer argument in Proposition 8.2.
The source's nonsolvable branch invokes `[II4; 3.3]`; the reusable content
needed here is that a normal `2`-subgroup acting regularly away from the
chosen point has a nontrivial centralizer on every subgroup fixing two
further points.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u v

/-- The regular-root core of the `[II4; 3.3]` application in Proposition
8.2.  If a `2`-subgroup `S`, normalized by `P`, acts regularly away from
`alpha`, and `P` fixes at least three points including `alpha`, then `S`
contains an involution centralizing `P`.

The proof chooses two further `P`-fixed points.  Their unique transporter in
`S` is fixed by conjugation by `P`, so `C_S(P)` is nontrivial.  Since it is a
`2`-group, Cauchy's theorem supplies an involution. -/
public theorem exists_involution_centralizing_of_regular_twoSubgroup
    {X : Type u} {Omega : Type v} [Group X] [Finite X]
    [MulAction X Omega] [Finite Omega]
    {S P : Subgroup X} {alpha : Omega}
    (hS2 : IsPGroup 2 S)
    (hPNormS : P ≤ Subgroup.normalizer (S : Set X))
    (hregular : IsRegularOn S {omega : Omega | omega ≠ alpha})
    (halpha : alpha ∈ fixedPointsOfSubgroup X Omega P)
    (hthree : 3 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega P}) :
    ∃ u : X, u ∈ S ∧ IsInvolution u ∧
      P ≤ Subgroup.centralizer ({u} : Set X) := by
  classical
  let FixedP := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega P}
  let alphaP : FixedP := ⟨alpha, halpha⟩
  have hthreeFixed : 3 ≤ Nat.card FixedP := by
    simpa [FixedP] using hthree
  have hnontrivial : Nontrivial FixedP :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial FixedP := hnontrivial
  obtain ⟨betaP, hbetaAlpha⟩ := exists_ne alphaP
  have hthreeCardinal : (3 : Cardinal) ≤ Cardinal.mk FixedP := by
    rw [← Nat.cast_card]
    exact_mod_cast hthreeFixed
  obtain ⟨gammaP, hgammaAlpha, hgammaBeta⟩ :=
    Cardinal.exists_ne_ne_of_three_le hthreeCardinal alphaP betaP
  let beta : Omega := betaP
  let gamma : Omega := gammaP
  have hbeta : beta ∈ fixedPointsOfSubgroup X Omega P := betaP.property
  have hgamma : gamma ∈ fixedPointsOfSubgroup X Omega P := gammaP.property
  have hbetaNeAlpha : beta ≠ alpha := by
    intro h
    apply hbetaAlpha
    apply Subtype.ext
    exact h
  have hgammaNeAlpha : gamma ≠ alpha := by
    intro h
    apply hgammaAlpha
    apply Subtype.ext
    exact h
  have hbetaGamma : beta ≠ gamma := by
    intro h
    apply hgammaBeta
    apply Subtype.ext
    exact h.symm
  obtain ⟨s, hsMove, hsUnique⟩ :=
    hregular hbetaNeAlpha hgammaNeAlpha
  have hsNeOne : s ≠ 1 := by
    intro hs
    have hmove : beta = gamma := by
      simpa [hs] using hsMove
    exact hbetaGamma hmove
  have hsCentral : (s : X) ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hpNorm : p ∈ Subgroup.normalizer (S : Set X) := hPNormS hpP
    have hconjS : p * (s : X) * p⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hpNorm (s : X)).mp s.property
    let sp : S := ⟨p * (s : X) * p⁻¹, hconjS⟩
    have hpBeta : p • beta = beta := hbeta p hpP
    have hpGamma : p • gamma = gamma := hgamma p hpP
    have hpInvBeta : p⁻¹ • beta = beta := by
      calc
        p⁻¹ • beta = p⁻¹ • (p • beta) := by rw [hpBeta]
        _ = beta := inv_smul_smul p beta
    have hspMove : (sp : X) • beta = gamma := by
      calc
        (sp : X) • beta = p • ((s : X) • (p⁻¹ • beta)) := by
          simp [sp, mul_smul, mul_assoc]
        _ = p • ((s : X) • beta) := by rw [hpInvBeta]
        _ = p • gamma := by rw [hsMove]
        _ = gamma := hpGamma
    have hspEq : sp = s := hsUnique sp hspMove
    have hconjEq : p * (s : X) * p⁻¹ = (s : X) :=
      congrArg Subtype.val hspEq
    calc
      p * (s : X) = (p * (s : X) * p⁻¹) * p := by group
      _ = (s : X) * p := by rw [hconjEq]
  let C : Subgroup S :=
    (Subgroup.centralizer (P : Set X)).comap S.subtype
  have hsC : s ∈ C := hsCentral
  have hCnontrivial : Nontrivial C := by
    refine ⟨⟨⟨s, hsC⟩, 1, ?_⟩⟩
    intro h
    apply hsNeOne
    exact congrArg Subtype.val h
  have hC2 : IsPGroup 2 C := hS2.to_subgroup C
  have htwoCard : 2 ∣ Nat.card C := by
    rcases (IsPGroup.nontrivial_iff_card
      (p := 2) (G := C) hC2).mp hCnontrivial with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨uC, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 htwoCard
  let u : X := ((uC : C) : S)
  have huOrderS : orderOf ((uC : C) : S) = 2 :=
    (Subgroup.orderOf_coe uC).trans huOrder
  have huOrderX : orderOf u = 2 := by
    simpa [u] using
      (Subgroup.orderOf_coe ((uC : C) : S)).trans huOrderS
  have huData := orderOf_eq_prime_iff.mp huOrderX
  have hu : IsInvolution u := ⟨huData.2, huData.1⟩
  refine ⟨u, ((uC : C) : S).property, hu, ?_⟩
  intro p hpP
  have huCentral : u ∈ Subgroup.centralizer (P : Set X) :=
    (uC : C).property
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp huCentral p hpP)

/-- Fixed-pair form of the regular-root argument on an arbitrary invariant
carrier.  This is convenient when regularity is known only on one orbit: the
caller can provide two fixed points in that carrier directly, without
comparing the orbit's cardinality with the ambient fixed-point type. -/
public theorem exists_involution_centralizing_of_regular_twoSubgroup_fixedPair
    {X : Type u} {Omega : Type v} [Group X] [Finite X]
    [MulAction X Omega]
    {S P : Subgroup X} {A : Set Omega} {beta gamma : Omega}
    (hS2 : IsPGroup 2 S)
    (hPNormS : P ≤ Subgroup.normalizer (S : Set X))
    (hregular : IsRegularOn S A)
    (hbeta : beta ∈ fixedPointsOfSubgroup X Omega P)
    (hgamma : gamma ∈ fixedPointsOfSubgroup X Omega P)
    (hbetaA : beta ∈ A)
    (hgammaA : gamma ∈ A)
    (hbetaGamma : beta ≠ gamma) :
    ∃ u : X, u ∈ S ∧ IsInvolution u ∧
      P ≤ Subgroup.centralizer ({u} : Set X) := by
  classical
  obtain ⟨s, hsMove, hsUnique⟩ :=
    hregular hbetaA hgammaA
  have hsNeOne : s ≠ 1 := by
    intro hs
    have hmove : beta = gamma := by
      simpa [hs] using hsMove
    exact hbetaGamma hmove
  have hsCentral : (s : X) ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hpNorm : p ∈ Subgroup.normalizer (S : Set X) := hPNormS hpP
    have hconjS : p * (s : X) * p⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hpNorm (s : X)).mp s.property
    let sp : S := ⟨p * (s : X) * p⁻¹, hconjS⟩
    have hpBeta : p • beta = beta := hbeta p hpP
    have hpGamma : p • gamma = gamma := hgamma p hpP
    have hpInvBeta : p⁻¹ • beta = beta := by
      calc
        p⁻¹ • beta = p⁻¹ • (p • beta) := by rw [hpBeta]
        _ = beta := inv_smul_smul p beta
    have hspMove : (sp : X) • beta = gamma := by
      calc
        (sp : X) • beta = p • ((s : X) • (p⁻¹ • beta)) := by
          simp [sp, mul_smul, mul_assoc]
        _ = p • ((s : X) • beta) := by rw [hpInvBeta]
        _ = p • gamma := by rw [hsMove]
        _ = gamma := hpGamma
    have hspEq : sp = s := hsUnique sp hspMove
    have hconjEq : p * (s : X) * p⁻¹ = (s : X) :=
      congrArg Subtype.val hspEq
    calc
      p * (s : X) = (p * (s : X) * p⁻¹) * p := by group
      _ = (s : X) * p := by rw [hconjEq]
  let C : Subgroup S :=
    (Subgroup.centralizer (P : Set X)).comap S.subtype
  have hsC : s ∈ C := hsCentral
  have hCnontrivial : Nontrivial C := by
    refine ⟨⟨⟨s, hsC⟩, 1, ?_⟩⟩
    intro h
    apply hsNeOne
    exact congrArg Subtype.val h
  have hC2 : IsPGroup 2 C := hS2.to_subgroup C
  have htwoCard : 2 ∣ Nat.card C := by
    rcases (IsPGroup.nontrivial_iff_card
      (p := 2) (G := C) hC2).mp hCnontrivial with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨uC, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 htwoCard
  let u : X := ((uC : C) : S)
  have huOrderS : orderOf ((uC : C) : S) = 2 :=
    (Subgroup.orderOf_coe uC).trans huOrder
  have huOrderX : orderOf u = 2 := by
    simpa [u] using
      (Subgroup.orderOf_coe ((uC : C) : S)).trans huOrderS
  have huData := orderOf_eq_prime_iff.mp huOrderX
  have hu : IsInvolution u := ⟨huData.2, huData.1⟩
  refine ⟨u, ((uC : C) : S).property, hu, ?_⟩
  intro p hpP
  have huCentral : u ∈ Subgroup.centralizer (P : Set X) :=
    (uC : C).property
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp huCentral p hpP)

/-- If the regular `2`-subgroup lies in the chosen point stabilizer, the
involution produced above is already an element of the local normalizer
`N_{X_alpha}(P)`. -/
public theorem exists_local_normalizer_involution_of_regular_twoSubgroup
    {X : Type u} {Omega : Type v} [Group X] [Finite X]
    [MulAction X Omega] [Finite Omega]
    {S P : Subgroup X} {alpha : Omega}
    (hS2 : IsPGroup 2 S)
    (hSalpha : S ≤ MulAction.stabilizer X alpha)
    (hPNormS : P ≤ Subgroup.normalizer (S : Set X))
    (hregular : IsRegularOn S {omega : Omega | omega ≠ alpha})
    (halpha : alpha ∈ fixedPointsOfSubgroup X Omega P)
    (hthree : 3 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega P}) :
    ∃ u : X, u ∈ MulAction.stabilizer X alpha ∧
      IsInvolution u ∧ u ∈ Subgroup.normalizer (P : Set X) := by
  obtain ⟨u, huS, hu, huCentral⟩ :=
    exists_involution_centralizing_of_regular_twoSubgroup
      hS2 hPNormS hregular halpha hthree
  refine ⟨u, hSalpha huS, hu, ?_⟩
  exact centralizer_le_normalizer P
    (show u ∈ Subgroup.centralizer (P : Set X) by
      rw [Subgroup.mem_centralizer_iff]
      intro p hpP
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (huCentral hpP))

/-- The no-exact-two branch of the completed Theorem 2 already has precisely
the chosen-point maximality needed in Proposition 8.2. -/
public theorem exists_local_normalizer_involution_of_theorem2_no_exact_two
    {X : Type u} [Group X] [Finite X] {M P : Subgroup X}
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    {p : ℕ} (hp : Nat.Prime p)
    (hnoTwo : ¬ ∃ Q : Subgroup X,
      IsPGroup p Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2)
    (beta : conjugateCosetSpace M)
    (hPp : IsPGroup p P)
    (hPbeta : P ≤ MulAction.stabilizer X beta)
    (hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P))
    (hmax : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X beta →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) →
      P ≤ Q → Q = P) :
    ∃ u : X, u ∈ MulAction.stabilizer X beta ∧
      IsInvolution u ∧ u ∈ Subgroup.normalizer (P : Set X) := by
  obtain ⟨_trans, hinvolution⟩ :=
    (hT2 p hp).2 hnoTwo beta P hPp hPbeta hPthree hmax
  obtain ⟨u, _huSet, hu, huNorm, huBeta⟩ :=
    hinvolution beta (fun x hxP =>
      MulAction.mem_stabilizer_iff.mp (hPbeta hxP))
  exact ⟨u, MulAction.mem_stabilizer_iff.mpr huBeta, hu, huNorm⟩

/-- In the exact-two branch, maximality is chosen while retaining the point
`gamma`.  The selected-point Bender normalizer argument first makes
`N_X(P) \cap X_gamma` transitive on the other fixed points.  Normalizer growth
then upgrades this local maximality to the global hypothesis of Proposition
5.3, without assuming that an arbitrary overgroup of `P` still fixes
`gamma`. -/
public theorem exists_local_normalizer_involution_of_maximal_containing
    {X : Type u} [Group X] [Finite X] {M R P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    {gamma : conjugateCosetSpace M}
    (hmaxContainR : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧ R ≤ Q ∧
        Q ≤ MulAction.stabilizer X gamma ∧
          3 ≤ Nat.card (theorem4bFixedPoints M Q)) P) :
    ∃ s : X, s ∈ MulAction.stabilizer X gamma ∧
      IsInvolution s ∧ s ∈ Subgroup.normalizer (P : Set X) := by
  classical
  let Omega := conjugateCosetSpace M
  have hmaxLocal : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧ Q ≤ MulAction.stabilizer X gamma ∧
        2 < Nat.card (theorem4bFixedPoints M Q)) P := by
    refine ⟨⟨hmaxContainR.1.1, hmaxContainR.1.2.2.1,
      lt_of_lt_of_le (by decide) hmaxContainR.1.2.2.2⟩, ?_⟩
    intro Q hQ hPQ
    exact hmaxContainR.2
      ⟨hQ.1, hmaxContainR.1.2.1.trans hPQ, hQ.2.1, by
        omega⟩ hPQ
  have hgamma : gamma ∈ fixedPointsOfSubgroup X Omega P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hmaxLocal.1.2.1 hxP)
  have htransLocal : IsTransitiveOn
      (Subgroup.normalizer (P : Set X) ⊓
        MulAction.stabilizer X gamma)
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup X Omega P ∧ omega ≠ gamma} :=
    chapter1_bender_normalizer_pointStabilizer_pretransitive_of_local
      hp htwo P hmaxLocal
  have hmaxGlobal : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card (theorem4bFixedPoints M Q)) P := by
    refine ⟨⟨hmaxLocal.1.1, hmaxLocal.1.2.2⟩, ?_⟩
    intro Q hQ hPQ
    by_cases hQP : Q ≤ P
    · exact hQP
    have hQPne : Q ≠ P := by
      intro h
      apply hQP
      rw [h]
    have hPQlt : P < Q := lt_of_le_of_ne hPQ hQPne.symm
    obtain ⟨A, hAp, hPA, hAQ, hAN⟩ :=
      exists_larger_normalizer_pSubgroup hp hQ.1 hPQlt
    let FixedQ := theorem4bFixedPoints M Q
    let FixedA := theorem4bFixedPoints M A
    let fixedQToA : FixedQ → FixedA := fun omega =>
      ⟨(omega : Omega), fun x hxA => omega.property x (hAQ hxA)⟩
    have hfixedQToA : Function.Injective fixedQToA := by
      intro a b hab
      apply Subtype.ext
      change (a : Omega) = (b : Omega)
      exact congrArg (fun z : FixedA => (z : Omega)) hab
    have hAcard : 2 < Nat.card FixedA :=
      hQ.2.trans_le (Nat.card_le_card_of_injective
        fixedQToA hfixedQToA)
    by_cases hAstab : A ≤ MulAction.stabilizer X gamma
    · have hAleP : A ≤ P := hmaxLocal.2
        ⟨hAp, hAstab, by simpa [FixedA] using hAcard⟩ hPA.le
      exact (not_le_of_gt hPA hAleP).elim
    obtain ⟨r, hrA, hrMove⟩ := SetLike.not_le_iff_exists.mp hAstab
    let delta : Omega := r • gamma
    have hrNorm : r ∈ Subgroup.normalizer (P : Set X) := hAN hrA
    have hdelta : delta ∈ fixedPointsOfSubgroup X Omega P :=
      fixedPoints_smul_of_mem_normalizer hrNorm hgamma
    have hdeltaGamma : delta ≠ gamma := by
      intro h
      apply hrMove
      exact MulAction.mem_stabilizer_iff.mpr h
    have hFixedQpos : 0 < Nat.card FixedQ := lt_trans (by decide) hQ.2
    letI : Nonempty FixedQ := (Nat.card_pos_iff.mp hFixedQpos).1
    let betaQ : FixedQ := Classical.choice inferInstance
    let beta : Omega := betaQ
    have hbetaQ : beta ∈ fixedPointsOfSubgroup X Omega Q :=
      betaQ.property
    have hbetaP : beta ∈ fixedPointsOfSubgroup X Omega P := by
      intro x hxP
      exact hbetaQ x (hPQ hxP)
    by_cases hbetaGamma : beta = gamma
    · have hQstab : Q ≤ MulAction.stabilizer X gamma := by
        intro x hxQ
        apply MulAction.mem_stabilizer_iff.mpr
        simpa [hbetaGamma] using hbetaQ x hxQ
      exact hmaxLocal.2 ⟨hQ.1, hQstab, hQ.2⟩ hPQ
    obtain ⟨n₀, hn₀⟩ := htransLocal
      ⟨hbetaP, hbetaGamma⟩ ⟨hdelta, hdeltaGamma⟩
    let n : X := r⁻¹ * (n₀ : X)
    have hnNorm : n ∈ Subgroup.normalizer (P : Set X) := by
      exact (Subgroup.normalizer (P : Set X)).mul_mem
        ((Subgroup.normalizer (P : Set X)).inv_mem hrNorm)
        n₀.property.1
    have hnBeta : n • beta = gamma := by
      simp [n, delta, mul_smul, hn₀]
    let Qn : Subgroup X := Q.conjBy n
    have hQnp : IsPGroup p Qn :=
      hQ.1.map (MulAut.conj n).toMonoidHom
    have hPconj : P.conjBy n = P :=
      section11_conjBy_eq_of_mem_normalizer hnNorm
    have hPQn : P ≤ Qn := by
      rw [← hPconj]
      exact Subgroup.map_mono hPQ
    have hnInvGamma : n⁻¹ • gamma = beta := by
      rw [← hnBeta]
      exact inv_smul_smul n beta
    have hQnStab : Qn ≤ MulAction.stabilizer X gamma := by
      intro x hxQn
      change x ∈ Q.conjBy n at hxQn
      rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
      rcases hxQn with ⟨y, hyQ, rfl⟩
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        (n * y * n⁻¹) • gamma = n • (y • (n⁻¹ • gamma)) := by
          simp [mul_smul, mul_assoc]
        _ = n • (y • beta) := by rw [hnInvGamma]
        _ = n • beta := by rw [hbetaQ y hyQ]
        _ = gamma := hnBeta
    let FixedQn := theorem4bFixedPoints M Qn
    let fixedQToQn : FixedQ → FixedQn := fun omega =>
      ⟨n • (omega : Omega), by
        intro x hxQn
        change x ∈ Q.conjBy n at hxQn
        rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
        rcases hxQn with ⟨y, hyQ, rfl⟩
        calc
          (n * y * n⁻¹) • (n • (omega : Omega)) =
              n • (y • (omega : Omega)) := by
            simp [mul_smul, mul_assoc]
          _ = n • (omega : Omega) := by
            rw [omega.property y hyQ]⟩
    have hfixedQToQn : Function.Injective fixedQToQn := by
      intro a b hab
      apply Subtype.ext
      apply MulAction.injective n
      exact congrArg Subtype.val hab
    have hQnCard : 2 < Nat.card FixedQn :=
      hQ.2.trans_le (Nat.card_le_card_of_injective
        fixedQToQn hfixedQToQn)
    have hQnleP : Qn ≤ P := hmaxLocal.2
      ⟨hQnp, hQnStab, by simpa [FixedQn] using hQnCard⟩ hPQn
    have hQnP : Qn = P := le_antisymm hQnleP hPQn
    have hnInvNorm : n⁻¹ ∈ Subgroup.normalizer (P : Set X) :=
      (Subgroup.normalizer (P : Set X)).inv_mem hnNorm
    have hQP' : Q = P := by
      calc
        Q = (Q.conjBy n).conjBy n⁻¹ :=
          (Subgroup.conjBy_inv Q n).symm
        _ = P.conjBy n⁻¹ := by
          rw [show Q.conjBy n = P by simpa [Qn] using hQnP]
        _ = P := section11_conjBy_eq_of_mem_normalizer hnInvNorm
    rw [hQP']
  obtain ⟨s, _hsSet, hs, hsNorm, hsGamma⟩ :=
    proposition_5_3_normalizer_involution
      hM hp hpOdd htwo hmaxGlobal hgamma
  exact ⟨s, MulAction.mem_stabilizer_iff.mpr hsGamma, hs, hsNorm⟩

/-- The normal regular Sylow-`2` subgroup supplied by the nonsolvable branch
of Corollary 7.13 and its retained Borel witness.  The subgroup is normal in
`F ∩ M`, not merely in `F° ∩ M`; this is the normality needed for a
chosen odd-prime subgroup of the full point stabilizer to normalize it. -/
public theorem corollary713_nonsolvable_exists_normal_twoSubgroup_regular
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) (hM : IsStronglyEmbedded M)
    {u : X} (huFM : u ∈ F ⊓ M) (hu : IsInvolution u)
    (hnotle : ¬ involutionCoreIn F ≤ M)
    (hnonsolvable : Corollary713NonsolvableConclusion M F)
    (hBorel : IsBorelSubgroup
      (((M ⊓ involutionCoreIn F).subgroupOf
          (involutionCoreIn F)).map
        (QuotientGroup.mk'
          (twoPrimeCore (involutionCoreIn F))))) :
    ∃ S : Subgroup X,
      IsPGroup 2 S ∧
        S ≤ F ⊓ M ∧
          (S.subgroupOf (F ⊓ M)).Normal ∧
          IsRegularOn S
            {omega : conjugateCosetSpace M |
              InOrbit F (QuotientGroup.mk 1) omega ∧
                omega ≠ QuotientGroup.mk 1} := by
  classical
  let F0 : Subgroup X := involutionCoreIn F
  let K : Subgroup F0 := twoPrimeCore F0
  let H0 : Subgroup X := M ⊓ F0
  let H : Subgroup F0 := H0.subgroupOf F0
  let q : F0 →* (F0 ⧸ K) := QuotientGroup.mk' K
  let B : Subgroup (F0 ⧸ K) := H.map q
  dsimp [Corollary713NonsolvableConclusion] at hnonsolvable
  rcases hnonsolvable with ⟨hcore, hmodel, htwo, hfactor⟩
  have huF0 : u ∈ F0 := by
    exact involution_mem_involutionCoreIn huFM.1 hu
  let u0 : F0 := ⟨u, huF0⟩
  have hcoreM : K.map F0.subtype ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hkK, rfl⟩
    have hkCenter : k ∈ Subgroup.center F0 := by
      rw [← hcore]
      exact hkK
    have hcomm : (k : X) * u = u * (k : X) := by
      exact (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hkCenter u0)).symm
    apply hM.centralizer_le huFM.2 hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hKH : K ≤ H := by
    intro k hkK
    exact ⟨hcoreM (Subgroup.mem_map_of_mem F0.subtype hkK), k.property⟩
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    simpa [K, twoPrimeCore] using
      (pPrimeCore_coprime_card (p := 2) (G := F0))
  have hKcentral : K ≤ Subgroup.center F0 := by
    rw [show K = twoPrimeCore F0 by rfl, hcore]
  have hBorel' : IsBorelSubgroup B := by
    simpa [B, H, H0, q, K, F0] using hBorel
  have hmodel' : IsSimpleBenderGroup (F0 ⧸ K) := by
    simpa [K, F0] using hmodel
  obtain ⟨Pbar, hPbarNormal, hPbarRegular⟩ :=
    simpleBender_borel_normalSylow_regular hBorel' hmodel'
  obtain ⟨P, hPNormal, hPmap, hPinj⟩ :=
    sylow_lift_of_central_odd_core K H hKH hKodd hKcentral
      Pbar hPbarNormal
  let e : H ≃* H0 := Subgroup.subgroupOfEquivOfLe inf_le_right
  let P0 : Sylow 2 H0 :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP0map : (P0 : Subgroup H0) =
      (P : Subgroup H).map e.toMonoidHom := by
    exact Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP0normal : (P0 : Subgroup H0).Normal := by
    rw [hP0map]
    exact hPNormal.map e.toMonoidHom e.surjective
  let SF0 : Subgroup F0 := (P : Subgroup H).map H.subtype
  let S : Subgroup X := (P0 : Subgroup H0).map H0.subtype
  have hS_eq : S = SF0.map F0.subtype := by
    dsimp [S, SF0]
    rw [hP0map]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hS2 : IsPGroup 2 S := by
    exact (P0.isPGroup'.map H0.subtype)
  have hker : q.ker ≤ H := by
    simpa [q, QuotientGroup.ker_mk'] using hKH
  have hregCoset : IsRegularOn SF0
      {c : F0 ⧸ H | c ≠ QuotientGroup.mk 1} := by
    apply coset_isRegularOn_of_surjective q
      (QuotientGroup.mk'_surjective K) H SF0
      ((Pbar : Subgroup B).map B.subtype)
    · exact hker
    · simpa [SF0, B, q] using hPmap
    · simpa [SF0, q] using hPinj
    · simpa [B] using hPbarRegular
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  have hpoint : pointStabilizerIn F0 alpha = H := by
    ext f
    change (f : X) ∈ MulAction.stabilizer X alpha ↔
      ((f : X) ∈ M ∧ (f : X) ∈ F0)
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha]]
    simp
  have hregF0 : IsRegularOn S
      {omega : conjugateCosetSpace M |
        InOrbit F0 alpha omega ∧ omega ≠ alpha} := by
    rw [hS_eq]
    apply regularOn_orbit_of_coset F0 alpha SF0
    rw [hpoint]
    exact hregCoset
  obtain ⟨x, hxF0, hxM⟩ := SetLike.not_le_iff_exists.mp hnotle
  let beta : conjugateCosetSpace M := x • alpha
  have hbetaOrbit : InOrbit F alpha beta := by
    exact ⟨⟨x, involutionCoreIn_le F hxF0⟩, rfl⟩
  have hbetaNe : beta ≠ alpha := by
    intro h
    apply hxM
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr h
  have hfactorBeta := hfactor beta hbetaOrbit hbetaNe
  have hfactorBase : (F : Set X) =
      (F0 : Set X) *
        ((F ⊓ MulAction.stabilizer X alpha : Subgroup X) : Set X) := by
    apply Set.Subset.antisymm
    · intro y hyF
      have hy := hyF
      rw [hfactorBeta, Set.mem_mul] at hy
      rcases hy with ⟨a, haF0, b, hb, hab⟩
      exact Set.mem_mul.mpr ⟨a, haF0, b, hb.1, hab⟩
    · intro y hy
      rw [Set.mem_mul] at hy
      rcases hy with ⟨a, haF0, b, hb, rfl⟩
      exact F.mul_mem (involutionCoreIn_le F haF0) hb.1
  have horbit : ∀ omega : conjugateCosetSpace M,
      InOrbit F alpha omega ↔ InOrbit F0 alpha omega := by
    intro omega
    exact inOrbit_iff_of_eq_mul_pointStabilizer
      F F0 alpha omega (involutionCoreIn_le F) hfactorBase
  have hregF : IsRegularOn S
      {omega : conjugateCosetSpace M |
        InOrbit F alpha omega ∧ omega ≠ alpha} := by
    intro a b ha hb
    exact hregF0 ⟨(horbit a).mp ha.1, ha.2⟩
      ⟨(horbit b).mp hb.1, hb.2⟩
  let B0 : Subgroup X := F ⊓ M
  have hH0B0 : H0 ≤ B0 := by
    intro x hx
    exact ⟨involutionCoreIn_le F hx.2, hx.1⟩
  have hF0normalF : (F0.subgroupOf F).Normal := by
    dsimp [F0]
    rw [involutionCoreIn, subgroupOf_map_subtype_eq]
    exact involutionCore_normal
  have hH0normalB0 : (H0.subgroupOf B0).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH0B0]
    intro h b hhH0 hbB0
    have hconjF0 : b * h * b⁻¹ ∈ F0 := by
      exact (Subgroup.normal_subgroupOf_iff (involutionCoreIn_le F)).mp
        hF0normalF h b hhH0.2 hbB0.1
    exact ⟨M.mul_mem (M.mul_mem hbB0.2 hhH0.1) (M.inv_mem hbB0.2),
      hconjF0⟩
  have hSleB0 : S ≤ B0 := by
    intro s hs
    rcases Subgroup.mem_map.mp hs with ⟨p, hp, rfl⟩
    exact hH0B0 p.property
  have hP0char : (P0 : Subgroup H0).Characteristic :=
    Sylow.characteristic_of_normal P0 hP0normal
  have hSnormalB0 : (S.subgroupOf B0).Normal :=
    normal_subgroupOf_map_of_characteristic_of_normal
      H0 S B0 hH0B0 hH0normalB0
      (P0 : Subgroup H0) hP0char rfl hSleB0
  exact ⟨S, hS2, by simpa [B0] using hSleB0,
    by simpa [B0] using hSnormalB0,
    by simpa [alpha] using hregF⟩

/-- In the solvable alternative of Corollary 7.13, the unique involution of
the point stabilizer is central there, and hence normalizes every subgroup of
that stabilizer. -/
public theorem exists_local_normalizer_involution_of_corollary713_solvable
    {X : Type u} [Group X] [Finite X] {M F P : Subgroup X}
    (hsolvable : Corollary713SolvableConclusion M F)
    (hP : P ≤ F ⊓ M) :
    ∃ u : X, u ∈ F ⊓ M ∧ IsInvolution u ∧
      u ∈ Subgroup.normalizer (P : Set X) := by
  rcases hsolvable with
    ⟨_solvable, u, huFM, hu, _hunique, hcentralizer⟩
  have huCentral : u ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hpCentral : p ∈ F ⊓ Subgroup.centralizer ({u} : Set X) := by
      rw [← hcentralizer]
      exact hP hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp hpCentral.2
  exact ⟨u, huFM, hu, centralizer_le_normalizer P huCentral⟩

/-- The complete proper-subgroup local normalizer step at the base point.
The solvable Corollary 7.13 branch uses its central involution.  In the
nonsolvable branch, the retained Borel witness gives a normal regular
Sylow-`2` subgroup of `F ∩ M`; two off-base `P`-fixed points then yield an
involution centralizing `P` by the regular-root argument above. -/
public theorem exists_local_normalizer_involution_of_corollary713_borel
    {X : Type u} [Group X] [Finite X]
    (M F P : Subgroup X) (hM : IsStronglyEmbedded M)
    {u : X} (huFM : u ∈ F ⊓ M) (hu : IsInvolution u)
    (h713 : Corollary713BorelConclusion M F)
    (hP : P ≤ F ⊓ M)
    (hthree : 3 ≤ Nat.card
      {omega : conjugateCosetSpace M //
        InOrbit F (QuotientGroup.mk 1) omega ∧
          omega ∈ fixedPointsOfSubgroup X
            (conjugateCosetSpace M) P}) :
    ∃ v : X, v ∈ F ⊓ M ∧ IsInvolution v ∧
      v ∈ Subgroup.normalizer (P : Set X) := by
  classical
  rcases h713 with
    ⟨hnotle, hsolvable | ⟨_nonsolvable, hnonsolvable, hBorel⟩⟩
  · exact exists_local_normalizer_involution_of_corollary713_solvable
      hsolvable hP
  · obtain ⟨S, hS2, hSFM, hSnormal, hregular⟩ :=
      corollary713_nonsolvable_exists_normal_twoSubgroup_regular
        M F hM huFM hu hnotle hnonsolvable hBorel
    have hFMNormS : F ⊓ M ≤ Subgroup.normalizer (S : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSFM).mp hSnormal
    have hPNormS : P ≤ Subgroup.normalizer (S : Set X) :=
      hP.trans hFMNormS
    let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
    let FixedOrbitP :=
      {omega : conjugateCosetSpace M //
        InOrbit F alpha omega ∧
          omega ∈ fixedPointsOfSubgroup X
            (conjugateCosetSpace M) P}
    have hthreeFixed : 3 ≤ Nat.card FixedOrbitP := by
      simpa [FixedOrbitP, alpha] using hthree
    have hPalpha : alpha ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) P := by
      intro p hpP
      apply MulAction.mem_stabilizer_iff.mp
      rw [show MulAction.stabilizer X alpha = M by simp [alpha]]
      exact (hP hpP).2
    let alphaP : FixedOrbitP :=
      ⟨alpha, ⟨⟨1, by simp⟩, hPalpha⟩⟩
    have hnontrivial : Nontrivial FixedOrbitP :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial FixedOrbitP := hnontrivial
    obtain ⟨betaP, hbetaAlpha⟩ := exists_ne alphaP
    have hthreeCardinal : (3 : Cardinal) ≤ Cardinal.mk FixedOrbitP := by
      rw [← Nat.cast_card]
      exact_mod_cast hthreeFixed
    obtain ⟨gammaP, hgammaAlpha, hgammaBeta⟩ :=
      Cardinal.exists_ne_ne_of_three_le
        hthreeCardinal alphaP betaP
    let beta : conjugateCosetSpace M := betaP
    let gamma : conjugateCosetSpace M := gammaP
    have hbetaNeAlpha : beta ≠ alpha := by
      intro h
      apply hbetaAlpha
      apply Subtype.ext
      exact h
    have hgammaNeAlpha : gamma ≠ alpha := by
      intro h
      apply hgammaAlpha
      apply Subtype.ext
      exact h
    have hbetaGamma : beta ≠ gamma := by
      intro h
      apply hgammaBeta
      apply Subtype.ext
      exact h.symm
    obtain ⟨v, hvS, hv, hvCentralizes⟩ :=
      exists_involution_centralizing_of_regular_twoSubgroup_fixedPair
        hS2 hPNormS hregular betaP.property.2 gammaP.property.2
          ⟨betaP.property.1, hbetaNeAlpha⟩
          ⟨gammaP.property.1, hgammaNeAlpha⟩ hbetaGamma
    have hvCentral : v ∈ Subgroup.centralizer (P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hpP
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (hvCentralizes hpP)
    exact ⟨v, hSFM hvS, hv,
      centralizer_le_normalizer P hvCentral⟩

end CFSG.BenderSuzuki
