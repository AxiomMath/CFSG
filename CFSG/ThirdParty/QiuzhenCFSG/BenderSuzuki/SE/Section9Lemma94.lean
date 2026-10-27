module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Focal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.4

This file formalizes the normalizer-factor argument of source Lemma 9.4.  The
two named inputs are the exact earlier-book results `[II1; 4.4]` and
`[II1; 4.3(b)]`; all conjugation, fixed-point, and Proposition 8.4 transport
is proved here.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- If a subgroup of the two-point stabilizer fixes exactly the base coset
and the selected outside coset, then its normalizer inside `W ≤ M` is already
contained in the two-point stabilizer. -/
public theorem normalizerIn_eq_inf_of_fixedPoints_card_eq_two
    {X : Type u} [Group X] [Finite X]
    {M W U : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hWM : W ≤ M)
    (hUD : U ≤ M ⊓ rightConjugate M t)
    (hcard : Nat.card (theorem4bFixedPoints M U) = 2) :
    normalizerIn W U =
      normalizerIn (W ⊓ (M ⊓ rightConjugate M t)) U := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hUM : U ≤ M := hUD.trans inf_le_left
  have hUconj : U ≤ rightConjugate M t := hUD.trans inf_le_right
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U :=
    theorem4b_baseCoset_mem_fixedPoints hUM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U := by
    intro u hu
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hUconj hu
  let alphaFixed : theorem4bFixedPoints M U := ⟨alpha, halpha⟩
  let betaFixed : theorem4bFixedPoints M U := ⟨beta, hbeta⟩
  have hbetaAlpha : betaFixed ≠ alphaFixed := by
    intro h
    apply htM
    simpa [alphaFixed, betaFixed, alpha, beta] using
      QuotientGroup.eq.mp (congrArg Subtype.val h).symm
  obtain ⟨gamma, hgamma, hgammaUnique⟩ :=
    (Nat.card_eq_two_iff' alphaFixed).mp hcard
  have hgammaBeta : gamma = betaFixed :=
    (hgammaUnique betaFixed hbetaAlpha).symm
  apply le_antisymm
  · intro n hn
    have hnM : n ∈ M := hWM hn.1
    have hnAlpha : n • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa [alpha, baseCoset_stabilizer M] using hnM
    have hnBetaFixed :
        (n • beta) ∈ fixedPointsOfSubgroup X
          (conjugateCosetSpace M) U :=
      smul_mem_fixedPointsOfSubgroup_of_mem_normalizer hn.2 hbeta
    let nBeta : theorem4bFixedPoints M U := ⟨n • beta, hnBetaFixed⟩
    have hnBetaNeAlpha : nBeta ≠ alphaFixed := by
      intro h
      apply hbetaAlpha
      apply Subtype.ext
      exact MulAction.injective n (by
        simpa [nBeta, betaFixed, alphaFixed, hnAlpha] using
          congrArg Subtype.val h)
    have hnBetaGamma : nBeta = gamma :=
      hgammaUnique nBeta hnBetaNeAlpha
    have hnBeta : n • beta = beta := by
      have : nBeta = betaFixed := hnBetaGamma.trans hgammaBeta
      exact congrArg Subtype.val this
    have hnConj : n ∈ rightConjugate M t := by
      have hnStab : n ∈ MulAction.stabilizer X beta :=
        MulAction.mem_stabilizer_iff.mpr hnBeta
      rw [show MulAction.stabilizer X beta = rightConjugate M t by
        simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t] at hnStab
      exact hnStab
    exact ⟨⟨hn.1, hnM, hnConj⟩, hn.2⟩
  · intro n hn
    exact ⟨hn.1.1, hn.2⟩

private theorem ambientPPrimeCore_mul_self
    {X : Type u} [Group X] [Finite X]
    (p : ℕ) (N : Subgroup X) :
    ((((pPrimeCore p N).map N.subtype : Subgroup X) : Set X) *
      (N : Set X)) = (N : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨o, ho, n, hn, rfl⟩
    exact N.mul_mem (Subgroup.map_subtype_le (pPrimeCore p N) ho) hn
  · intro n hn
    rw [Set.mem_mul]
    exact ⟨1, by simp, n, hn, one_mul n⟩

/-- The first alternative in source Lemma 9.4. -/
@[expose] public def Lemma94AlternativeA
    {X : Type u} [Group X] [Finite X]
    (W E : Subgroup X) (_hEW : E ≤ W) (p : ℕ) : Prop :=
  ∃ Q : Sylow p W,
    (Q : Subgroup W) ≤ E.subgroupOf W ∧
      ControlsFusionIn (E.subgroupOf W) (Q : Subgroup W)

/-- The second alternative in source Lemma 9.4. -/
@[expose] public def Lemma94AlternativeB
    {X : Type u} [Group X] [Finite X]
    (D E : Subgroup X) (t : X) (p : ℕ) : Prop :=
  ∃ P : Sylow p E,
    IsCyclic P ∧
      (P : Subgroup E).map E.subtype ≤ peterfalviV D t ∧
      PeterfalviCentralizersTrivial D t
        ((P : Subgroup E).map E.subtype)

private theorem factorization_subgroupOf_eq_of_eq_sup_coprime_normal
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {B T N : Subgroup G}
    (hTB : T ≤ B) (hNB : N ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTcop : Nat.Coprime p (Nat.card T)) (hsup : B = T ⊔ N) :
    (Nat.card (N.subgroupOf B)).factorization p =
      (Nat.card B).factorization p := by
  classical
  let TB : Subgroup B := T.subgroupOf B
  let NB : Subgroup B := N.subgroupOf B
  haveI : TB.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2
    exact hBnormT
  have hsupB : TB ⊔ NB = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTB,
      Subgroup.map_subgroupOf_eq_of_le hNB,
      ← hsup]
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (H := B)).symm
  let qB : B →* B ⧸ TB := QuotientGroup.mk' TB
  let f : NB →* B ⧸ TB := qB.comp NB.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective TB y
    have hb : b ∈ TB ⊔ NB := by rw [hsupB]; trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hb with ⟨t, ht, n, hn, htn⟩
    let nn : NB := ⟨n, hn⟩
    refine ⟨nn, ?_⟩
    change qB n = qB b
    have hqt : qB t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [← htn, map_mul, hqt, one_mul]
  have hkerMapLe : f.ker.map NB.subtype ≤ TB := by
    intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨n, hn, rfl⟩
    change qB n = 1 at hn
    exact (QuotientGroup.eq_one_iff (N := TB) (x := (n : B))).1 hn
  have hkerCardDvd : Nat.card f.ker ∣ Nat.card T := by
    have hmapCard : Nat.card (f.ker.map NB.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective NB.subtype_injective
    have hdiv : Nat.card (f.ker.map NB.subtype) ∣ Nat.card TB :=
      Subgroup.card_dvd_of_le hkerMapLe
    rw [show Nat.card TB = Nat.card T by
      simpa [TB] using natCard_subgroupOf_eq T B hTB, hmapCard] at hdiv
    exact hdiv
  have hkerCop : Nat.Coprime p (Nat.card f.ker) :=
    Nat.Coprime.of_dvd_right hkerCardDvd hTcop
  have hquotCard : Nat.card (NB ⧸ f.ker) = Nat.card (B ⧸ TB) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup TB
  have hNBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  calc
    (Nat.card NB).factorization p =
        (Nat.card (NB ⧸ f.ker) * Nat.card f.ker).factorization p := by
      rw [hNBcard]
    _ = (Nat.card (NB ⧸ f.ker)).factorization p := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_eq_zero_of_not_dvd
        ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hkerCop)]
      simp
    _ = (Nat.card (B ⧸ TB)).factorization p := by rw [hquotCard]
    _ = (Nat.card (B ⧸ TB) * Nat.card TB).factorization p := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [show (Nat.card TB).factorization p = 0 by
        apply Nat.factorization_eq_zero_of_not_dvd
        apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
        simpa [TB, natCard_subgroupOf_eq T B hTB] using hTcop]
      simp
    _ = (Nat.card B).factorization p := by rw [hBcard]

private theorem exists_ambient_sylow_of_full_normalizer_factorization
    {X : Type u} [Group X] [Finite X]
    {W E : Subgroup X} (hEW : E ≤ W)
    {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    (hfactor :
      (normalizerIn W ((P : Subgroup E).map E.subtype) : Set X) =
        (((pPrimeCore p
          (normalizerIn W ((P : Subgroup E).map E.subtype))).map
            (normalizerIn W ((P : Subgroup E).map E.subtype)).subtype :
              Subgroup X) : Set X) *
          (normalizerIn E ((P : Subgroup E).map E.subtype) : Set X)) :
    ∃ Q : Sylow p W,
      (Q : Subgroup W).map W.subtype =
        (P : Subgroup E).map E.subtype := by
  classical
  let PA : Subgroup X := (P : Subgroup E).map E.subtype
  let NW : Subgroup X := normalizerIn W PA
  let NE : Subgroup X := normalizerIn E PA
  let K : Subgroup X := (pPrimeCore p NW).map NW.subtype
  have hKNW : K ≤ NW := by
    exact Subgroup.map_subtype_le (pPrimeCore p NW)
  have hNENW : NE ≤ NW := by
    intro x hx
    exact ⟨hEW hx.1, hx.2⟩
  have hNWnormK : NW ≤ Subgroup.normalizer (K : Set X) := by
    intro n hn
    let nNW : NW := ⟨n, hn⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      refine Subgroup.mem_map.mpr ⟨nNW * k * nNW⁻¹,
        pPrimeCore_normal.conj_mem k hk nNW, ?_⟩
      rfl
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
      have hback : n⁻¹ * (n * x * n⁻¹) * n ∈ K := by
        refine Subgroup.mem_map.mpr ⟨nNW⁻¹ * k * nNW,
          (by simpa only [inv_inv] using
            pPrimeCore_normal.conj_mem k hk nNW⁻¹), ?_⟩
        change (n : X)⁻¹ * NW.subtype k * (n : X) =
          n⁻¹ * (n * x * n⁻¹) * n
        rw [hkx]
      simpa [mul_assoc] using hback
  have hKcard : Nat.card K = Nat.card (pPrimeCore p NW) := by
    exact Subgroup.card_map_of_injective NW.subtype_injective
  have hKcop : Nat.Coprime p (Nat.card K) := by
    rw [hKcard]
    exact pPrimeCore_coprime_card
  have hsup : NW = K ⊔ NE := by
    apply le_antisymm
    · intro x hx
      have hxprod : x ∈ (K : Set X) * (NE : Set X) := by
        have hx' : x ∈
            (normalizerIn W ((P : Subgroup E).map E.subtype) : Set X) := by
          simpa [NW, PA] using hx
        rw [hfactor] at hx'
        simpa [K, NE, NW, PA] using hx'
      rw [Set.mem_mul] at hxprod
      rcases hxprod with ⟨k, hk, e, he, rfl⟩
      exact (K ⊔ NE).mul_mem (Subgroup.mem_sup_left hk)
        (Subgroup.mem_sup_right he)
    · exact sup_le hKNW hNENW
  have hfacNEraw :=
    factorization_subgroupOf_eq_of_eq_sup_coprime_normal
      hKNW hNENW hNWnormK hKcop hsup
  have hfacNE_NW : (Nat.card NE).factorization p =
      (Nat.card NW).factorization p := by
    simpa [natCard_subgroupOf_eq NE NW hNENW] using hfacNEraw
  have hNEE : NE ≤ E := by
    exact inf_le_left
  have hPANE : PA ≤ NE := by
    intro x hx
    exact ⟨Subgroup.map_subtype_le (P : Subgroup E) hx,
      Subgroup.le_normalizer hx⟩
  have hfacNEleE : (Nat.card NE).factorization p ≤
      (Nat.card E).factorization p := by
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hNEE) Nat.card_pos.ne' Nat.card_pos.ne'
  have hPAcard : Nat.card PA = p ^ (Nat.card E).factorization p := by
    calc
      Nat.card PA = Nat.card (P : Subgroup E) := by
        simpa [PA] using
          Subgroup.card_map_of_injective E.subtype_injective
      _ = p ^ (Nat.card E).factorization p := P.card_eq_multiplicity
  have hfacPA : (Nat.card PA).factorization p =
      (Nat.card E).factorization p := by
    rw [hPAcard, Nat.factorization_pow_self Fact.out]
  have hfacEleNE : (Nat.card E).factorization p ≤
      (Nat.card NE).factorization p := by
    rw [← hfacPA]
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hPANE) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfacNE_E : (Nat.card NE).factorization p =
      (Nat.card E).factorization p :=
    le_antisymm hfacNEleE hfacEleNE
  have hPANW : PA ≤ NW := hPANE.trans hNENW
  let PNW : Subgroup NW := PA.subgroupOf NW
  have hPNWcard : Nat.card PNW = p ^ (Nat.card NW).factorization p := by
    calc
      Nat.card PNW = Nat.card PA := by
        simpa [PNW] using natCard_subgroupOf_eq PA NW hPANW
      _ = p ^ (Nat.card E).factorization p := hPAcard
      _ = p ^ (Nat.card NE).factorization p := by rw [hfacNE_E]
      _ = p ^ (Nat.card NW).factorization p := by rw [hfacNE_NW]
  let SNW : Sylow p NW := Sylow.ofCard PNW hPNWcard
  have hPAW : PA ≤ W := hPANE.trans (hNENW.trans inf_le_left)
  let PW : Subgroup W := PA.subgroupOf W
  have hPAp : IsPGroup p PA := by
    simpa [PA] using P.isPGroup'.map E.subtype
  have hPWp : IsPGroup p PW :=
    hPAp.of_equiv (Subgroup.subgroupOfEquivOfLe hPAW).symm
  obtain ⟨SW, hPWSW⟩ := hPWp.exists_le_sylow
  have hPWeq : PW = (SW : Subgroup W) := by
    by_contra hne
    have hPWlt : PW < (SW : Subgroup W) := lt_of_le_of_ne hPWSW hne
    have hlt := External.hkt_factorization_lt_ambient_normalizer_of_lt_sylow
      (S := SW) hPWlt
    have hnormEq : Subgroup.normalizer (PW : Set W) = NW.subgroupOf W := by
      ext n
      constructor
      · intro hn
        change (n : X) ∈ NW
        refine ⟨n.property, ?_⟩
        change (n : X) ∈ Subgroup.normalizer (PA : Set X)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hxPA
          let xW : W := ⟨x, hPAW hxPA⟩
          have hxPW : xW ∈ PW := hxPA
          have hconj := (Subgroup.mem_normalizer_iff.mp hn xW).mp hxPW
          exact hconj
        · intro hxConjPA
          have hxW : x ∈ W := by
            have hxConjW : (n : X) * x * (n : X)⁻¹ ∈ W :=
              hPAW hxConjPA
            have hback := W.mul_mem
              (W.mul_mem (W.inv_mem n.property) hxConjW) n.property
            simpa [mul_assoc] using hback
          let xW : W := ⟨x, hxW⟩
          have hconj : (n * xW * n⁻¹ : W) ∈ PW := hxConjPA
          exact (Subgroup.mem_normalizer_iff.mp hn xW).mpr hconj
      · intro hn
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have hnPA : (n : X) ∈ Subgroup.normalizer (PA : Set X) := hn.2
        constructor
        · intro hxPW
          exact (Subgroup.mem_normalizer_iff.mp hnPA (x : X)).mp hxPW
        · intro hxConj
          exact (Subgroup.mem_normalizer_iff.mp hnPA (x : X)).mpr hxConj
    have hnormCard : Nat.card (Subgroup.normalizer (PW : Set W)) = Nat.card NW := by
      rw [hnormEq]
      simpa using natCard_subgroupOf_eq NW W (by simpa [NW, normalizerIn])
    have hPWcard : Nat.card PW = Nat.card PNW := by
      calc
        Nat.card PW = Nat.card PA := by
          simpa [PW] using natCard_subgroupOf_eq PA W hPAW
        _ = Nat.card PNW := by
          simpa [PNW] using (natCard_subgroupOf_eq PA NW hPANW).symm
    have hfacSNW : (Nat.card PNW).factorization p =
        (Nat.card NW).factorization p := by
      simpa [SNW] using section8_factorization_card_sylow SNW
    rw [hPWcard, hnormCard, hfacSNW] at hlt
    exact (lt_irrefl _ hlt)
  refine ⟨SW, ?_⟩
  rw [← hPWeq]
  exact Subgroup.map_subgroupOf_eq_of_le hPAW

/-- Ambient-subgroup form of `[II1; 4.4]`.  This is the literal source
normalizer criterion, with every subgroup embedded in the common ambient
group so it can be compared directly with Proposition 8.4. -/
@[expose] public def II1Lemma44Ambient
    {X : Type u} [Group X] [Finite X]
    (W E : Subgroup X) (hEW : E ≤ W) (p : ℕ) : Prop :=
  (∀ P : Sylow p E,
    ∀ U : Subgroup X,
      U ≤ (P : Subgroup E).map E.subtype →
      (¬ IsCyclic U ∨ U = (P : Subgroup E).map E.subtype) →
      (normalizerIn W U : Set X) =
        (((pPrimeCore p (normalizerIn W U)).map
          (normalizerIn W U).subtype : Subgroup X) : Set X) *
          (normalizerIn E U : Set X)) →
    Lemma94AlternativeA W E hEW p

private theorem section9_cyclic_extremal_normalizer_factor
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {U : Subgroup G}
    (hU : External.HuppertExtremal P U) (hUcyc : IsCyclic U)
    {h : G} (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    ∃ c n : G,
      c ∈ Subgroup.centralizer (U : Set G) ∧
      n ∈ Subgroup.normalizer
        (((P : Subgroup G) ⊓ Subgroup.normalizer (U : Set G)) : Set G) ∧
      h = c * n := by
  classical
  let N : Subgroup G := Subgroup.normalizer (U : Set G)
  let V : Subgroup G := (P : Subgroup G) ⊓ N
  have hVN : V ≤ N := inf_le_right
  let VN : Subgroup N := V.subgroupOf N
  have hVp : IsPGroup p V := IsPGroup.to_le P.isPGroup' inf_le_left
  have hVNp : IsPGroup p VN :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  have hVNcard : Nat.card VN = p ^ (Nat.card N).factorization p := by
    calc
      Nat.card VN = Nat.card V := by
        simpa [VN] using natCard_subgroupOf_eq V N hVN
      _ = p ^ (Nat.card V).factorization p :=
        section8_card_eq_prime_pow_factorization_of_isPGroup hVp
      _ = p ^ (Nat.card N).factorization p := by
        rw [show (Nat.card V).factorization p =
            (Nat.card N).factorization p by
          simpa [V, N] using hU.2]
  let S : Sylow p N := Sylow.ofCard VN hVNcard
  let C : Subgroup G := Subgroup.centralizer (U : Set G)
  have hCN : C ≤ N := by
    simpa [C, N] using centralizer_le_normalizer U
  let CN : Subgroup N := C.subgroupOf N
  haveI : CN.Normal := by
    simpa [CN, C, N] using
      (External.hkt_normal_subgroupOf_centralizer_normalizer U)
  letI : IsCyclic U := hUcyc
  have hAutComm : IsMulCommutative (MulAut U) := by
    let e := IsCyclic.mulAutMulEquiv (G := U)
    refine ⟨⟨fun a b => ?_⟩⟩
    apply e.injective
    change e (a * b) = e (b * a)
    simp [mul_comm]
  letI : IsMulCommutative (MulAut U) := hAutComm
  let K : Subgroup N := CN ⊔ VN
  have hconjVN : ∀ n : N, ∀ v : N, v ∈ VN → n * v * n⁻¹ ∈ K := by
    intro n v hv
    let z : N := n * v * n⁻¹ * v⁻¹
    have hzker : z ∈ U.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [z]
      simp only [map_mul, map_inv]
      rw [mul_comm' (U.normalizerMonoidHom n)
        (U.normalizerMonoidHom v)]
      simp
    have hzCN : z ∈ CN := by
      simpa [CN, C, N, Subgroup.normalizerMonoidHom_ker] using hzker
    have hzv : z * v ∈ K :=
      K.mul_mem (Subgroup.mem_sup_left hzCN) (Subgroup.mem_sup_right hv)
    simpa [z, mul_assoc] using hzv
  letI : K.Normal := by
    refine { conj_mem := ?_ }
    intro k hk n
    rcases Subgroup.mem_sup_of_normal_left.mp hk with
      ⟨c, hc, v, hv, hcv⟩
    have hcn : n * c * n⁻¹ ∈ CN :=
      (inferInstance : CN.Normal).conj_mem c hc n
    have hvn : n * v * n⁻¹ ∈ K := hconjVN n v hv
    have hprod : (n * c * n⁻¹) * (n * v * n⁻¹) ∈ K :=
      K.mul_mem (Subgroup.mem_sup_left hcn) hvn
    rw [← hcv]
    simpa [mul_assoc] using hprod
  have hSleK : (S : Subgroup N) ≤ K := by
    change VN ≤ K
    exact le_sup_right
  have hfrattini :
      Subgroup.normalizer ((S : Subgroup N) : Set N) ⊔ K = ⊤ :=
    S.normalizer_sup_eq_top' hSleK
  let hN : N := ⟨h, hh⟩
  have hhSup : hN ∈ Subgroup.normalizer ((S : Subgroup N) : Set N) ⊔ K := by
    rw [hfrattini]
    trivial
  rcases Subgroup.mem_sup_of_normal_right.mp hhSup with
    ⟨r, hr, k, hk, hrk⟩
  rcases Subgroup.mem_sup_of_normal_left.mp hk with
    ⟨c, hc, v, hv, hcv⟩
  let c' : N := r * c * r⁻¹
  let n' : N := r * v
  have hc'CN : c' ∈ CN :=
    (inferInstance : CN.Normal).conj_mem c hc r
  have hn'Norm : n' ∈ Subgroup.normalizer (VN : Set N) := by
    change r * v ∈ Subgroup.normalizer ((S : Subgroup N) : Set N)
    exact (Subgroup.normalizer ((S : Subgroup N) : Set N)).mul_mem hr
      (Subgroup.le_normalizer hv)
  have hn'NormV : (n' : G) ∈ Subgroup.normalizer (V : Set G) := by
    have hn'map : (n' : G) ∈
        (Subgroup.normalizer (VN : Set N)).map N.subtype :=
      Subgroup.mem_map.mpr ⟨n', hn'Norm, rfl⟩
    have := Subgroup.le_normalizer_map N.subtype hn'map
    simpa [VN, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hVN] using this
  refine ⟨(c' : G), (n' : G), ?_, ?_, ?_⟩
  · change (c' : G) ∈ C
    exact hc'CN
  · simpa [V, N] using hn'NormV
  · calc
      h = (hN : G) := rfl
      _ = ((r * k : N) : G) := congrArg Subtype.val hrk.symm
      _ = ((r * (c * v) : N) : G) := by rw [hcv]
      _ = (c' : G) * (n' : G) := by
        dsimp [c', n']
        simp [mul_assoc]

private theorem section9_factor_step
    {X : Type u} [Group X] [Finite X]
    {W E : Subgroup X} (hEW : E ≤ W)
    {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    {Q : Sylow p W}
    (hQmap : (Q : Subgroup W).map W.subtype =
      (P : Subgroup E).map E.subtype)
    (hcriterion : ∀ P : Sylow p E,
      ∀ U : Subgroup X,
        U ≤ (P : Subgroup E).map E.subtype →
        (¬ IsCyclic U ∨ U = (P : Subgroup E).map E.subtype) →
        (normalizerIn W U : Set X) =
          (((pPrimeCore p (normalizerIn W U)).map
            (normalizerIn W U).subtype : Subgroup X) : Set X) *
            (normalizerIn E U : Set X))
    {S : Subgroup W} (hSQ : S ≤ (Q : Subgroup W))
    (hSshape : ¬ IsCyclic S ∨ S = (Q : Subgroup W))
    {n a : W} (hn : n ∈ Subgroup.normalizer (S : Set W))
    (ha : a ∈ S) :
    ∃ e : E.subgroupOf W,
      (e : W)⁻¹ * a * (e : W) = n⁻¹ * a * n := by
  classical
  let SA : Subgroup X := S.map W.subtype
  let PA : Subgroup X := (P : Subgroup E).map E.subtype
  have hSQmap :
      S.map W.subtype ≤ (Q : Subgroup W).map W.subtype :=
    Subgroup.map_mono hSQ
  have hSAP : SA ≤ PA := by
    change S.map W.subtype ≤ (P : Subgroup E).map E.subtype
    exact hSQmap.trans_eq hQmap
  let eS : S ≃* SA := by
    simpa [SA] using
      Subgroup.equivMapOfInjective S W.subtype W.subtype_injective
  have hSAshape : ¬ IsCyclic SA ∨ SA = PA := by
    rcases hSshape with hSnoncyclic | hSQeq
    · left
      intro hSAcyclic
      exact hSnoncyclic (eS.isCyclic.mpr hSAcyclic)
    · right
      simpa [SA, PA, hSQeq] using hQmap
  have hnSA : (n : X) ∈ Subgroup.normalizer (SA : Set X) := by
    have hnMap : (n : X) ∈
        (Subgroup.normalizer (S : Set W)).map W.subtype :=
      Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    simpa [SA] using Subgroup.le_normalizer_map W.subtype hnMap
  let NW : Subgroup X := normalizerIn W SA
  have hnNW : (n : X) ∈ NW := ⟨n.property, hnSA⟩
  have hfactor := hcriterion P SA hSAP hSAshape
  have hnProd : (n : X) ∈
      ((((pPrimeCore p NW).map NW.subtype : Subgroup X) : Set X) *
        (normalizerIn E SA : Set X)) := by
    rw [← hfactor]
    exact hnNW
  rcases Set.mem_mul.mp hnProd with ⟨o, ho, e, he, hoe⟩
  have hSANW : SA ≤ NW := by
    intro x hx
    exact ⟨Subgroup.map_subtype_le S hx, Subgroup.le_normalizer hx⟩
  let SAN : Subgroup NW := SA.subgroupOf NW
  haveI : SAN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hSANW).2
    exact inf_le_right
  have hSp : IsPGroup p S := IsPGroup.to_le Q.isPGroup' hSQ
  have hSAp : IsPGroup p SA := by
    simpa [SA] using hSp.map W.subtype
  have hSANp : IsPGroup p SAN :=
    hSAp.of_equiv (Subgroup.subgroupOfEquivOfLe hSANW).symm
  have hcoreCent :
      pPrimeCore p NW ≤ Subgroup.centralizer (SAN : Set NW) :=
    pPrimeCore_le_centralizer_of_normal_pgroup p SAN hSANp
  rcases Subgroup.mem_map.mp ho with ⟨oN, hoCore, rfl⟩
  have hoCent : (oN : X) ∈ Subgroup.centralizer (SA : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let sN : NW := ⟨s, hSANW hs⟩
    have hsSAN : sN ∈ SAN := hs
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp (hcoreCent hoCore)) sN hsSAN)
  have haSA : (a : X) ∈ SA :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hoa : (oN : X) * (a : X) = (a : X) * (oN : X) :=
    ((Subgroup.mem_centralizer_iff.mp hoCent) (a : X) haSA).symm
  have hoConj : (oN : X)⁻¹ * (a : X) * (oN : X) = (a : X) := by
    calc
      (oN : X)⁻¹ * (a : X) * (oN : X) =
          (oN : X)⁻¹ * ((a : X) * (oN : X)) := by simp [mul_assoc]
      _ = (oN : X)⁻¹ * ((oN : X) * (a : X)) := by rw [hoa]
      _ = (a : X) := by simp [mul_assoc]
  let eW : E.subgroupOf W := ⟨⟨e, hEW he.1⟩, he.1⟩
  change (oN : X) * e = (n : X) at hoe
  refine ⟨eW, ?_⟩
  apply Subtype.ext
  change e⁻¹ * (a : X) * e = (n : X)⁻¹ * (a : X) * (n : X)
  calc
    e⁻¹ * (a : X) * e =
        e⁻¹ * ((oN : X)⁻¹ * (a : X) * (oN : X)) * e := by
      rw [hoConj]
    _ = ((oN : X) * e)⁻¹ * (a : X) * ((oN : X) * e) := by
      group
    _ = (n : X)⁻¹ * (a : X) * (n : X) := by rw [hoe]

private theorem section9_factor_centric_decomposition
    {X : Type u} [Group X] [Finite X]
    {W E : Subgroup X} (hEW : E ≤ W)
    {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    {Q : Sylow p W}
    (hQmap : (Q : Subgroup W).map W.subtype =
      (P : Subgroup E).map E.subtype)
    (hcriterion : ∀ P : Sylow p E,
      ∀ U : Subgroup X,
        U ≤ (P : Subgroup E).map E.subtype →
        (¬ IsCyclic U ∨ U = (P : Subgroup E).map E.subtype) →
        (normalizerIn W U : Set X) =
          (((pPrimeCore p (normalizerIn W U)).map
            (normalizerIn W U).subtype : Subgroup X) : Set X) *
            (normalizerIn E U : Set X))
    {A : Subgroup W} {a g : W} (ha : a ∈ A)
    (hdec : External.HuppertCentricConjugationDecomposition
      (Q : Subgroup W) (External.HuppertExtremal Q) A g) :
    ∃ e : E.subgroupOf W,
      (e : W)⁻¹ * a * (e : W) = g⁻¹ * a * g := by
  classical
  induction hdec with
  | one =>
      exact ⟨1, by simp⟩
  | @tail g h U hprev hUext hUQ hcur hn hcentric ih =>
      rcases ih with ⟨e₀, he₀⟩
      have haU : g⁻¹ * a * g ∈ U := by
        exact hcur (rightConjugateElem_mem_rightConjugate ha)
      have hstep : ∃ e₁ : E.subgroupOf W,
          (e₁ : W)⁻¹ * (g⁻¹ * a * g) * (e₁ : W) =
            h⁻¹ * (g⁻¹ * a * g) * h := by
        rcases hcentric with hself | hcentral
        · by_cases hshape : ¬ IsCyclic U ∨ U = (Q : Subgroup W)
          · exact section9_factor_step hEW P hQmap hcriterion
              hUQ hshape hn haU
          · have hUcyc : IsCyclic U := by
              by_contra hnoncyc
              exact hshape (Or.inl hnoncyc)
            have hUne : U ≠ (Q : Subgroup W) := by
              intro hUQeq
              exact hshape (Or.inr hUQeq)
            have hUltQ : U < (Q : Subgroup W) :=
              lt_of_le_of_ne hUQ hUne
            let V : Subgroup W :=
              (Q : Subgroup W) ⊓ Subgroup.normalizer (U : Set W)
            have hUV : U ≤ V :=
              le_inf hUQ Subgroup.le_normalizer
            have hfacUV :
                (Nat.card U).factorization p <
                  (Nat.card V).factorization p := by
              calc
                (Nat.card U).factorization p <
                    (Nat.card (Subgroup.normalizer (U : Set W))).factorization p :=
                  External.hkt_factorization_lt_ambient_normalizer_of_lt_sylow
                    Q hUltQ
                _ = (Nat.card V).factorization p := by
                  simpa [V] using hUext.2.symm
            have hUVlt : U < V := by
              apply lt_of_le_of_ne hUV
              intro hUVeq
              rw [← hUVeq] at hfacUV
              exact (lt_irrefl _ hfacUV)
            have hVnoncyc : ¬ IsCyclic V := by
              intro hVcyc
              letI : IsCyclic V := hVcyc
              have hVcent :
                  V ≤ subgroupCentralizerIn (Q : Subgroup W) U := by
                intro v hv
                refine ⟨hv.1, ?_⟩
                change v ∈ Subgroup.centralizer (U : Set W)
                rw [Subgroup.mem_centralizer_iff]
                intro z hz
                exact congrArg Subtype.val
                  (mul_comm' (⟨z, hUV hz⟩ : V) (⟨v, hv⟩ : V))
              exact (not_le_of_gt hUVlt) (hVcent.trans hself)
            obtain ⟨c, n, hc, hnV, hhn⟩ :=
              section9_cyclic_extremal_normalizer_factor hUext hUcyc hn
            obtain ⟨e₁, he₁⟩ := section9_factor_step hEW P hQmap
              hcriterion (S := V) inf_le_left (Or.inl hVnoncyc)
                hnV (hUV haU)
            have hcComm :
                (g⁻¹ * a * g) * c = c * (g⁻¹ * a * g) :=
              (Subgroup.mem_centralizer_iff.mp hc) _ haU
            have hcFix :
                c⁻¹ * (g⁻¹ * a * g) * c = g⁻¹ * a * g := by
              calc
                c⁻¹ * (g⁻¹ * a * g) * c =
                    c⁻¹ * ((g⁻¹ * a * g) * c) := by
                  simp [mul_assoc]
                _ = c⁻¹ * (c * (g⁻¹ * a * g)) := by rw [hcComm]
                _ = g⁻¹ * a * g := by simp [mul_assoc]
            refine ⟨e₁, he₁.trans ?_⟩
            rw [hhn]
            calc
              n⁻¹ * (g⁻¹ * a * g) * n =
                  n⁻¹ * (c⁻¹ * (g⁻¹ * a * g) * c) * n := by
                rw [hcFix]
              _ = (c * n)⁻¹ * (g⁻¹ * a * g) * (c * n) := by
                group
        · refine ⟨1, ?_⟩
          have hcomm :
              (g⁻¹ * a * g) * h = h * (g⁻¹ * a * g) :=
            (Subgroup.mem_centralizer_iff.mp hcentral) _ haU
          have hfix : h⁻¹ * (g⁻¹ * a * g) * h = g⁻¹ * a * g := by
            calc
              h⁻¹ * (g⁻¹ * a * g) * h =
                  h⁻¹ * ((g⁻¹ * a * g) * h) := by
                simp [mul_assoc]
              _ = h⁻¹ * (h * (g⁻¹ * a * g)) := by rw [hcomm]
              _ = g⁻¹ * a * g := by simp [mul_assoc]
          simpa using hfix.symm
      rcases hstep with ⟨e₁, he₁⟩
      refine ⟨e₀ * e₁, ?_⟩
      change
        ((e₀ : W) * (e₁ : W))⁻¹ * a * ((e₀ : W) * (e₁ : W)) =
          (g * h)⁻¹ * a * (g * h)
      calc
        ((e₀ : W) * (e₁ : W))⁻¹ * a * ((e₀ : W) * (e₁ : W)) =
            (e₁ : W)⁻¹ * ((e₀ : W)⁻¹ * a * (e₀ : W)) * (e₁ : W) := by
          group
        _ = (e₁ : W)⁻¹ * (g⁻¹ * a * g) * (e₁ : W) := by rw [he₀]
        _ = h⁻¹ * (g⁻¹ * a * g) * h := he₁
        _ = (g * h)⁻¹ * a * (g * h) := by group

public theorem ii1Lemma44Ambient
    {X : Type u} [Group X] [Finite X]
    {W E : Subgroup X} (hEW : E ≤ W) {p : ℕ} [Fact p.Prime] :
    II1Lemma44Ambient W E hEW p := by
  intro hcriterion
  classical
  let P : Sylow p E :=
    Classical.choice (Sylow.nonempty (p := p) (G := E))
  obtain ⟨Q, hQmap⟩ :=
    exists_ambient_sylow_of_full_normalizer_factorization hEW P
      (hcriterion P ((P : Subgroup E).map E.subtype)
        le_rfl (Or.inr rfl))
  have hQleE : (Q : Subgroup W) ≤ E.subgroupOf W := by
    intro q hq
    have hqx : (q : X) ∈ (P : Subgroup E).map E.subtype := by
      rw [← hQmap]
      exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    rcases Subgroup.mem_map.mp hqx with ⟨r, hr, hqr⟩
    change (q : X) ∈ E
    rw [← hqr]
    exact r.property
  refine ⟨Q, hQleE, ControlsFusionIn.of_conjugators ?_⟩
  intro x y hxQ hyQ hxy
  rcases isConj_iff.mp hxy with ⟨g, hxyg⟩
  let A : Subgroup W := Subgroup.zpowers x
  have hAQ : A ≤ (Q : Subgroup W) := by
    simpa [A] using (Subgroup.zpowers_le.mpr hxQ)
  have hrightA : rightConjugate A g⁻¹ = Subgroup.zpowers y := by
    change rightConjugate (Subgroup.zpowers x) g⁻¹ = Subgroup.zpowers y
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    simp [hxyg]
  have hrightAQ : rightConjugate A g⁻¹ ≤ (Q : Subgroup W) := by
    rw [hrightA]
    exact Subgroup.zpowers_le.mpr hyQ
  have hdec :=
    External.HuppertExtremal.centric_conjugation_decomposition Q hAQ hrightAQ
  obtain ⟨e, he⟩ := section9_factor_centric_decomposition hEW P hQmap
    hcriterion (A := A) (a := x) (g := g⁻¹)
      (Subgroup.mem_zpowers x) hdec
  refine ⟨e⁻¹, ?_⟩
  have heY : (e : W)⁻¹ * x * (e : W) = y := by
    calc
      (e : W)⁻¹ * x * (e : W) =
          (g⁻¹ : W)⁻¹ * x * (g⁻¹ : W) := he
      _ = y := by simpa using hxyg
  simpa using heY

private theorem section9_normalizer_conjBy
    {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer (H.conjBy g : Set G) =
      (Subgroup.normalizer (H : Set G)).conjBy g := by
  simpa [Subgroup.conjBy] using
    (Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)).symm

private theorem section9_normalizerIn_conjBy
    {G : Type u} [Group G] (H U : Subgroup G) (g : G) :
    normalizerIn (H.conjBy g) (U.conjBy g) =
      (normalizerIn H U).conjBy g := by
  rw [normalizerIn, normalizerIn, section9_normalizer_conjBy]
  simpa [Subgroup.conjBy] using
    (Subgroup.map_inf_eq H (Subgroup.normalizer (U : Set G))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

private theorem section9_conjBy_set_mul
    {G : Type u} [Group G] (A B : Subgroup G) (g : G) :
    (((A.conjBy g : Subgroup G) : Set G) *
        ((B.conjBy g : Subgroup G) : Set G)) =
      (MulAut.conj g) '' ((A : Set G) * (B : Set G)) := by
  rw [Set.image_mul]
  rfl

private theorem section9_factorization_conjBy_back
    {G : Type u} [Group G] [Finite G]
    {W E U : Subgroup G} (p : ℕ) (g : G)
    (hEq : (normalizerIn (W.conjBy g) (U.conjBy g) : Set G) =
      (((pPrimeCore p (normalizerIn (W.conjBy g) (U.conjBy g))).map
        (normalizerIn (W.conjBy g) (U.conjBy g)).subtype : Subgroup G) : Set G) *
        (normalizerIn (E.conjBy g) (U.conjBy g) : Set G)) :
    (normalizerIn W U : Set G) =
      (((pPrimeCore p (normalizerIn W U)).map
        (normalizerIn W U).subtype : Subgroup G) : Set G) *
        (normalizerIn E U : Set G) := by
  rw [section9_normalizerIn_conjBy, section9_normalizerIn_conjBy] at hEq
  rw [← theorem4b_ambientPPrimeCore_conjBy p (normalizerIn W U) g] at hEq
  rw [section9_conjBy_set_mul] at hEq
  exact (Set.image_injective.mpr (MulAut.conj g).injective) hEq

private theorem section9_two_le_fixedPoints_of_le_inf
    {X : Type u} [Group X] [Finite X]
    {M D U : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hUD : U ≤ D) (hD : D ≤ M ⊓ rightConjugate M t) :
    2 ≤ Nat.card (theorem4bFixedPoints M U) := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hUM : U ≤ M := hUD.trans (hD.trans inf_le_left)
  have hUconj : U ≤ rightConjugate M t := hUD.trans (hD.trans inf_le_right)
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U :=
    theorem4b_baseCoset_mem_fixedPoints hUM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U := by
    intro u hu
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hUconj hu
  have hab : alpha ≠ beta := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  let p0 : theorem4bFixedPoints M U := ⟨alpha, halpha⟩
  let p1 : theorem4bFixedPoints M U := ⟨beta, hbeta⟩
  let f : Fin 2 → theorem4bFixedPoints M U :=
    fun i => if i = 0 then p0 else p1
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hab (congrArg Subtype.val hij)
    · exfalso
      exact hab (congrArg Subtype.val hij).symm
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

public theorem lemma_9_4
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsNormalSupplement M (M ⊓ rightConjugate M t) W)
    (hpE : p ∣ Nat.card (W ⊓ (M ⊓ rightConjugate M t) : Subgroup X))
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43 : II1Lemma43bCyclic (X := X)) :
    Lemma94AlternativeA W (W ⊓ (M ⊓ rightConjugate M t))
        inf_le_left p ∨
      Lemma94AlternativeB (M ⊓ rightConjugate M t)
        (W ⊓ (M ⊓ rightConjugate M t)) t p := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  have hEW : E ≤ W := inf_le_left
  by_cases hA : Lemma94AlternativeA W E hEW p
  · exact Or.inl (by simpa [D, E] using hA)
  right
  have hcriterion : ¬ (∀ P : Sylow p E,
      ∀ U : Subgroup X,
        U ≤ (P : Subgroup E).map E.subtype →
        (¬ IsCyclic U ∨ U = (P : Subgroup E).map E.subtype) →
        (normalizerIn W U : Set X) =
          (((pPrimeCore p (normalizerIn W U)).map
            (normalizerIn W U).subtype : Subgroup X) : Set X) *
            (normalizerIn E U : Set X)) := by
    intro h
    exact hA ((ii1Lemma44Ambient (W := W) (E := E) inf_le_left) h)
  push_neg at hcriterion
  rcases hcriterion with ⟨P, U, hUP, hUshape, hbad⟩
  have hUE : U ≤ E :=
    hUP.trans (Subgroup.map_subtype_le (P : Subgroup E))
  have hUD : U ≤ D := hUE.trans inf_le_right
  have htwo : 2 ≤ Nat.card (theorem4bFixedPoints M U) :=
    section9_two_le_fixedPoints_of_le_inf ht htM hUD (by
      simp [D])
  by_cases hcard : Nat.card (theorem4bFixedPoints M U) = 2
  · have hnormEq : normalizerIn W U = normalizerIn E U := by
      simpa [E, D] using
        (normalizerIn_eq_inf_of_fixedPoints_card_eq_two
          (M := M) (W := W) (U := U) ht htM hW.le_M hUD hcard)
    apply False.elim
    apply hbad
    rw [← hnormEq]
    exact (ambientPPrimeCore_mul_self p (normalizerIn W U)).symm
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M U) := by omega
  obtain ⟨d, hdD, hUright⟩ := d83.conjugate_le U (by simpa [D] using hUD) hthree
  let g : X := d⁻¹
  let U' : Subgroup X := U.conjBy g
  have hU'V : U' ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    simpa [U', g, D, rightConjugate] using hUright
  have hgD : g ∈ D := D.inv_mem (by simpa [D] using hdD)
  have hDleM : D ≤ M := by
    simp [D]
  have hgM : g ∈ M := hDleM hgD
  have hWnorm : M ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW.le_M).mp
      hW.normal_in_M
  have hWg : W.conjBy g = W :=
    section11_conjBy_eq_of_mem_normalizer (hWnorm hgM)
  have hDg : D.conjBy g = D :=
    section11_conjBy_eq_of_mem_normalizer (Subgroup.le_normalizer hgD)
  have hEg : E.conjBy g = E := by
    change (W ⊓ D).conjBy g = W ⊓ D
    rw [Subgroup.conjBy,
      Subgroup.map_inf_eq W D (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective]
    change W.conjBy g ⊓ D.conjBy g = W ⊓ D
    rw [hWg, hDg]
  have hU'E : U' ≤ E := by
    rw [← hEg]
    exact Subgroup.map_mono hUE
  let Pamb : Subgroup X := (P : Subgroup E).map E.subtype
  have hPambP : IsPGroup p Pamb := by
    simpa [Pamb] using P.isPGroup'.map E.subtype
  let UP : Subgroup Pamb := U.subgroupOf Pamb
  have hUp : IsPGroup p U := by
    have hUPp : IsPGroup p UP := hPambP.to_subgroup UP
    exact hUPp.of_equiv (Subgroup.subgroupOfEquivOfLe hUP)
  let eU : U ≃* U' := by
    exact MulEquiv.subgroupMap (MulAut.conj g) U
  have hU'p : IsPGroup p U' := hUp.of_equiv eU
  have hNoI : ∀ (U1 : Subgroup X), U1 ≠ ⊥ → U1 ≤ U' →
      ¬ HasNontrivialPeterfalviNormalizer D t U1 := by
    intro U1 hU1ne hU1U' hIU1
    haveI : Group.IsNilpotent U' :=
      IsPGroup.isNilpotent (G := U') (p := p) hU'p
    have hsubnormal : (U1.subgroupOf U').IsSubnormal :=
      section8_isSubnormal_of_normalizerCondition
        normalizerCondition_of_isNilpotent (U1.subgroupOf U')
    have hEq' := hM.proposition84_normalizerIn_eq_pPrimeCore_mul
      htM d83 h84 hU'V hU1ne hU1U' hsubnormal hIU1 hW
      ((Fact.out : Nat.Prime p).odd_of_ne_two (by
        intro hp2
        subst p
        exact (hM.minimalNormalSupplement_inf_right_card_odd
          (W := W) htM).not_two_dvd_nat hpE))
    have hEqConj :
        (normalizerIn (W.conjBy g) (U.conjBy g) : Set X) =
          (((pPrimeCore p
            (normalizerIn (W.conjBy g) (U.conjBy g))).map
              (normalizerIn (W.conjBy g) (U.conjBy g)).subtype :
                Subgroup X) : Set X) *
            (normalizerIn (E.conjBy g) (U.conjBy g) : Set X) := by
      rw [hWg, hEg]
      simpa [U'] using hEq'
    exact hbad (section9_factorization_conjBy_back p g hEqConj)
  have htrivial : PeterfalviCentralizersTrivial D t U' := by
    intro x hxU hxne j hjI hjcomm
    by_contra hjne
    let Z : Subgroup X := Subgroup.zpowers x
    have hZne : Z ≠ ⊥ := by
      simpa [Z] using (Subgroup.zpowers_ne_bot.mpr hxne)
    have hZU : Z ≤ U' := by
      simpa [Z] using (Subgroup.zpowers_le.mpr hxU)
    have hjC : j ∈ Subgroup.centralizer (Z : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact ((show Commute j x from hjcomm).zpow_right n).eq.symm
    exact hNoI Z hZne hZU ⟨j, hjI,
      centralizer_le_normalizer Z hjC, hjne⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hU'cyclic : IsCyclic U' :=
    h43 D t hDodd ht
      (by simpa [D] using inf_rightConjugate_invariant_of_isInvolution M ht)
      (by simpa [D] using hIne) p Fact.out U' hU'p hU'V htrivial
  have hUcyclic : IsCyclic U := eU.isCyclic.mpr hU'cyclic
  have hUPeq : U = Pamb := by
    rcases hUshape with hUnoncyclic | hEq
    · exact False.elim (hUnoncyclic hUcyclic)
    · simpa [Pamb] using hEq
  have hU'card : Nat.card U' = p ^ (Nat.card E).factorization p := by
    calc
      Nat.card U' = Nat.card U := Nat.card_congr eU.symm.toEquiv
      _ = Nat.card Pamb := by rw [hUPeq]
      _ = Nat.card (P : Subgroup E) := by
        simpa [Pamb] using
          Subgroup.card_map_of_injective E.subtype_injective
      _ = p ^ (Nat.card E).factorization p := Sylow.card_eq_multiplicity P
  have hU'subcard : Nat.card (U'.subgroupOf E) =
      p ^ (Nat.card E).factorization p := by
    simpa [natCard_subgroupOf_eq U' E hU'E] using hU'card
  let P' : Sylow p E := Sylow.ofCard (U'.subgroupOf E) hU'subcard
  have hP'map : (P' : Subgroup E).map E.subtype = U' := by
    change (U'.subgroupOf E).map E.subtype = U'
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hU'E]
  refine ⟨P', ?_, ?_, ?_⟩
  · let eP : P' ≃* U' :=
      (Subgroup.equivMapOfInjective (P' : Subgroup E) E.subtype
        E.subtype_injective).trans (MulEquiv.subgroupCongr hP'map)
    exact eP.isCyclic.mpr hU'cyclic
  · rw [hP'map]
    exact hU'V
  · simpa [hP'map, D, E] using htrivial

end CFSG.BenderSuzuki
