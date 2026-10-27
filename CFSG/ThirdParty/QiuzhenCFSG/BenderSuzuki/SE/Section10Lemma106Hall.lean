module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Support

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.6: Hall-prime argument

This module proves the prime-by-prime Hall-subgroup half of Lemma 10.6.  It
first proves Peterfalvi `[II1; 4.2]` from the odd-order decomposition and
coprime Hall action, then combines it with the checked Lemma 10.1, Lemma 10.5,
and `[IG; 11.14]` interfaces.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public theorem lemma106_prime_not_dvd_pred_of_dvd_two_pow_sub_one
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrne2 : r ≠ 2)
    (hrpow : r ∣ 2 ^ p - 1) :
    ¬ r ∣ p - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact r.Prime := ⟨hr⟩
  have htwo_ne_zero : (2 : ZMod r) ≠ 0 := by
    intro hzero
    have hrdvd2 : r ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 r).1 (by simpa using hzero)
    rcases (Nat.dvd_prime Nat.prime_two).mp hrdvd2 with hrone | hrtwo
    · exact hr.ne_one hrone
    · exact hrne2 hrtwo
  let z : (ZMod r)ˣ := Units.mk0 2 htwo_ne_zero
  have hmod : 2 ^ p ≡ 1 [MOD r] := by
    have hone_le : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by omega)
    exact ((Nat.modEq_iff_dvd' (n := r) hone_le).2 hrpow).symm
  have hzpow : z ^ p = 1 := by
    apply Units.ext
    change (2 : ZMod r) ^ p = 1
    simpa [Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff (2 ^ p) 1 r).2 hmod
  have hzne : z ≠ 1 := by
    intro hz
    have hcast : (2 : ZMod r) = 1 := by
      simpa [z] using congrArg (fun w : (ZMod r)ˣ => (w : ZMod r)) hz
    have hmod21 : 2 ≡ 1 [MOD r] :=
      (ZMod.natCast_eq_natCast_iff 2 1 r).1 (by simpa using hcast)
    have hrdvd1 : r ∣ 1 := by
      simpa using
        (Nat.modEq_iff_dvd' (n := r) (by omega : 1 ≤ 2)).1 hmod21.symm
    exact hr.not_dvd_one hrdvd1
  have hzorder : orderOf z = p := orderOf_eq_prime hzpow hzne
  have hpdvdr : p ∣ r - 1 := by
    simpa [hzorder] using ZMod.orderOf_units_dvd_card_sub_one z
  intro hrdvdp
  have hp_one_lt : 1 < p := hp.one_lt
  have hr_one_lt : 1 < r := hr.one_lt
  have hrgt : 0 < r - 1 := by omega
  have hpgt : 0 < p - 1 := by omega
  have hple : p ≤ r - 1 := Nat.le_of_dvd hrgt hpdvdr
  have hrle : r ≤ p - 1 := Nat.le_of_dvd hpgt hrdvdp
  omega

/-- A checked `[IG; 11.21]` adapter for the actual Lemma 10.6 subgroups:
there is a `P`-invariant Sylow `r`-subgroup of `A`. -/
public theorem lemma106_exists_P_invariant_sylow_A
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (r : ℕ) (hr : r.Prime) :
    let A := d.choice.initial.A1
    let P := d.choice.P
    ∃ R : Subgroup X,
      theorem4bIsSylowSubgroupOf r R A ∧
        R ≤ A ∧ P ≤ Subgroup.normalizer (R : Set X) := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  change ∃ R : Subgroup X,
    theorem4bIsSylowSubgroupOf r R A ∧
      R ≤ A ∧ P ≤ Subgroup.normalizer (R : Set X)
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact r.Prime := ⟨hr⟩
  have hPp : IsPGroup p P := by
    obtain ⟨PD, hPDmap⟩ := d.P_sylow_D
    have hPp0 : IsPGroup d.choice.p d.choice.P := by
      rw [hPDmap]
      exact PD.isPGroup'.map D.subtype
    simpa [p, P] using hPp0
  letI : Fact (IsPGroup p P) := ⟨hPp⟩
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hPnormA : P ≤ Subgroup.normalizer (A : Set X) := by
    exact d.choice.P_le_V.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp
        d.choice.initial.A1_normal_V)
  letI : Subgroup.Normalizes P A := ⟨hPnormA⟩
  letI : MulDistribMulAction P A :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P A hPnormA
  have hpAcop : Nat.Coprime p (Nat.card A) := by
    have hAeq : A = (pPrimeCore p V).map V.subtype := by
      simpa [p, A, V] using d.A1_eq_pPrimeCore
    have hcardA : Nat.card A = Nat.card (pPrimeCore p V) := by
      rw [hAeq, Subgroup.card_map_of_injective V.subtype_injective]
    rw [hcardA]
    exact pPrimeCore_coprime_card
  obtain ⟨S, hSinv⟩ :=
    exists_invariant_sylow (G := A) (A := P) (p := p) (q := r) hpAcop
  let R : Subgroup X := (S : Subgroup A).map A.subtype
  have hRA : R ≤ A := Subgroup.map_subtype_le (S : Subgroup A)
  have hPnormR : P ≤ Subgroup.normalizer (R : Set X) := by
    intro x hxP
    apply Subgroup.mem_normalizer_fintype
    intro y hyR
    rcases Subgroup.mem_map.mp hyR with ⟨a, haS, hay⟩
    let xP : P := ⟨x, hxP⟩
    have hxaS : xP • a ∈ (S : Subgroup A) :=
      (hSinv.invariant xP a).1 haS
    apply Subgroup.mem_map.mpr
    refine ⟨xP • a, hxaS, ?_⟩
    calc
      ((xP • a : A) : X) = (xP : X) * (a : X) * (xP : X)⁻¹ :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe P A xP a
      _ = x * y * x⁻¹ := by
        change (a : X) = y at hay
        rw [hay]
  exact ⟨R, ⟨S, rfl⟩, hRA, hPnormR⟩

/-- The orbit-congruence glue for the Peterfalvi anti-fixed set. -/
public theorem lemma106_kset_card_modEq_centralizer
    {X : Type u} [Group X] [Finite X]
    {D R : Subgroup X} {t : X} {r : ℕ}
    (hr : r.Prime) (hRp : IsPGroup r R)
    (hRV : R ≤ peterfalviV D t) :
    Nat.card {x : X // x ∈ peterfalviKSet D t} ≡
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} [MOD r] := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let I := {x : X // x ∈ peterfalviKSet D t}
  let conjI : R → I → I := fun a x =>
    ⟨(a : X) * (x : X) * (a : X)⁻¹,
      peterfalviKSet_conj_mem_of_mem_V (hRV a.property) x.property⟩
  letI : MulAction R I :=
    { smul := conjI
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : X) * (x : X) * (1 : X)⁻¹ = (x : X)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change ((a : X) * (b : X)) * (x : X) *
            ((a : X) * (b : X))⁻¹ =
          (a : X) * ((b : X) * (x : X) * (b : X)⁻¹) * (a : X)⁻¹
        group }
  let fixedEquiv : MulAction.fixedPoints R I ≃
      {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} :=
    { toFun := fun x => ⟨(x.1 : X), x.1.property, by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        let aR : R := ⟨a, ha⟩
        have hfix := MulAction.mem_fixedPoints.mp x.2 aR
        have hval := congrArg Subtype.val hfix
        change a * (x.1 : X) * a⁻¹ = (x.1 : X) at hval
        have hmul := congrArg (fun z : X => z * a) hval
        simpa [mul_assoc] using hmul⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        rw [MulAction.mem_fixedPoints]
        intro a
        apply Subtype.ext
        change (a : X) * x.1 * (a : X)⁻¹ = x.1
        have hcomm := Subgroup.mem_centralizer_iff.mp x.2.2
          (a : X) a.property
        calc
          (a : X) * x.1 * (a : X)⁻¹ = x.1 * (a : X) * (a : X)⁻¹ := by
            rw [hcomm]
          _ = x.1 := by simp⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    Nat.card {x : X // x ∈ peterfalviKSet D t} = Nat.card I := rfl
    _ ≡ Nat.card (MulAction.fixedPoints R I) [MOD r] :=
      hRp.card_modEq_card_fixedPoints I
    _ = Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} := Nat.card_congr fixedEquiv

/-- The exclusion direction of the Hall-prime argument: every prime divisor
of `C_A(P)` belongs to the source set `pi`.  The only source callback is the
prime-transfer consequence of `[II1; 4.2]`. -/
public theorem lemma106_prime_mem_pi_of_dvd_C
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (hCcard : Nat.card
      (d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X) :
        Subgroup X) ∣
        d.choice.p - 1)
    (r : Nat.Primes)
    (hrC : r.val ∣ Nat.card
      (d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X) :
        Subgroup X)) :
    r ∈ lemma106Pi d := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let C : Subgroup X := A ⊓ Subgroup.centralizer (P : Set X)
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact r.val.Prime := ⟨r.property⟩
  have hA_V : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hC_A : C ≤ A := inf_le_left
  have hC_D : C ≤ D := hC_A.trans (hA_V.trans inf_le_left)
  have hrC' : r.val ∣ Nat.card C := by
    simpa [C, A, P] using hrC
  have hCcard' : Nat.card C ∣ p - 1 := by
    simpa [C, A, P, p] using hCcard
  have hrD : r.val ∣ Nat.card D := by
    exact hrC'.trans (Subgroup.card_dvd_of_le hC_D)
  have hrmemC : r ∈ subgroupPrimeSet C := by
    simpa [subgroupPrimeSet, C] using hrC
  have hrnep : r.val ≠ p := by
    simpa [C, p, P, A] using d.prime_ne_selected_of_mem_C hrmemC
  refine ⟨hrD, hrnep, ?_⟩
  intro hrK
  obtain ⟨R, hRsylA, hR_A, hPnormR⟩ :=
    lemma106_exists_P_invariant_sylow_A d r.val r.property
  obtain ⟨RA, hRAmap⟩ := hRsylA
  have hrA : r.val ∣ Nat.card A := by
    exact hrC'.trans (Subgroup.card_dvd_of_le hC_A)
  have hRAne : (RA : Subgroup A) ≠ ⊥ := RA.ne_bot_of_dvd_card hrA
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRAne
    apply Subgroup.map_injective A.subtype_injective
    rw [← hRAmap]
    simp [hRbot]
  have hRp : IsPGroup r.val R := by
    rw [hRAmap]
    exact RA.isPGroup'.map A.subtype
  have hR_V : R ≤ V := hR_A.trans hA_V
  have hmod := lemma106_kset_card_modEq_centralizer
    r.property hRp hR_V
  have hsetR :
      {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (R : Set X)} =
        (d.choice.initial.J : Set X) := by
    calc
      {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (R : Set X)} =
          {x : X | x ∈ peterfalviKSet D t ∧
            x ∈ Subgroup.centralizer (A : Set X)} := by
              simpa [A, P] using d.centralizer_uniform R hR_A hRne hPnormR
      _ = (d.choice.initial.J : Set X) := by
        simpa [A] using d.centralizer_A1.symm
  have hfixedCard :
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (R : Set X)} =
        Nat.card d.choice.initial.J := by
    change Nat.card ({x : X | x ∈ peterfalviKSet D t ∧
      x ∈ Subgroup.centralizer (R : Set X)} : Set X) =
      Nat.card (d.choice.initial.J : Set X)
    exact Nat.card_congr (Set.equivOfEq hsetR)
  have hmod' :
      Nat.card {x : X // x ∈ peterfalviKSet D t} ≡
        2 ^ p - 1 [MOD r.val] := by
    rw [hfixedCard] at hmod
    calc
      Nat.card {x : X // x ∈ peterfalviKSet D t} ≡
          Nat.card d.choice.initial.J [MOD r.val] := hmod
      _ = 2 ^ p - 1 := by simpa [p] using d.centralizer_A1_card
  have hrI : r.val ∣ Nat.card {x : X // x ∈ peterfalviKSet D t} :=
    h42 D t hDodd ht hDnorm r.val r.property (by simpa [K] using hrK)
  have hrpow : r.val ∣ 2 ^ p - 1 :=
    (hmod'.dvd_iff (dvd_refl r.val)).1 hrI
  have hrne2 : r.val ≠ 2 := by
    intro hr2
    have hoddPow : Odd (2 ^ p - 1) := by
      exact Nat.Even.sub_odd (Nat.one_le_pow p 2 (by omega))
        (by simp [Nat.even_pow, hp.ne_zero]) (by simp)
    exact hoddPow.not_two_dvd_nat (by simpa [hr2] using hrpow)
  have hrnotpred : ¬ r.val ∣ p - 1 :=
    lemma106_prime_not_dvd_pred_of_dvd_two_pow_sub_one
      hp r.property hrne2 hrpow
  apply hrnotpred
  exact hrC'.trans hCcard'

/-- Cardinality of a subgroup represented as a disjoint set product. -/
public theorem lemma106_natCard_eq_mul_of_set_mul_disjoint
    {X : Type u} [Group X] [Finite X]
    {N C P : Subgroup X}
    (hset : (N : Set X) = (C : Set X) * (P : Set X))
    (hdisj : Disjoint C P) :
    Nat.card N = Nat.card C * Nat.card P := by
  let f : C × P → N := fun z =>
    ⟨(z.1 : X) * (z.2 : X), by
      change (z.1 : X) * (z.2 : X) ∈ (N : Set X)
      rw [hset]
      exact Set.mem_mul.mpr ⟨z.1, z.1.property, z.2, z.2.property, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subgroup.mul_injective_of_disjoint hdisj
      (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : X) ∈ (C : Set X) * (P : Set X) := by
      rw [← hset]
      exact x.property
    rcases Set.mem_mul.mp hx with ⟨c, hc, p, hp, hcp⟩
    exact ⟨(⟨c, hc⟩, ⟨p, hp⟩), Subtype.ext hcp⟩
  calc
    Nat.card N = Nat.card (C × P) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
    _ = Nat.card C * Nat.card P := Nat.card_prod C P

/-- The `[IG; 11.14]` direction after the exclusion half has shown that
`C_A(P)` is a `pi`-group.  Every `P`-invariant subgroup of `A` then
centralizes `P`. -/
public theorem lemma106_invariant_subgroup_le_C
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (h97 : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (hCpi : ∀ q : Nat.Primes,
      q.val ∣ Nat.card
        (d.choice.initial.A1 ⊓ Subgroup.centralizer (d.choice.P : Set X) :
          Subgroup X) →
      q ∈ lemma106Pi d)
    (q : Nat.Primes)
    (hqPi : q ∈ lemma106Pi d)
    (R : Subgroup X)
    (hRq : IsPGroup q.val R)
    (hR_A : R ≤ d.choice.initial.A1)
    (hPnormR : d.choice.P ≤ Subgroup.normalizer (R : Set X)) :
    R ≤ d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X) := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let C : Subgroup X := A ⊓ Subgroup.centralizer (P : Set X)
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let N : Subgroup X := normalizerIn D P
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.val.Prime := ⟨q.property⟩
  have hA_V : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hK_D : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hP_D : P ≤ D := d.choice.P_le_V.trans inf_le_left
  have hPp : IsPGroup p P := by
    exact IsPGroup.of_card (n := 1) (by simpa [p, P] using d.P_card)
  have hR_V : R ≤ V := hR_A.trans hA_V
  have hR_D : R ≤ D := hR_V.trans inf_le_left
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_D).mp hKnormalD
  have hRPnormK : R ⊔ P ≤ Subgroup.normalizer (K : Set X) :=
    (sup_le hR_D hP_D).trans hDnormK
  have hpKA : Nat.Coprime p (Nat.card (K ⊔ A : Subgroup X)) := by
    have hKA := d.kernel_sup_A1_eq_pPrimeCore
    have hcard : Nat.card (K ⊔ A : Subgroup X) =
        Nat.card (pPrimeCore p D) := by
      rw [show K ⊔ A = (pPrimeCore p D).map D.subtype by
        simpa [K, A, p] using hKA,
        Subgroup.card_map_of_injective D.subtype_injective]
    rw [hcard]
    exact pPrimeCore_coprime_card
  have hpK : Nat.Coprime p (Nat.card K) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le le_sup_left) hpKA
  have hCK : Nat.Coprime (Nat.card C) (Nat.card K) := by
    apply Nat.coprime_of_dvd
    intro q hq hqC hqK
    let q' : Nat.Primes := ⟨q, hq⟩
    have hqPi : q' ∈ lemma106Pi d := by
      apply hCpi q'
      simpa [C, A, P] using hqC
    exact hqPi.2.2 hqK
  have hKcopC : Nat.Coprime (Nat.card K) (Nat.card C) := hCK.symm
  have hKcopP : Nat.Coprime (Nat.card K) (Nat.card P) := by
    simpa [p, P, d.P_card] using hpK.symm
  have hNcard : Nat.card N = Nat.card C * Nat.card P := by
    exact lemma106_natCard_eq_mul_of_set_mul_disjoint
      (by simpa [N, C, P, A] using d.normalizer_factorization.2.1)
      (by simpa [C, P, A] using d.normalizer_factorization.2.2)
  have hKcopN : Nat.Coprime (Nat.card K) (Nat.card N) := by
    rw [hNcard]
    exact hKcopC.mul_right hKcopP
  have hKNbot : K ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime hKcopN
  have hCKP : subgroupCentralizerIn K P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN : x ∈ N := by
      exact ⟨hK_D hx.1, centralizer_le_normalizer P hx.2⟩
    have hxKN : x ∈ K ⊓ N := ⟨hx.1, hxN⟩
    rw [hKNbot] at hxKN
    exact hxKN
  have hoddRP : Odd (Nat.card (R ⊔ P : Subgroup X)) :=
    hDodd.of_dvd_nat
      (Subgroup.card_dvd_of_le (sup_le hR_D hP_D))
  have hcopPR : Nat.Coprime (Nat.card P) (Nat.card R) :=
    (IsPGroup.coprime_card_of_ne q.val p hqPi.2.1 R P hRq hPp).symm
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    obtain ⟨n, hRcard⟩ := hRq.exists_card_eq
    rw [hRcard]
    exact (q.property.coprime_pow_of_not_dvd hqPi.2.2).symm
  have hPprime : Nat.Prime (Nat.card P) := by
    simpa [p, P, d.P_card] using hp
  have hcommK : ⁅R, P⁆ ≤ Subgroup.centralizer (K : Set X) :=
    ig1114_i_commutator_le_centralizer_of_fixedPointFree K R P
      (by simpa [P] using hPnormR) hRPnormK hoddRP hcopPR hcopRK
      hKcopP.symm hPprime hCKP
  have hcommV : ⁅R, P⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro r hrR q hqP
    have hrV := hR_V hrR
    have hqV := d.choice.P_le_V hqP
    exact V.mul_mem
      (V.mul_mem (V.mul_mem hrV hqV) (V.inv_mem hrV)) (V.inv_mem hqV)
  have hcommI : ⁅R, P⁆ ≤
      Subgroup.centralizer (peterfalviKSet D t) := by
    simpa [K, Subgroup.centralizer_closure] using hcommK
  have hcommbot : ⁅R, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← h97]
    exact le_inf hcommV hcommI
  have hRcentP : R ≤ Subgroup.centralizer (P : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
  simpa [A, P] using le_inf hR_A hRcentP

/-- If a normal subgroup and a second subgroup generate the ambient group,
the index of the second subgroup divides the order of the normal factor. -/
public theorem lemma106_index_dvd_card_of_sup_eq_top_normal
    {Q : Type u} [Group Q] [Finite Q]
    {K U : Subgroup Q} [K.Normal]
    (hKU : K ⊔ U = ⊤) :
    U.index ∣ Nat.card K := by
  have hrel_eq :
      U.relIndex (U ⊔ K) = (U ⊓ K).relIndex K := by
    have hK_rel :
        K.relIndex (U ⊔ K) = (U ⊓ K).relIndex U := by
      calc
        K.relIndex (U ⊔ K) = K.relIndex U := by simp
        _ = (U ⊓ K).relIndex U := by
          symm
          simpa [inf_comm] using
            (Subgroup.inf_relIndex_left (H := U) (K := K))
    have hmul :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
      calc
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
            (U ⊓ K).relIndex (U ⊔ K) := by
          exact Subgroup.relIndex_mul_relIndex
            (H := U ⊓ K) (K := U) (L := U ⊔ K)
            inf_le_left le_sup_left
        _ = (U ⊓ K).relIndex K * K.relIndex (U ⊔ K) := by
          symm
          exact Subgroup.relIndex_mul_relIndex
            (H := U ⊓ K) (K := K) (L := U ⊔ K)
            inf_le_right le_sup_right
        _ = (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
          rw [hK_rel]
    have hrel_pos : 0 < (U ⊓ K).relIndex U := by
      have hrel_ne_zero : (U ⊓ K).relIndex U ≠ 0 := by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
          (H := (U ⊓ K).subgroupOf U)
      exact Nat.pos_of_ne_zero hrel_ne_zero
    have hmul' :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex U * (U ⊓ K).relIndex K := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hrel_pos hmul'
  have hidx_eq : U.relIndex (U ⊔ K) = U.index := by
    rw [show U ⊔ K = ⊤ by simpa [sup_comm] using hKU]
    exact Subgroup.relIndex_top_right (H := U)
  have hrel_dvd_cardK : U.relIndex (U ⊔ K) ∣ Nat.card K := by
    rw [hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := U ⊓ K) (K := K)
  simpa [hidx_eq] using hrel_dvd_cardK

/-- A Sylow subgroup of the second factor remains Sylow after adjoining a
normal factor whose order is coprime to the Sylow prime. -/
public theorem lemma106_sylow_of_normal_factor
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} (hr : r.Prime)
    {K A R N : Subgroup X}
    (hKN : K ≤ N) (hAN : A ≤ N)
    (hKnormal : (K.subgroupOf N).Normal)
    (hKA : K.subgroupOf N ⊔ A.subgroupOf N = ⊤)
    (hRA : theorem4bIsSylowSubgroupOf r R A)
    (hRleA : R ≤ A)
    (hrK : ¬ r ∣ Nat.card K) :
    theorem4bIsSylowSubgroupOf r R N := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let KN : Subgroup N := K.subgroupOf N
  let AN : Subgroup N := A.subgroupOf N
  letI : KN.Normal := by simpa [KN] using hKnormal
  have hAidx_dvd : AN.index ∣ Nat.card KN := by
    exact lemma106_index_dvd_card_of_sup_eq_top_normal
      (by simpa [KN, AN] using hKA)
  have hcardKN : Nat.card KN = Nat.card K := by
    simpa [KN] using natCard_subgroupOf_eq K N hKN
  have hrAidx : ¬ r ∣ AN.index := by
    intro h
    apply hrK
    rw [← hcardKN]
    exact h.trans hAidx_dvd
  obtain ⟨RA, hRAmap⟩ := hRA
  have hRAsub : R.subgroupOf A = (RA : Subgroup A) := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleA]
    exact hRAmap
  have hrRAidx : ¬ r ∣ (R.subgroupOf A).index := by
    rw [hRAsub]
    exact RA.not_dvd_index
  have hRleN : R ≤ N := hRleA.trans hAN
  have hchain : R.relIndex A * A.relIndex N = R.relIndex N :=
    Subgroup.relIndex_mul_relIndex R A N hRleA hAN
  have hANidx : AN.index = A.relIndex N := rfl
  have hRidx : ¬ r ∣ (R.subgroupOf N).index := by
    change ¬ r ∣ R.relIndex N
    rw [← hchain]
    intro hd
    rcases hr.dvd_mul.mp hd with h1 | h2
    · exact hrRAidx h1
    · exact hrAidx (by simpa [hANidx] using h2)
  have hRp : IsPGroup r R := by
    rw [hRAmap]
    exact RA.isPGroup'.map A.subtype
  have hRNp : IsPGroup r (R.subgroupOf N) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRleN).symm
  let RN : Sylow r N := hRNp.toSylow hRidx
  refine ⟨RN, ?_⟩
  change R = (RN : Subgroup N).map N.subtype
  rw [show (RN : Subgroup N) = R.subgroupOf N by
    exact IsPGroup.toSylow_coe hRNp hRidx]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleN]

/-- A Sylow subgroup of a normal subgroup remains Sylow after adjoining a
factor whose order is coprime to the Sylow prime. -/
public theorem lemma106_sylow_of_normal_subgroup_sup
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} (hr : r.Prime)
    {K U R N : Subgroup X}
    (hKN : K ≤ N) (hUN : U ≤ N)
    (hKnormal : (K.subgroupOf N).Normal)
    (hKU : K.subgroupOf N ⊔ U.subgroupOf N = ⊤)
    (hRK : theorem4bIsSylowSubgroupOf r R K)
    (hRleK : R ≤ K)
    (hrU : ¬ r ∣ Nat.card U) :
    theorem4bIsSylowSubgroupOf r R N := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let KN : Subgroup N := K.subgroupOf N
  let UN : Subgroup N := U.subgroupOf N
  letI : KN.Normal := by simpa [KN] using hKnormal
  have hKidx_dvd : KN.index ∣ Nat.card UN := by
    have hidx : KN.index = (KN ⊓ UN).relIndex UN := by
      calc
        KN.index = KN.relIndex (⊤ : Subgroup N) :=
          (Subgroup.relIndex_top_right (H := KN)).symm
        _ = KN.relIndex (KN ⊔ UN) := by rw [hKU]
        _ = KN.relIndex UN := by simp
        _ = (KN ⊓ UN).relIndex UN := by
          symm
          exact Subgroup.inf_relIndex_right KN UN
    rw [hidx]
    exact Subgroup.relIndex_dvd_card (H := KN ⊓ UN) (K := UN)
  have hcardUN : Nat.card UN = Nat.card U := by
    simpa [UN] using natCard_subgroupOf_eq U N hUN
  have hrKidx : ¬ r ∣ KN.index := by
    intro h
    apply hrU
    rw [← hcardUN]
    exact h.trans hKidx_dvd
  obtain ⟨RK, hRKmap⟩ := hRK
  have hRKsub : R.subgroupOf K = (RK : Subgroup K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleK]
    exact hRKmap
  have hrRKidx : ¬ r ∣ (R.subgroupOf K).index := by
    rw [hRKsub]
    exact RK.not_dvd_index
  have hRleN : R ≤ N := hRleK.trans hKN
  have hchain : R.relIndex K * K.relIndex N = R.relIndex N :=
    Subgroup.relIndex_mul_relIndex R K N hRleK hKN
  have hKNidx : KN.index = K.relIndex N := rfl
  have hRidx : ¬ r ∣ (R.subgroupOf N).index := by
    change ¬ r ∣ R.relIndex N
    rw [← hchain]
    intro hd
    rcases hr.dvd_mul.mp hd with h1 | h2
    · exact hrRKidx h1
    · exact hrKidx (by simpa [hKNidx] using h2)
  have hRp : IsPGroup r R := by
    rw [hRKmap]
    exact RK.isPGroup'.map K.subtype
  have hRNp : IsPGroup r (R.subgroupOf N) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRleN).symm
  let RN : Sylow r N := hRNp.toSylow hRidx
  refine ⟨RN, ?_⟩
  change R = (RN : Subgroup N).map N.subtype
  rw [show (RN : Subgroup N) = R.subgroupOf N by
    exact IsPGroup.toSylow_coe hRNp hRidx]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleN]

/-- For a prime in the source set `pi`, the invariant Sylow subgroup chosen
inside `A` is already Sylow in `D`.  This is the prime-by-prime bookkeeping
needed for the Hall-index half of Lemma 10.6. -/
public theorem lemma106_exists_P_invariant_sylow_D
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (r : Nat.Primes)
    (hrPi : r ∈ lemma106Pi d) :
    ∃ R : Subgroup X,
      theorem4bIsSylowSubgroupOf r.val R D ∧
        R ≤ d.choice.initial.A1 ∧
        d.choice.P ≤ Subgroup.normalizer (R : Set X) := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let N : Subgroup X := K ⊔ A
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  have hK_D : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hA_V : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hV_D : V ≤ D := inf_le_left
  have hA_D : A ≤ D := hA_V.trans hV_D
  have hP_D : P ≤ D := d.choice.P_le_V.trans hV_D
  have hK_N : K ≤ N := le_sup_left
  have hA_N : A ≤ N := le_sup_right
  have hN_D : N ≤ D := sup_le hK_D hA_D
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_D).mp hKnormalD
  have hKnormalN : (K.subgroupOf N).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK_N).mpr
      (hN_D.trans hDnormK)
  have hKAsup : K.subgroupOf N ⊔ A.subgroupOf N = ⊤ := by
    calc
      K.subgroupOf N ⊔ A.subgroupOf N = (K ⊔ A).subgroupOf N :=
        (Subgroup.subgroupOf_sup hK_N hA_N).symm
      _ = ⊤ := by simp [N]
  obtain ⟨R, hRsylA, hR_A, hPnormR⟩ :=
    lemma106_exists_P_invariant_sylow_A d r.val r.property
  have hRsylN : theorem4bIsSylowSubgroupOf r.val R N :=
    lemma106_sylow_of_normal_factor r.property
      hK_N hA_N hKnormalN hKAsup hRsylA hR_A hrPi.2.2
  have hNeq :
      N = (pPrimeCore p D).map D.subtype := by
    simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
  have hNsub : N.subgroupOf D = pPrimeCore p D := by
    rw [hNeq]
    exact subgroupOf_map_subtype_eq (pPrimeCore p D)
  have hNnormalD : (N.subgroupOf D).Normal := by
    rw [hNsub]
    exact pPrimeCore_normal
  have hNsupP : N ⊔ P = D := by
    apply le_antisymm
    · exact sup_le hN_D hP_D
    · intro x hxD
      have hxprod :
          x ∈ (K : Set X) * (A : Set X) * (P : Set X) := by
        rw [← d.D_eq_kernel_mul_A1_mul_P]
        exact hxD
      rcases Set.mem_mul.mp hxprod with ⟨ka, hka, q, hqP, hkaq⟩
      rcases Set.mem_mul.mp hka with ⟨k, hkK, a, haA, hka⟩
      rw [← hkaq, ← hka]
      exact (N ⊔ P).mul_mem
        ((N ⊔ P).mul_mem
          ((le_sup_left : N ≤ N ⊔ P) (hK_N hkK))
          ((le_sup_left : N ≤ N ⊔ P) (hA_N haA)))
        ((le_sup_right : P ≤ N ⊔ P) hqP)
  have hNPsup : N.subgroupOf D ⊔ P.subgroupOf D = ⊤ := by
    calc
      N.subgroupOf D ⊔ P.subgroupOf D = (N ⊔ P).subgroupOf D :=
        (Subgroup.subgroupOf_sup hN_D hP_D).symm
      _ = D.subgroupOf D := by rw [hNsupP]
      _ = ⊤ := Subgroup.subgroupOf_self D
  have hrP : ¬ r.val ∣ Nat.card P := by
    intro hrPcard
    have hrdvp : r.val ∣ p := by
      simpa [P, p, d.P_card] using hrPcard
    rcases (Nat.dvd_prime hp).mp hrdvp with hrone | hrp
    · exact r.property.ne_one hrone
    · exact hrPi.2.1 hrp
  have hRsylD : theorem4bIsSylowSubgroupOf r.val R D :=
    lemma106_sylow_of_normal_subgroup_sup r.property
      hN_D hP_D hNnormalD hNPsup hRsylN (hR_A.trans hA_N) hrP
  exact ⟨R, hRsylD, hR_A, hPnormR⟩

/-- The complete Hall-subgroup half of source Lemma 10.6. -/
public theorem lemma106_C_isHall
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (h97 : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (hCcard : Nat.card (lemma104C d) ∣ d.choice.p - 1) :
    IsHallSubgroup (lemma106Pi d)
      ((lemma104C d).subgroupOf D) := by
  classical
  let C : Subgroup X := lemma104C d
  have hA_V : d.choice.initial.A1 ≤ peterfalviV D t := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hA_D : d.choice.initial.A1 ≤ D := hA_V.trans inf_le_left
  have hC_D : C ≤ D := by
    exact (show C ≤ d.choice.initial.A1 by simp [C, lemma104C]).trans hA_D
  have hCpi : ∀ q : Nat.Primes, q.val ∣ Nat.card C →
      q ∈ lemma106Pi d := by
    intro q hq
    exact lemma106_prime_mem_pi_of_dvd_C d hDodd ht hDnorm h42
      (by simpa [lemma104C] using hCcard) q
      (by simpa [C, lemma104C] using hq)
  refine isHallSubgroup_of
    (G := D) (π := lemma106Pi d)
    (H := C.subgroupOf D) ?_ ?_
  · intro q hq
    apply hCpi q
    simpa [natCard_subgroupOf_eq C D hC_D] using hq
  · intro q hqPi hqIndex
    letI : Fact q.val.Prime := ⟨q.property⟩
    obtain ⟨R, hRsylD, hR_A, hPnormR⟩ :=
      lemma106_exists_P_invariant_sylow_D d hDodd ht hDnorm q hqPi
    obtain ⟨RD, hRDmap⟩ := hRsylD
    have hRq : IsPGroup q.val R := by
      rw [hRDmap]
      exact RD.isPGroup'.map D.subtype
    have hR_C : R ≤ C := by
      simpa [C, lemma104C] using lemma106_invariant_subgroup_le_C d hDodd ht
        hDnorm h97 hCpi q hqPi R hRq hR_A hPnormR
    have hRsub_eq : R.subgroupOf D = (RD : Subgroup D) := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hR_C.trans hC_D)]
      exact hRDmap
    have hRsub_le_Csub : R.subgroupOf D ≤ C.subgroupOf D := by
      intro x hx
      exact hR_C hx
    have hCindex_dvd_Rindex : (C.subgroupOf D).index ∣
        (R.subgroupOf D).index :=
      Subgroup.index_dvd_of_le hRsub_le_Csub
    have hqRindex : q.val ∣ (R.subgroupOf D).index :=
      hqIndex.trans hCindex_dvd_Rindex
    rw [hRsub_eq] at hqRindex
    exact RD.not_dvd_index hqRindex


end CFSG.BenderSuzuki
