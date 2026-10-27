module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Reflection probe for the finite `S₄` certificate

The production theorem uses one monolithic `decide` over structured
permutations.  This probe instead encodes `S₄` as `Fin 4 × Fin 3 × Fin 2`,
evaluates permutation expressions pointwise, and proves a Boolean checker
sound before using it in the theorem proof.
-/

namespace CFSG.GorensteinWalter

private abbrev S4Code := Fin 4 × Fin 3 × Fin 2

private def s2Decode (k : Fin 2) : Equiv.Perm (Fin 2) :=
  Equiv.Perm.decomposeFin.symm (k, 1)

private def s3Decode (c : Fin 3 × Fin 2) : Equiv.Perm (Fin 3) :=
  Equiv.Perm.decomposeFin.symm (c.1, s2Decode c.2)

private def s4Decode (c : S4Code) : Equiv.Perm (Fin 4) :=
  Equiv.Perm.decomposeFin.symm (c.1, s3Decode c.2)

private def s4Encode (p : Equiv.Perm (Fin 4)) : S4Code :=
  let p4 := Equiv.Perm.decomposeFin p
  let p3 := Equiv.Perm.decomposeFin p4.2
  let p2 := Equiv.Perm.decomposeFin p3.2
  (p4.1, p3.1, p2.1)

private theorem s4Decode_encode (p : Equiv.Perm (Fin 4)) :
    s4Decode (s4Encode p) = p := by
  let p4 := Equiv.Perm.decomposeFin p
  let p3 := Equiv.Perm.decomposeFin p4.2
  let p2 := Equiv.Perm.decomposeFin p3.2
  change Equiv.Perm.decomposeFin.symm
      (p4.1, Equiv.Perm.decomposeFin.symm
        (p3.1, Equiv.Perm.decomposeFin.symm (p2.1, 1))) = p
  rw [show (1 : Equiv.Perm (Fin 1)) = p2.2 from Subsingleton.elim _ _]
  simp [p4, p3, p2]

private theorem s4Encode_decode (c : S4Code) :
    s4Encode (s4Decode c) = c := by
  simp only [s4Decode, s3Decode, s2Decode, s4Encode, Equiv.apply_symm_apply]

private def s2Act (k : Fin 2) (x : Fin 2) : Fin 2 :=
  Equiv.swap 0 k x

private theorem s2Act_eq_decode (k : Fin 2) (x : Fin 2) :
    s2Act k x = s2Decode k x := by
  simp [s2Act, s2Decode]

private def s3Act (j : Fin 3) (k : Fin 2) (x : Fin 3) : Fin 3 :=
  Fin.cases j (fun y => Equiv.swap 0 j (Fin.succ (s2Act k y))) x

private theorem s3Act_eq_decode (j : Fin 3) (k : Fin 2) (x : Fin 3) :
    s3Act j k x = s3Decode (j, k) x := by
  refine Fin.cases ?_ (fun y => ?_) x
  · simp [s3Act, s3Decode]
  · simp [s3Act, s3Decode, s2Act_eq_decode]

private def s4Act (c : S4Code) (x : Fin 4) : Fin 4 :=
  Fin.cases c.1
    (fun y => Equiv.swap 0 c.1 (Fin.succ (s3Act c.2.1 c.2.2 y))) x

private theorem s4Act_eq_decode (c : S4Code) (x : Fin 4) :
    s4Act c x = s4Decode c x := by
  refine Fin.cases ?_ (fun y => ?_) x
  · simp [s4Act, s4Decode]
  · simp [s4Act, s4Decode, s3Act_eq_decode]

private def actionEqB (f g : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all fun i => f i == g i

private theorem actionEqB_eq_true_iff (f g : Fin 4 → Fin 4) :
    actionEqB f g = true ↔ ∀ x, f x = g x := by
  simp [actionEqB]

private theorem actionEqB_eq_false_iff (f g : Fin 4 → Fin 4) :
    actionEqB f g = false ↔ ¬∀ x, f x = g x := by
  constructor
  · intro h hall
    have htrue := (actionEqB_eq_true_iff f g).2 hall
    rw [h] at htrue
    contradiction
  · intro hne
    cases h : actionEqB f g with
    | false => rfl
    | true => exact False.elim (hne ((actionEqB_eq_true_iff f g).1 h))

private def s4PowAct (a : S4Code) : ℕ → Fin 4 → Fin 4
  | 0 => id
  | n + 1 => fun x => s4PowAct a n (s4Act a x)

private theorem s4PowAct_eq_decode_pow (a : S4Code) (n : ℕ) (x : Fin 4) :
    s4PowAct a n x = (s4Decode a ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change s4PowAct a n (s4Act a x) = (s4Decode a ^ (n + 1)) x
      rw [ih, s4Act_eq_decode, pow_succ, Equiv.Perm.mul_apply]

private def allS4 (p : S4Code → Bool) : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 3).all fun j =>
      (List.finRange 2).all fun k => p (i, j, k)

private theorem allS4_eq_true_iff (p : S4Code → Bool) :
    allS4 p = true ↔ ∀ c, p c = true := by
  constructor
  · intro h c
    rcases c with ⟨i, j, k⟩
    simp only [allS4, List.all_eq_true, List.mem_finRange] at h
    exact h i trivial j trivial k trivial
  · intro h
    simpa [allS4] using h

private def boolImp (p q : Bool) : Bool :=
  !p || q

private theorem boolImp_eq_true_iff (p q : Bool) :
    boolImp p q = true ↔ (p = true → q = true) := by
  cases p <;> cases q <;> simp [boolImp]

private def s4OrderPremiseB (n : ℕ) (a : S4Code) : Bool :=
  !actionEqB (s4Act a) id && actionEqB (s4PowAct a n) id

private theorem s4OrderPremiseB_eq_true_iff (n : ℕ) (a : S4Code) :
    s4OrderPremiseB n a = true ↔
      s4Decode a ≠ 1 ∧ s4Decode a ^ n = 1 := by
  rw [s4OrderPremiseB, Bool.and_eq_true]
  constructor
  · rintro ⟨hne, hpow⟩
    have hne' : actionEqB (s4Act a) id = false := by
      cases hEq : actionEqB (s4Act a) id <;> simp_all
    have hnePoint := (actionEqB_eq_false_iff _ _).1 hne'
    have hpowPoint := (actionEqB_eq_true_iff _ _).1 hpow
    constructor
    · intro hEq
      apply hnePoint
      intro x
      rw [s4Act_eq_decode, hEq]
      rfl
    · apply Equiv.ext
      intro x
      rw [← s4PowAct_eq_decode_pow]
      exact hpowPoint x
  · rintro ⟨hne, hpow⟩
    constructor
    · have hfalse : actionEqB (s4Act a) id = false := by
        apply (actionEqB_eq_false_iff _ _).2
        intro hall
        apply hne
        apply Equiv.ext
        intro x
        rw [← s4Act_eq_decode]
        exact hall x
      simp [hfalse]
    · apply (actionEqB_eq_true_iff _ _).2
      intro x
      rw [s4PowAct_eq_decode_pow, hpow]
      rfl

private def s4CommuteB (a b : S4Code) : Bool :=
  actionEqB (fun x => s4Act a (s4Act b x))
    (fun x => s4Act b (s4Act a x))

private theorem s4CommuteB_eq_true_iff (a b : S4Code) :
    s4CommuteB a b = true ↔
      s4Decode a * s4Decode b = s4Decode b * s4Decode a := by
  rw [s4CommuteB, actionEqB_eq_true_iff, Equiv.ext_iff]
  simp only [Equiv.Perm.mul_apply, s4Act_eq_decode]

private def s4ConjugateIntoCyclicThreeB (c a : S4Code) : Bool :=
  actionEqB (fun x => s4Act c (s4Act a x))
      (fun x => s4Act a (s4Act c x)) ||
    actionEqB (fun x => s4Act c (s4Act a x))
      (fun x => s4PowAct a 2 (s4Act c x))

private theorem s4ConjugateIntoCyclicThreeB_eq_true_iff
    (c a : S4Code) :
    s4ConjugateIntoCyclicThreeB c a = true ↔
      s4Decode c * s4Decode a = s4Decode a * s4Decode c ∨
        s4Decode c * s4Decode a = s4Decode a ^ 2 * s4Decode c := by
  simp only [s4ConjugateIntoCyclicThreeB, Bool.or_eq_true,
    actionEqB_eq_true_iff, Equiv.ext_iff, Equiv.Perm.mul_apply,
    s4Act_eq_decode, s4PowAct_eq_decode_pow]

private def s4NormalizerPremiseB (a s : S4Code) : Bool :=
  allS4 fun c => boolImp (s4CommuteB c s) (s4ConjugateIntoCyclicThreeB c a)

private theorem s4NormalizerPremiseB_eq_true_iff (a s : S4Code) :
    s4NormalizerPremiseB a s = true ↔
      ∀ c : S4Code,
        s4Decode c * s4Decode s = s4Decode s * s4Decode c →
          s4Decode c * s4Decode a = s4Decode a * s4Decode c ∨
            s4Decode c * s4Decode a = s4Decode a ^ 2 * s4Decode c := by
  simp only [s4NormalizerPremiseB, allS4_eq_true_iff, boolImp_eq_true_iff,
    s4CommuteB_eq_true_iff, s4ConjugateIntoCyclicThreeB_eq_true_iff]

private def s4CertificateCaseB (a s : S4Code) : Bool :=
  boolImp (s4OrderPremiseB 3 a)
    (boolImp (s4OrderPremiseB 2 s)
      (boolImp (s4NormalizerPremiseB a s) (s4CommuteB a s)))

private theorem s4CertificateCaseB_eq_true_iff (a s : S4Code) :
    s4CertificateCaseB a s = true ↔
      (s4Decode a ≠ 1 ∧ s4Decode a ^ 3 = 1) →
      (s4Decode s ≠ 1 ∧ s4Decode s ^ 2 = 1) →
      (∀ c : S4Code,
        s4Decode c * s4Decode s = s4Decode s * s4Decode c →
          s4Decode c * s4Decode a = s4Decode a * s4Decode c ∨
            s4Decode c * s4Decode a = s4Decode a ^ 2 * s4Decode c) →
      s4Decode a * s4Decode s = s4Decode s * s4Decode a := by
  simp only [s4CertificateCaseB, boolImp_eq_true_iff,
    s4OrderPremiseB_eq_true_iff, s4NormalizerPremiseB_eq_true_iff,
    s4CommuteB_eq_true_iff]

private def s4CertificateB : Bool :=
  allS4 fun a => allS4 fun s => s4CertificateCaseB a s

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private theorem s4CertificateB_true : s4CertificateB = true := by
  rfl

private theorem s4ReflectedCertificate :
    ∀ (a s : Equiv.Perm (Fin 4)),
      (a ≠ 1 ∧ a ^ 3 = 1) → (s ≠ 1 ∧ s ^ 2 = 1) →
      (∀ c : Equiv.Perm (Fin 4), c * s = s * c →
        c * a * c⁻¹ = a ∨ c * a * c⁻¹ = a ^ 2) →
      a * s = s * a := by
  intro a s ha hs hnormalizes
  let ac := s4Encode a
  let sc := s4Encode s
  have hdecodeA : s4Decode ac = a := s4Decode_encode a
  have hdecodeS : s4Decode sc = s := s4Decode_encode s
  have houter : ∀ a, allS4 (fun s => s4CertificateCaseB a s) = true := by
    apply (allS4_eq_true_iff _).1
    simpa only [s4CertificateB] using s4CertificateB_true
  have hcaseB : s4CertificateCaseB ac sc = true :=
    (allS4_eq_true_iff _).1 (houter ac) sc
  have hcase := (s4CertificateCaseB_eq_true_iff ac sc).1 hcaseB
  have hresult := hcase (by simpa only [hdecodeA] using ha)
    (by simpa only [hdecodeS] using hs) (by
    intro cc hcommutes
    have hconj := hnormalizes (s4Decode cc) (by
      simpa only [hdecodeS] using hcommutes)
    rcases hconj with hconj | hconj
    · left
      have hmul := congrArg (fun z => z * s4Decode cc) hconj
      simpa [hdecodeA, mul_assoc] using hmul
    · right
      have hmul := congrArg (fun z => z * s4Decode cc) hconj
      simpa [hdecodeA, mul_assoc] using hmul)
  simpa only [hdecodeA, hdecodeS] using hresult

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem sFour_invariant_oddP_subgroup_centralized_reflection_probe
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (Equiv.Perm (Fin 4))) (hPp : IsPGroup p P)
    {t : Equiv.Perm (Fin 4)} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) ≤
      Subgroup.normalizer (P : Set (Equiv.Perm (Fin 4)))) :
    P ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hGcard : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hPdvd : Fintype.card P ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card P
    simpa [hGcard] using h
  rcases hPp.exists_card_eq with ⟨n, hn⟩
  rw [Nat.card_eq_fintype_card] at hn
  by_cases hnzero : n = 0
  · have hPcard : Nat.card P = 1 := by
      rw [Nat.card_eq_fintype_card, hn, hnzero]
      simp
    have hPbot : P = ⊥ := Subgroup.eq_bot_of_card_eq P hPcard
    intro x hx
    have hxone : x = 1 := by
      rw [hPbot] at hx
      exact Subgroup.mem_bot.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, hxone]
    simp
  · have hpdvd : p ∣ 24 := by
      apply (show p ∣ Fintype.card P from ?_).trans hPdvd
      rw [hn]
      exact dvd_pow_self p hnzero
    have hpeq : p = 3 := by
      have hfactor : 24 = 2 ^ 3 * 3 := by norm_num
      rw [hfactor] at hpdvd
      rcases hp.dvd_mul.mp hpdvd with htwo | hthree
      · have hp2 : p = 2 :=
          Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two htwo
        subst p
        exact False.elim (hpodd.not_two_dvd_nat (by norm_num))
      · exact ((Nat.dvd_prime Nat.prime_three).mp hthree).resolve_left hp.ne_one
    subst p
    have hnle : n ≤ 1 := by
      by_contra hnnot
      have htwo : 2 ≤ n := by omega
      have hbad : 9 ∣ 24 := by
        apply (pow_dvd_pow 3 htwo).trans
        simpa [hn] using hPdvd
      norm_num at hbad
    have hnone : n = 1 := by omega
    have hPcard : Fintype.card P = 3 := by simpa [hnone] using hn
    have hPcardNat : Nat.card P = 3 := by
      rw [Nat.card_eq_fintype_card, hPcard]
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨xP, hxPorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hPcardNat])
    let x : Equiv.Perm (Fin 4) := xP
    have hxorder : orderOf x = 3 := by
      simpa [x, Subgroup.orderOf_coe] using hxPorder
    have hxne : x ≠ 1 := by
      intro hxone
      have : (3 : ℕ) = 1 := by rw [← hxorder, hxone, orderOf_one]
      norm_num at this
    have hxpow : x ^ 3 = 1 := by
      rw [← hxorder]
      exact pow_orderOf_eq_one x
    have hZle : Subgroup.zpowers x ≤ P :=
      Subgroup.zpowers_le.mpr xP.property
    have hZcard : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxorder]
    have hZeq : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge hZle
      rw [hZcard, hPcardNat]
    have hnorm : ∀ c : Equiv.Perm (Fin 4), c * t = t * c →
        c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x ^ 2 := by
      intro c hc
      have hcCent : c ∈
          Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc
      have hcNorm := hPinv hcCent
      have hconjP : c * x * c⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hcNorm x).mp xP.property
      rw [← hZeq] at hconjP
      rcases Subgroup.mem_zpowers_iff.mp hconjP with ⟨k, hk⟩
      have hnonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
      have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
      rw [zpow_eq_zpow_emod' k hxpow] at hk
      interval_cases hrem : k % (3 : ℤ)
      · simp at hk
        exfalso
        apply hxne
        calc
          x = c⁻¹ * (c * x * c⁻¹) * c := by group
          _ = 1 := by rw [← hk]; simp
      · simp at hk
        exact Or.inl hk.symm
      · right
        rw [← zpow_natCast]
        exact hk.symm
    have hxt : x * t = t * x :=
      s4ReflectedCertificate x t ⟨hxne, hxpow⟩
        (by simpa only [IsInvolution] using ht) hnorm
    rw [← hZeq]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hxt)


end CFSG.GorensteinWalter
