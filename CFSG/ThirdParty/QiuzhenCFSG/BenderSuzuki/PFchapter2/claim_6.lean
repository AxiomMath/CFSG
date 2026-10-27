module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.Multiplicity

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

universe v

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open PFAppendixII
open scoped Matrix

/-!
# Peterfalvi, Part II, Chapter II, Claim (6)
-/

private theorem huppert_blackburn_IX_2_7_prime_power_successor_trichotomy
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (hb : 0 < b) (heq : p ^ a = q ^ b + 1) :
    (p = 2 ∧ b = 1 ∧ Nat.Prime a ∧ q = 2 ^ a - 1) ∨
      (q = 2 ∧ a = 1 ∧ ∃ m : ℕ, b = 2 ^ m ∧ p = 2 ^ (2 ^ m) + 1) ∨
        (p ^ a = 9 ∧ q ^ b = 8) := by
  have odd_dvd_two_pow_eq_one : ∀ {d n : ℕ}, Odd d → d ∣ 2 ^ n → d = 1 := by
    intro d n hd hdiv
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    cases k with
    | zero => simp
    | succ k =>
        exact False.elim (hd.not_two_dvd_nat (dvd_pow_self 2 (Nat.succ_ne_zero k)))
  have odd_geom_sum_of_odd :
      ∀ {x n : ℕ}, Odd x → Odd n → Odd (∑ i ∈ Finset.range n, x ^ i) := by
    intro x n hx hn
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa [hx.pow] using hn
  by_cases ha1 : a = 1
  · subst a
    simp only [pow_one] at heq
    right
    left
    have hq2 : q = 2 := by
      rcases hq.eq_two_or_odd' with hq2 | hqodd
      · exact hq2
      · have hpEven : Even p := by
          rw [heq]
          exact hqodd.pow.add_one
        rcases hp.eq_two_or_odd' with hp2 | hpodd
        · subst p
          have hqle : q ≤ q ^ b := Nat.le_pow hb
          have hqge : 2 ≤ q := hq.two_le
          omega
        · rcases hpEven with ⟨u, hu⟩
          rcases hpodd with ⟨v, hv⟩
          omega
    subst q
    obtain ⟨n, hn⟩ :=
      Nat.pow_of_pow_add_prime (a := 2) (n := b) (by norm_num) hb.ne'
        (by simpa [heq] using hp)
    exact ⟨rfl, rfl, n, hn, by simpa [hn] using heq⟩
  by_cases hb1 : b = 1
  · subst b
    simp only [pow_one] at heq
    have hq' : Nat.Prime (p ^ a - 1) := by
      convert hq using 1
      omega
    obtain ⟨hp2, haPrime⟩ := Nat.prime_of_pow_sub_one_prime ha1 hq'
    left
    subst p
    exact ⟨rfl, rfl, haPrime, by omega⟩
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have hp2_or_hq2 : p = 2 ∨ q = 2 := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · exact Or.inl hp2
    rcases hq.eq_two_or_odd' with hq2 | hqodd
    · exact Or.inr hq2
    exfalso
    have hpowa : Odd (p ^ a) := hpodd.pow
    have hqpowb : Odd (q ^ b) := hqodd.pow
    rcases hpowa with ⟨u, hu⟩
    rcases hqpowb with ⟨v, hv⟩
    omega
  right
  right
  rcases hp2_or_hq2 with hp2 | hq2
  · subst p
    have hqodd : Odd q := (hq.eq_two_or_odd').resolve_left (by
      intro hq2
      subst q
      have hleft : Even (2 ^ a) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      have hright : Even (2 ^ b) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rcases hleft with ⟨u, hu⟩
      rcases hright with ⟨v, hv⟩
      omega)
    have hfour : 4 ∣ 2 ^ a := by
      simpa using Nat.pow_dvd_pow 2 ha2
    have hbOdd : Odd b := by
      rcases Nat.even_or_odd b with hbEven | hbOdd
      · exfalso
        rcases hbEven with ⟨c, hc⟩
        have hsq : q ^ b = (q ^ c) ^ 2 := by
          simp [hc, pow_two, pow_add]
        have hxodd : Odd (q ^ c) := hqodd.pow
        have height : 8 ∣ (q ^ c) ^ 2 - 1 :=
          Nat.eight_dvd_sq_sub_one_of_odd hxodd
        rcases hfour with ⟨u, hu⟩
        rcases height with ⟨v, hv⟩
        omega
      · exact hbOdd
    have hqnot : ¬(2 : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast hqodd.not_two_dvd_nat
    have hbnot : ¬(2 : ℤ) ∣ (b : ℤ) := by
      exact_mod_cast hbOdd.not_two_dvd_nat
    have hqplus : (2 : ℤ) ∣ (q : ℤ) - (-1) := by
      rcases hqodd with ⟨c, hc⟩
      use c + 1
      omega
    have hmult :=
      emultiplicity_pow_sub_pow_of_prime Int.prime_two hqplus hqnot hbnot
    have hcast : (q : ℤ) ^ b + 1 = (2 : ℤ) ^ a := by
      exact_mod_cast heq.symm
    rw [Odd.neg_one_pow hbOdd, sub_neg_eq_add, hcast,
      emultiplicity_pow_self (by norm_num : (2 : ℤ) ≠ 0)
        (by norm_num [Int.isUnit_iff] : ¬IsUnit (2 : ℤ))] at hmult
    have hdivZ : (2 : ℤ) ^ a ∣ (q : ℤ) + 1 :=
      (emultiplicity_eq_coe.mp hmult.symm).1
    have hdiv : 2 ^ a ∣ q + 1 := by
      exact_mod_cast hdivZ
    have hle : q + 1 ≤ 2 ^ a := by
      rw [heq]
      exact Nat.add_le_add_right (Nat.le_pow hb) 1
    have heqq : q + 1 = 2 ^ a :=
      Nat.le_antisymm hle (Nat.le_of_dvd (by omega) hdiv)
    have hpow : q ^ b = q := by omega
    exact False.elim (hb1 ((Nat.pow_eq_self_iff hq.one_lt).mp hpow))
  · subst q
    have hpodd : Odd p := (hp.eq_two_or_odd').resolve_left (by
      intro hp2
      subst p
      have hleft : Even (2 ^ a) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      have hright : Even (2 ^ b) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rcases hleft with ⟨u, hu⟩
      rcases hright with ⟨v, hv⟩
      omega)
    have hsub : p ^ a - 1 = 2 ^ b := by
      exact (Nat.sub_eq_iff_eq_add (Nat.one_le_pow a p hp.pos)).2 (by simpa [add_comm] using heq)
    have haEven : Even a := by
      rcases Nat.even_or_odd a with haEven | haOdd
      · exact haEven
      · exfalso
        let S := ∑ i ∈ Finset.range a, p ^ i
        have hSodd : Odd S := odd_geom_sum_of_odd hpodd haOdd
        have hfac : S * (p - 1) = p ^ a - 1 := by
          simpa [S] using geom_sum_mul_of_one_le hp.one_le a
        have hSdvd : S ∣ 2 ^ b := by
          refine ⟨p - 1, ?_⟩
          exact (hfac.trans hsub).symm
        have hS1 : S = 1 := odd_dvd_two_pow_eq_one hSodd hSdvd
        have hpow : p ^ a = p := by
          rw [hS1, one_mul] at hfac
          exact Nat.sub_one_cancel (Nat.pow_pos hp.pos) hp.pos hfac.symm
        exact ha1 ((Nat.pow_eq_self_iff hp.one_lt).mp hpow)
    rcases haEven with ⟨c, hc⟩
    have hcpos : 0 < c := by omega
    let x := p ^ c
    have hxodd : Odd x := hpodd.pow
    have hxpos : 0 < x := Nat.pow_pos hp.pos
    have hfac : (x - 1) * (x + 1) = 2 ^ b := by
      calc
        (x - 1) * (x + 1) = x ^ 2 - 1 := by
          obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ x)
          rw [hy]
          simp only [Nat.add_sub_cancel_left]
          rw [mul_add]
          trans y * (1 + y) + (y + 1) * 1 - 1
          · simp
          · ring_nf
        _ = p ^ a - 1 := by simp [x, hc, pow_two, pow_add]
        _ = 2 ^ b := hsub
    have hleftDvd : x - 1 ∣ 2 ^ b := ⟨x + 1, hfac.symm⟩
    have hrightDvd : x + 1 ∣ 2 ^ b := ⟨x - 1, by simpa [mul_comm] using hfac.symm⟩
    obtain ⟨r, hrb, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hleftDvd
    obtain ⟨s, hsb, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrightDvd
    have hr0 : r ≠ 0 := by
      intro hrzero
      rw [hrzero, pow_zero] at hr
      rcases hxodd with ⟨u, hu⟩
      omega
    have hrs : r ≤ s := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      rw [← hr, ← hs]
      omega
    have hpowDvd : 2 ^ r ∣ 2 ^ s := Nat.pow_dvd_pow 2 hrs
    have htwoDvd : 2 ^ r ∣ 2 := by
      have h1 : 2 ^ r ∣ x + 1 := by simpa [hs] using hpowDvd
      have h2 : 2 ^ r ∣ x - 1 := by simp [hr]
      convert Nat.dvd_sub h1 h2 using 1
      omega
    have hrpow : 2 ^ r = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp htwoDvd with h | h
      · have : r = 0 := by simpa using (Nat.pow_eq_one.mp h)
        exact False.elim (hr0 this)
      · exact h
    have hx : x = 3 := by omega
    have hpa : p ^ a = 9 := by
      calc
        p ^ a = (p ^ c) ^ 2 := by simp [hc, pow_two, pow_add]
        _ = x ^ 2 := by rfl
        _ = 9 := by simp [hx]
    exact ⟨hpa, by omega⟩


/-- Public checked wrapper for the prime-power successor classification used
by the fixed-field calculations in later claims. -/
public theorem prime_power_successor_trichotomy
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (hb : 0 < b) (heq : p ^ a = q ^ b + 1) :
    (p = 2 ∧ b = 1 ∧ Nat.Prime a ∧ q = 2 ^ a - 1) ∨
      (q = 2 ∧ a = 1 ∧ ∃ m : ℕ, b = 2 ^ m ∧ p = 2 ^ (2 ^ m) + 1) ∨
        (p ^ a = 9 ∧ q ^ b = 8) :=
  huppert_blackburn_IX_2_7_prime_power_successor_trichotomy hp hq ha hb heq

private theorem claim6_units_card_power_of_two
    {G F : Type*} [Group G] [Finite G]
    [PFAppendixII.RightNearField F] [Finite F]
    (Q S Q1 P : Subgroup G)
    (hS_sylow : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hQ1 : Q1 = ⊥) (hsup : S ⊔ Q1 = Q)
    (unitEquiv : nearFieldStar Q P ≃* Fˣ) :
    ∃ b : ℕ, Nat.card Fˣ = 2 ^ b := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQ : S = Q := by
    simpa [hQ1] using hsup
  rcases hS_sylow with ⟨P2, hS⟩
  have hSp : IsPGroup 2 S := by
    have hp := P2.isPGroup'.map Q.subtype
    rw [← hS] at hp
    exact hp
  have hstar_le_S : nearFieldStar Q P ≤ S := by
    rw [hSQ]
    exact inf_le_left
  let starInS : Subgroup S :=
    (nearFieldStar Q P).subgroupOf S
  have hstarInSp : IsPGroup 2 starInS := hSp.to_subgroup starInS
  have hstarP : IsPGroup 2 (nearFieldStar Q P) :=
    hstarInSp.of_equiv (Subgroup.subgroupOfEquivOfLe hstar_le_S)
  obtain ⟨b, hb⟩ := hstarP.exists_card_eq
  exact ⟨b, (Nat.card_congr unitEquiv.toEquiv).symm.trans hb⟩

private theorem claim6_nearField_commutative_of_unitEquiv
    {G F : Type*} [Group G]
    [PFAppendixII.RightNearField F]
    (Q P : Subgroup G) (unitEquiv : nearFieldStar Q P ≃* Fˣ)
    (hstar : IsMulCommutative (nearFieldStar Q P)) :
    IsMulCommutative F := by
  have hUnits : IsMulCommutative Fˣ := by
    letI : IsMulCommutative (nearFieldStar Q P) := hstar
    refine ⟨⟨fun x y => ?_⟩⟩
    apply unitEquiv.symm.injective
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := nearFieldStar Q P)).comm _ _
  letI : IsMulCommutative Fˣ := hUnits
  refine ⟨⟨fun x y => ?_⟩⟩
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  let ux : Fˣ := Units.mk0 x hx
  let uy : Fˣ := Units.mk0 y hy
  exact congrArg Units.val
    ((IsMulCommutative.is_comm (M := Fˣ)).comm ux uy)

/- Claim (6), exceptional branch: the odd quotient automorphism factor has
order one or three when the actual near-field has eight units. -/
private theorem claim6_units_card_eight_sigma_card
    {X F : Type*} [Group X] [Finite X]
    [PFAppendixII.RightNearField F] [Finite F]
    (H Sigma Q : Subgroup X)
    (hPO : PFAppendixII.PropositionOneConclusion H Sigma Q F)
    (hSigmaOdd : Odd (Nat.card Sigma))
    (hUnitsCard : Nat.card Fˣ = 8) :
    Nat.card Sigma = 1 ∨ Nat.card Sigma = 3 := by
  classical
  have hFcard : Nat.card F = 9 := by
    rw [Nat.card_eq_card_units_add_one, hUnitsCard]
  have hCharPrime : Nat.Prime (addOrderOf (1 : F)) :=
    rightNearField_addOrderOf_one_prime
  have hCharDvdNine : addOrderOf (1 : F) ∣ 9 := by
    simpa [hFcard] using addOrderOf_dvd_natCard (1 : F)
  have hChar : addOrderOf (1 : F) = 3 :=
    Nat.prime_eq_prime_of_dvd_pow (m := 2) hCharPrime Nat.prime_three
      (by simpa using hCharDvdNine)
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let moduleThree : Module (ZMod 3) F := by
    exact AddCommGroup.zmodModule (n := 3) (by
      intro x
      rw [← hChar]
      exact rightNearField_addOrderOf_one_nsmul_eq_zero x)
  letI : Module (ZMod 3) F := moduleThree
  have hfinrank : Module.finrank (ZMod 3) F = 2 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    calc
      3 ^ Module.finrank (ZMod 3) F = Nat.card F :=
        FiniteField.pow_finrank_eq_natCard 3 F
      _ = 3 ^ 2 := by norm_num [hFcard]
  rcases hPO with
    ⟨_addLift, _unitLift, sigmaAct, _hcoordinates, _haddZero, _hadd,
      _hunitOne, _hunitMul, _hunitRange, _hright, hsigmaMaps,
      hsigmaOne, hsigmaMul, hsigmaInjective, _hrightSigma,
      _hinvolutionUnique, _hinvolutionOrder⟩
  let sigmaAddEquiv (d : Sigma) : F ≃+ F :=
    { toFun := sigmaAct d⁻¹
      invFun := sigmaAct d
      left_inv := by
        intro x
        calc
          sigmaAct d (sigmaAct d⁻¹ x) = sigmaAct (d⁻¹ * d) x :=
            (hsigmaMul d⁻¹ d x).symm
          _ = x := by simpa using hsigmaOne x
      right_inv := by
        intro x
        calc
          sigmaAct d⁻¹ (sigmaAct d x) = sigmaAct (d * d⁻¹) x :=
            (hsigmaMul d d⁻¹ x).symm
          _ = x := by simpa using hsigmaOne x
      map_add' := by
        intro x y
        exact (hsigmaMaps d⁻¹ x y).1 }
  let sigmaLinearEquiv (d : Sigma) : F ≃ₗ[ZMod 3] F :=
    (sigmaAddEquiv d).toLinearEquiv (by
      intro c x
      exact
        (AddMonoidHom.toZModLinearMap 3
          (sigmaAddEquiv d).toAddMonoidHom).map_smul c x)
  let sigmaLinearHom : Sigma →* (F ≃ₗ[ZMod 3] F) :=
    { toFun := sigmaLinearEquiv
      map_one' := by
        apply LinearEquiv.ext
        intro x
        change sigmaAct (1 : Sigma)⁻¹ x = x
        simpa using hsigmaOne x
      map_mul' := by
        intro d e
        apply LinearEquiv.ext
        intro x
        change sigmaAct (d * e)⁻¹ x = sigmaAct d⁻¹ (sigmaAct e⁻¹ x)
        rw [mul_inv_rev]
        exact hsigmaMul e⁻¹ d⁻¹ x }
  have hsigmaLinearInjective : Function.Injective sigmaLinearHom := by
    intro d e hde
    have hfun : sigmaAct d⁻¹ = sigmaAct e⁻¹ := by
      funext x
      exact congrArg (fun f : F ≃ₗ[ZMod 3] F => f x) hde
    have hinv : d⁻¹ = e⁻¹ := hsigmaInjective hfun
    exact inv_injective hinv
  let basisTwo : Module.Basis (Fin 2) (ZMod 3) F := by
    rw [← hfinrank]
    exact Module.finBasis (ZMod 3) F
  let glEquiv : GL (Fin 2) (ZMod 3) ≃* (F ≃ₗ[ZMod 3] F) :=
    (Matrix.GeneralLinearGroup.toLin' basisTwo).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) F)
  have hLinearAutCard : Nat.card (F ≃ₗ[ZMod 3] F) = 48 := by
    calc
      Nat.card (F ≃ₗ[ZMod 3] F) = Nat.card (GL (Fin 2) (ZMod 3)) :=
        Nat.card_congr glEquiv.symm.toEquiv
      _ = 48 := by
        rw [Matrix.card_GL_field]
        norm_num [Fin.prod_univ_two]
  have hSigmaDvdFortyEight : Nat.card Sigma ∣ 48 := by
    simpa [hLinearAutCard] using
      Subgroup.card_dvd_of_injective sigmaLinearHom hsigmaLinearInjective
  have hSigmaCoprimeSixteen : (Nat.card Sigma).Coprime 16 := by
    simpa using hSigmaOdd.coprime_two_right.pow_right 4
  have hSigmaDvdThree : Nat.card Sigma ∣ 3 := by
    apply (hSigmaCoprimeSixteen.dvd_mul_right).mp
    exact hSigmaDvdFortyEight
  exact (Nat.dvd_prime Nat.prime_three).mp hSigmaDvdThree

/- Claim (6), field branch: the actual near-field order is its characteristic
or nine. -/
private theorem claim6_field_order_or_nine
    {F : Type*} [PFAppendixII.RightNearField F] [Finite F]
    (ell : ℕ) (_hcomm : IsMulCommutative F)
    (hchar : addOrderOf (1 : F) = ell)
    (hunits : ∃ b : ℕ, Nat.card Fˣ = 2 ^ b) :
    Nat.card F = ell ∨ Nat.card F = 9 := by
  have hellPrime : Nat.Prime ell := by
    rw [← hchar]
    exact rightNearField_addOrderOf_one_prime
  obtain ⟨a, hcard⟩ :=
    rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  rw [hchar] at hcard
  have ha : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    rw [ha0, pow_zero] at hcard
    exact (not_lt_of_ge (show Nat.card F ≤ 1 by omega))
      (Finite.one_lt_card (α := F))
  obtain ⟨b, hb⟩ := hunits
  have hsucc : ell ^ a = 2 ^ b + 1 := by
    rw [← hcard, Nat.card_eq_card_units_add_one, hb]
  by_cases hb0 : b = 0
  · have hpowTwo : ell ^ a = 2 := by simpa [hb0] using hsucc
    have hellDvdTwo : ell ∣ 2 := by
      rw [← hpowTwo]
      exact dvd_pow_self ell ha.ne'
    have hellTwo : ell = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hellDvdTwo with hellOne | hellTwo
      · exact False.elim (hellPrime.ne_one hellOne)
      · exact hellTwo
    have haOne : a = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      simpa [hellTwo] using hpowTwo
    left
    simp [hcard, haOne]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    rcases
        huppert_blackburn_IX_2_7_prime_power_successor_trichotomy
          hellPrime Nat.prime_two ha hbpos hsucc with
      hMersenne | hFermat | hNine
    · rcases hMersenne with ⟨hellTwo, _hbOne, haPrime, htwo⟩
      have hpowThree : 2 ^ a = 3 := by omega
      have hpowEven : Even (2 ^ a) :=
        Nat.even_pow.mpr ⟨even_two, ha.ne'⟩
      rw [hpowThree] at hpowEven
      rcases hpowEven with ⟨k, hk⟩
      omega
    · left
      rcases hFermat with ⟨_htwo, haOne, _⟩
      simp [hcard, haOne]
    · right
      exact hcard.trans hNine.1

/- Claim (6), field branch: the odd quotient automorphism factor is trivial. -/
private theorem claim6_field_sigma_bot
    {X F : Type*} [Group X] [Finite X]
    [PFAppendixII.RightNearField F] [Finite F]
    (H Sigma Q : Subgroup X) (ell : ℕ)
    (hPO : PFAppendixII.PropositionOneConclusion H Sigma Q F)
    (hSigmaOdd : Odd (Nat.card Sigma))
    (hcomm : IsMulCommutative F)
    (hchar : addOrderOf (1 : F) = ell)
    (horder : Nat.card F = ell ∨ Nat.card F = 9) :
    Sigma = ⊥ := by
  classical
  have hCharDvdCard : addOrderOf (1 : F) ∣ Nat.card F :=
    addOrderOf_dvd_natCard (1 : F)
  letI : IsMulCommutative F := hcomm
  let fieldF : Field F :=
    Field.ofMinimalAxioms F add_assoc zero_add neg_add_cancel mul_assoc
      (IsMulCommutative.is_comm (M := F)).comm one_mul
      (fun a ha => mul_inv_cancel₀ ha) inv_zero
      (fun a b c => by
        calc
          a * (b + c) = (b + c) * a :=
            (IsMulCommutative.is_comm (M := F)).comm _ _
          _ = b * a + c * a := RightNearField.right_distrib b c a
          _ = a * b + a * c := by
            rw [(IsMulCommutative.is_comm (M := F)).comm b a,
              (IsMulCommutative.is_comm (M := F)).comm c a])
      ⟨0, 1, zero_ne_one⟩
  letI : Field F := fieldF
  letI : AddCommGroup F := fieldF.toAddCommGroup
  letI : AddCommMonoid F := fieldF.toAddCommGroup.toAddCommMonoid
  have hellPrime : Nat.Prime ell := by
    rw [← hchar]
    exact rightNearField_addOrderOf_one_prime
  letI : Fact (Nat.Prime ell) := ⟨hellPrime⟩
  let zmodField : Field (ZMod ell) := inferInstance
  letI : Semiring (ZMod ell) :=
    zmodField.toSemifield.toDivisionSemiring.toSemiring
  letI : CharP F ell := by
    rw [← hchar]
    exact CharP.addOrderOf_one F
  letI : Module (ZMod ell) F :=
    { (ZMod.castHom dvd_rfl F : ZMod ell →+* _).toModule with }
  letI : Algebra (ZMod ell) F := ZMod.algebraOfModule ell F
  letI : Module (ZMod ell) F := Algebra.toModule
  rcases hPO with
    ⟨_addLift, _unitLift, sigmaAct, _hcoordinates, _haddZero, _hadd,
      _hunitOne, _hunitMul, _hunitRange, _hright, hsigmaMaps,
      hsigmaOne, hsigmaMul, hsigmaInjective, _hrightSigma,
      _hinvolutionUnique, _hinvolutionOrder⟩
  let sigmaRingEquiv (d : Sigma) : F ≃+* F :=
    { toFun := sigmaAct d⁻¹
      invFun := sigmaAct d
      left_inv := by
        intro x
        calc
          sigmaAct d (sigmaAct d⁻¹ x) = sigmaAct (d⁻¹ * d) x :=
            (hsigmaMul d⁻¹ d x).symm
          _ = x := by simpa using hsigmaOne x
      right_inv := by
        intro x
        calc
          sigmaAct d⁻¹ (sigmaAct d x) = sigmaAct (d * d⁻¹) x :=
            (hsigmaMul d d⁻¹ x).symm
          _ = x := by simpa using hsigmaOne x
      map_mul' := by
        intro x y
        exact (hsigmaMaps d⁻¹ x y).2.1
      map_add' := by
        intro x y
        exact (hsigmaMaps d⁻¹ x y).1 }
  let sigmaRingHom : Sigma →* (F ≃+* F) :=
    { toFun := sigmaRingEquiv
      map_one' := by
        ext x
        change sigmaAct (1 : Sigma)⁻¹ x = x
        simpa using hsigmaOne x
      map_mul' := by
        intro d e
        ext x
        change sigmaAct (d * e)⁻¹ x = sigmaAct d⁻¹ (sigmaAct e⁻¹ x)
        rw [mul_inv_rev]
        exact hsigmaMul e⁻¹ d⁻¹ x }
  have hsigmaRingInjective : Function.Injective sigmaRingHom := by
    intro d e hde
    have hfun : sigmaAct d⁻¹ = sigmaAct e⁻¹ := by
      funext x
      exact congrArg (fun f : F ≃+* F => f x) hde
    have hinv : d⁻¹ = e⁻¹ := hsigmaInjective hfun
    exact inv_injective hinv
  let toAlg : (F ≃+* F) → (F ≃ₐ[ZMod ell] F) := fun e =>
    AlgEquiv.ofRingEquiv (R := ZMod ell) (A₁ := F) (A₂ := F) (f := e) (by
      intro x
      have h :
          (e.toRingHom.comp (algebraMap (ZMod ell) F) :
              ZMod ell →+* F) = algebraMap (ZMod ell) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have htoAlgInjective : Function.Injective toAlg := by
    intro e₁ e₂ h
    ext x
    have hRing : e₁ = e₂ := by
      apply RingEquiv.ext
      intro y
      exact DFunLike.congr_fun (congrArg (fun f : F ≃ₐ[ZMod ell] F => f.toRingEquiv) h) y
    exact congrArg (fun e : F ≃+* F => e x) hRing
  have hRingAutCardLe :
      Nat.card (F ≃+* F) ≤ Module.finrank (ZMod ell) F := by
    calc
      Nat.card (F ≃+* F) ≤ Nat.card (F ≃ₐ[ZMod ell] F) :=
        Nat.card_le_card_of_injective toAlg htoAlgInjective
      _ ≤ Module.finrank (ZMod ell) F := by
        simpa [Nat.card_eq_fintype_card] using
          (AlgEquiv.card_le (F := ZMod ell) (K := F))
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e₁ e₂ h
      ext x
      exact congr_fun h x)
  have hSigmaCardLe :
      Nat.card Sigma ≤ Module.finrank (ZMod ell) F :=
    (Nat.card_le_card_of_injective sigmaRingHom hsigmaRingInjective).trans
      hRingAutCardLe
  have hpowCard :
      ell ^ Module.finrank (ZMod ell) F = Nat.card F :=
    FiniteField.pow_finrank_eq_natCard ell F
  have hSigmaCardOne : Nat.card Sigma = 1 := by
    rcases horder with hFieldPrime | hFieldNine
    · have hfinrank : Module.finrank (ZMod ell) F = 1 := by
        apply Nat.pow_right_injective hellPrime.two_le
        calc
          ell ^ Module.finrank (ZMod ell) F = Nat.card F := hpowCard
          _ = ell := hFieldPrime
          _ = ell ^ 1 := (pow_one ell).symm
      rw [hfinrank] at hSigmaCardLe
      rcases hSigmaOdd with ⟨k, hk⟩
      omega
    · have hellThree : ell = 3 := by
        have hCharDvdNine : ell ∣ 9 := by
          rw [← hchar, ← hFieldNine]
          exact hCharDvdCard
        exact Nat.prime_eq_prime_of_dvd_pow
          (m := 2) hellPrime Nat.prime_three (by simpa using hCharDvdNine)
      have hfinrank : Module.finrank (ZMod ell) F = 2 := by
        apply Nat.pow_right_injective hellPrime.two_le
        calc
          ell ^ Module.finrank (ZMod ell) F = Nat.card F := hpowCard
          _ = 9 := hFieldNine
          _ = ell ^ 2 := by norm_num [hellThree]
      rw [hfinrank] at hSigmaCardLe
      rcases hSigmaOdd with ⟨k, hk⟩
      omega
  exact Subgroup.card_eq_one.mp hSigmaCardOne

public theorem claim_6
    {G : Type*} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p ell : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hQ1 : Q1 = ⊥) (hell : orderOf (s * t) = ell) :
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let OmegaP : Type _ := {w : Omega // w ∈ fixedPointsOfSubgroup G Omega P}
    letI : MulAction C OmegaP := fixedPointCentralizerAction G Omega P
    let _HP : Subgroup C := H.comap C.subtype
    let DP : Subgroup C := D.comap C.subtype
    let _QP : Subgroup C := Q.comap C.subtype
    let core : Subgroup C := pointStabilizerCore C OmegaP
    ∃ hnormal : core.Normal,
      letI : core.Normal := hnormal
      let pi : C →* C ⧸ core := QuotientGroup.mk' core
      let SigmaBar : Subgroup (C ⧸ core) := DP.map pi
      (¬ IsMulCommutative (nearFieldStar Q P) →
          Nat.card SigmaBar = 1 ∨ Nat.card SigmaBar = 3) ∧
        (IsMulCommutative (nearFieldStar Q P) →
          (Nat.card (nearFieldStar Q P) + 1 = ell ∨
            Nat.card (nearFieldStar Q P) + 1 = 9) ∧ SigmaBar = ⊥) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type _ := {w : Omega // w ∈ fixedPointsOfSubgroup G Omega P}
  letI : MulAction C OmegaP := fixedPointCentralizerAction G Omega P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨_hNcore, hnormal, _quotientAction, _hsmul, hAbar,
      F, hF, hFfinite, hFnontrivial, unitEquiv, hPO, hcharacteristic⟩
  letI : core.Normal := hnormal
  letI : PFAppendixII.RightNearField F := hF
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  have hQnil : Group.IsNilpotent Q :=
    PFchapter1section2.proposition_1_b H D Q K V W Q0 S Q1 t
      hch.section3.section2
  have hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S :=
    PFchapter1section2.corollary H D Q K V W Q0 S Q1 t
      hch.section3.section2
  have hunits : ∃ b : ℕ, Nat.card Fˣ = 2 ^ b :=
    claim6_units_card_power_of_two Q S Q1 P
      hch.section3.section2.S_sylow_in_Q hQ1
      hch.section3.section2.Q_decomp unitEquiv
  have hcharEll : addOrderOf (1 : F) = ell :=
    hcharacteristic.trans hell
  refine ⟨hnormal, ?_⟩
  dsimp only
  constructor
  · intro hstarNoncomm
    obtain ⟨_hFnoncomm, hUnitsCard, _hmodel⟩ :=
      claim_5_classify_nearFieldWitness Q S P hQnil
        hch.section3.section2.S_sylow_in_Q hSclass unitEquiv hstarNoncomm
    exact claim6_units_card_eight_sigma_card
      (HP.map pi) (DP.map pi) (QP.map pi) hPO hAbar.D_odd hUnitsCard
  · intro hstarComm
    have hFcomm : IsMulCommutative F :=
      claim6_nearField_commutative_of_unitEquiv Q P unitEquiv hstarComm
    have hForder : Nat.card F = ell ∨ Nat.card F = 9 :=
      claim6_field_order_or_nine ell hFcomm hcharEll hunits
    have hcardBridge :
        Nat.card (nearFieldStar Q P) + 1 = Nat.card F := by
      calc
        Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by
          rw [Nat.card_congr unitEquiv.toEquiv]
        _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
    refine ⟨?_, claim6_field_sigma_bot
      (HP.map pi) (DP.map pi) (QP.map pi) ell hPO hAbar.D_odd
        hFcomm hcharEll hForder⟩
    exact hForder.imp (hcardBridge.trans ·) (hcardBridge.trans ·)

end PFchapter2
end CFSG.BenderSuzuki
