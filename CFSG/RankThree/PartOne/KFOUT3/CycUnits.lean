module

public import CFSG.RankThree.PartOne.KFOUT3.CycKrylov
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Polynomial

variable {K : Type} [Field K]

theorem quad_ne_zero [CharP K 2] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) (x : K) :
    x ^ 2 + x + 1 ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * h
  let u : Kˣ := Units.mk0 x hx0
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hx3)
  have hu1 : u ≠ 1 := by
    intro h1
    have hx1 : x = 1 := congrArg Units.val h1
    rw [hx1] at h
    exact one_ne_zero (by linear_combination h - h2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [Nat.card_units, hord] at hdvd
  exact h3 hdvd

theorem irreducible_quad [CharP K 2] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) :
    Irreducible (X ^ 2 + X + 1 : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    rw [this]
    simp
  · intro x hx
    apply quad_ne_zero h3 x
    simpa [IsRoot] using hx

theorem coprime_quad [CharP K 2] : IsCoprime (X - 1 : K[X]) (X ^ 2 + X + 1) := by
  have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
  exact ⟨-(X + 2), 1, by linear_combination h2⟩

abbrev Qring (K : Type) [Field K] : Type := AdjoinRoot (X ^ 3 - 1 : K[X])

abbrev Lring (K : Type) [Field K] : Type := AdjoinRoot (X ^ 2 + X + 1 : K[X])

noncomputable def qCRT [CharP K 2] : Qring K ≃+* K × Lring K := by
  have hcop : IsCoprime (Ideal.span {(X - 1 : K[X])}) (Ideal.span {(X ^ 2 + X + 1 : K[X])}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 coprime_quad
  have hmul : Ideal.span {(X - 1 : K[X])} * Ideal.span {(X ^ 2 + X + 1 : K[X])} =
      Ideal.span {(X ^ 3 - 1 : K[X])} := by
    have hpoly : ((X - 1) * (X ^ 2 + X + 1) : K[X]) = X ^ 3 - 1 := by ring
    rw [Ideal.span_singleton_mul_span_singleton, hpoly]
  have e1 : K[X] ⧸ Ideal.span {(X - 1 : K[X])} ≃+* K := by
    have h : Ideal.span {(X - 1 : K[X])} = Ideal.span {X - C (1 : K)} := by simp
    exact (Ideal.quotEquivOfEq h).trans (Polynomial.quotientSpanXSubCAlgEquiv (1 : K)).toRingEquiv
  exact (Ideal.quotEquivOfEq hmul.symm).trans
    ((Ideal.quotientMulEquivQuotientProd _ _ hcop).trans (RingEquiv.prodCongr e1 (RingEquiv.refl _)))

theorem natDegree_quad : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!

theorem quad_ne_zero' : (X ^ 2 + X + 1 : K[X]) ≠ 0 := by
  intro h
  have := natDegree_quad (K := K)
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

theorem finite_Lring [Finite K] : Finite (Lring K) := by
  have : Module.Finite K (Lring K) := Module.Finite.of_basis (AdjoinRoot.powerBasis quad_ne_zero').basis
  exact Module.finite_of_finite K

theorem card_Lring [Finite K] : Nat.card (Lring K) = Nat.card K ^ 2 := by
  have : Module.Finite K (Lring K) := Module.Finite.of_basis (AdjoinRoot.powerBasis quad_ne_zero').basis
  have hfin : Module.finrank K (Lring K) = 2 :=
    (finrank_quotient_span_eq_natDegree (K := K) (f := (X ^ 2 + X + 1 : K[X]))).trans natDegree_quad
  rw [Module.natCard_eq_pow_finrank (K := K), hfin]

theorem finite_Qring [CharP K 2] [Finite K] : Finite (Qring K) := by
  have : Finite (Lring K) := finite_Lring
  exact Finite.of_equiv _ qCRT.symm.toEquiv

noncomputable abbrev lField [CharP K 2] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) : Field (Lring K) :=
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_quad h3⟩
  inferInstanceAs (Field (AdjoinRoot (X ^ 2 + X + 1 : K[X])))

noncomputable def qUnitsEquiv [CharP K 2] : (Qring K)ˣ ≃* Kˣ × (Lring K)ˣ :=
  (Units.mapEquiv qCRT.toMulEquiv).trans MulEquiv.prodUnits

theorem card_Qunits [CharP K 2] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) :
    Nat.card (Qring K)ˣ = (Nat.card K - 1) * (Nat.card K ^ 2 - 1) := by
  let _ := lField h3
  rw [Nat.card_congr qUnitsEquiv.toEquiv, Nat.card_prod, Nat.card_units, Nat.card_units,
    card_Lring]

theorem exists_threeElts {Γ : Type*} [CommGroup Γ] [Finite Γ] :
    ∃ P : Subgroup Γ, (∀ g, g ∈ P ↔ ∃ n : ℕ, g ^ (3 ^ n) = 1) ∧
      Nat.card P = 3 ^ (Nat.card Γ).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 Γ))
  refine ⟨S.toSubgroup, fun g => ⟨fun hg => ?_, fun ⟨n, hn⟩ => ?_⟩, Sylow.card_eq_multiplicity S⟩
  · obtain ⟨n, hn⟩ := S.isPGroup' ⟨g, hg⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · have hP : IsPGroup 3 (Subgroup.zpowers g) := by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
      refine ⟨n, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
        one_zpow]
      rfl
    exact hP.le_sylow_of_normal S (Subgroup.mem_zpowers g)

theorem exists_threeElts_cyclic [CharP K 2] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) :
    ∃ P : Subgroup (Qring K)ˣ, (∀ g, g ∈ P ↔ ∃ n : ℕ, g ^ (3 ^ n) = 1) ∧ IsCyclic P ∧
      Nat.card P = 3 ^ (Nat.card K ^ 2 - 1).factorization 3 := by
  let _ := lField h3
  have : Finite (Lring K) := finite_Lring
  have : Finite (Qring K) := finite_Qring
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hcard⟩ := exists_threeElts (Γ := (Qring K)ˣ)
  have hK1 : 0 < Nat.card K - 1 := by
    have := Nat.card_pos (α := K)
    have : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    omega
  have hK2 : 0 < Nat.card K ^ 2 - 1 := by
    have : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  refine ⟨P, hP, ?_, ?_⟩
  ·
    let φ : P →* (Lring K)ˣ := (MonoidHom.snd _ _).comp (qUnitsEquiv.toMonoidHom.comp P.subtype)
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨n, hn⟩ := (hP x.1).1 x.2
      have hx' : qUnitsEquiv (x : (Qring K)ˣ) = (1, 1) := by
        have h1 : (qUnitsEquiv (x : (Qring K)ˣ)).2 = 1 := hx
        have h2 : (qUnitsEquiv (x : (Qring K)ˣ)).1 = 1 := by
          set a := (qUnitsEquiv (x : (Qring K)ˣ)).1 with ha
          have ha3 : a ^ (3 ^ n) = 1 := by
            have := congrArg (fun y => (qUnitsEquiv y).1) hn
            simpa [ha, map_pow] using this
          have hdvd1 : orderOf a ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one ha3
          have hdvd2 : orderOf a ∣ Nat.card K - 1 := by
            have := orderOf_dvd_natCard a
            rwa [Nat.card_units] at this
          have hcop : Nat.Coprime (3 ^ n) (Nat.card K - 1) :=
            Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
          have : orderOf a ∣ Nat.gcd (3 ^ n) (Nat.card K - 1) := Nat.dvd_gcd hdvd1 hdvd2
          rw [hcop] at this
          exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
        exact Prod.ext h2 h1
      have : (x : (Qring K)ˣ) = 1 := qUnitsEquiv.injective (by rw [hx', map_one]; rfl)
      exact Subtype.ext this
    exact isCyclic_of_injective φ hφ
  · rw [hcard, card_Qunits h3, Nat.factorization_mul hK1.ne' hK2.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3, zero_add]

end CFSG.RankThree.PartOne.KFOUT3
