module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.A10

open Subgroup

theorem exists_normal_complement_of_normalizer_le_centralizer {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (P : Sylow p X)
    (hP : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X)) :
    ∃ K : Subgroup X, K.Normal ∧ Nat.card K * Nat.card P = Nat.card X := by
  have : Finite (Sylow p X) := inferInstance
  have : (P : Subgroup X).FiniteIndex := inferInstance
  refine ⟨(MonoidHom.transferSylow P hP).ker, inferInstance, ?_⟩
  exact (MonoidHom.ker_transferSylow_isComplement' P hP).card_mul_card

theorem card_sylow_eq_prime {H : Type*} [Group H] [Finite H] {p a : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hcard : Nat.card H = p * 2 ^ a) (P : Sylow p H) : Nat.card P = p := by
  rw [Sylow.card_eq_multiplicity, hcard]
  have h1 : (p * 2 ^ a).factorization p = 1 := by
    rw [Nat.factorization_mul hp.out.ne_zero (by positivity)]
    simp [Nat.Prime.factorization_self hp.out, Nat.factorization_pow,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ p ∣ 2 from fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h))]
  rw [h1, pow_one]

theorem card_sylow_two_eq {H : Type*} [Group H] [Finite H] {p a : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hcard : Nat.card H = p * 2 ^ a) (S : Sylow 2 H) : Nat.card S = 2 ^ a := by
  rw [Sylow.card_eq_multiplicity, hcard]
  have h1 : (p * 2 ^ a).factorization 2 = a := by
    rw [Nat.factorization_mul hp.out.ne_zero (by positivity)]
    simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ p from fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h).symm)]
  rw [h1]

theorem sylow_comm_of_card_prime {H : Type*} [Group H] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card P = p) :
    ∀ x ∈ (P : Subgroup H), ∀ y ∈ (P : Subgroup H), x * y = y * x := by
  have : IsCyclic P := isCyclic_of_prime_card hPcard
  have hc : Std.Commutative (α := ↥P) (· * ·) := inferInstance
  intro x hx y hy
  exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sylow_normal_of_card {H : Type*} [Group H] [Finite H]
    (hO : ∀ K : Subgroup H, K.Normal → IsPGroup 2 K → K = ⊥)
    {p a : ℕ} [hp : Fact p.Prime] (hp57 : p = 5 ∨ p = 7) (ha : a ≤ 3)
    (hcard : Nat.card H = p * 2 ^ a) (P : Sylow p H) : (P : Subgroup H).Normal := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> decide
  have hPcard : Nat.card P = p := card_sylow_eq_prime hp2 hcard P
  have hPidx : (P : Subgroup H).index = 2 ^ a := by
    have := Subgroup.card_mul_index (P : Subgroup H)
    rw [hPcard, hcard] at this
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  have hmod : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
  have hdvd : Nat.card (Sylow p H) ∣ 2 ^ a := hPidx ▸ Sylow.card_dvd_index P
  obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hPcomm := sylow_comm_of_card_prime P hPcard
  by_cases hone : Nat.card (Sylow p H) = 1
  · have : Subsingleton (Sylow p H) := (Nat.card_eq_one_iff_unique.1 hone).1
    exact Sylow.normal_of_subsingleton P
  · exfalso
    have hb3 : b ≤ 3 := hba.trans ha
    have hb0 : b ≠ 0 := fun h => hone (by rw [hb, h]; rfl)
    have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
    have h8 : Nat.card (Sylow p H) = 8 ∧ p = 7 ∧ a = 3 := by
      rcases hp57 with rfl | rfl
      · exfalso
        interval_cases b <;> simp_all [Nat.ModEq]
      · interval_cases b
        · simp_all [Nat.ModEq]
        · simp_all [Nat.ModEq]
        · refine ⟨by rw [hb]; norm_num, rfl, ?_⟩
          omega
    obtain ⟨hn8, rfl, rfl⟩ := h8
    have h1 : Nat.card (Subgroup.normalizer (P : Set H)) * 8 = 7 * 2 ^ 3 := by
      have := Subgroup.card_mul_index (Subgroup.normalizer (P : Set H))
      rw [← Sylow.card_eq_index_normalizer, hn8, hcard] at this
      exact this
    have hnorm : Subgroup.normalizer (P : Set H) = (P : Subgroup H) := by
      have hle : (P : Subgroup H) ≤ Subgroup.normalizer (P : Set H) := Subgroup.le_normalizer
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hPcard]
      omega
    have hPc : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
      rw [hnorm]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hPcomm y hy x hx
    obtain ⟨K, hKn, hK⟩ := exists_normal_complement_of_normalizer_le_centralizer P hPc
    rw [hPcard, hcard] at hK
    have hK8 : Nat.card K = 8 := by omega
    have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 3) (by rw [hK8]; norm_num)
    have := hO K hKn hK2
    rw [this, Subgroup.card_bot] at hK8
    omega

theorem centralizer_normal_of_normal {H : Type*} [Group H] (P : Subgroup H) [P.Normal] :
    (Subgroup.centralizer (P : Set H)).Normal := by
  refine ⟨fun g hg h => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : h⁻¹ * x * h ∈ P := by
    have := (inferInstance : P.Normal).conj_mem x hx h⁻¹
    simpa using this
  have := hg (h⁻¹ * x * h) hx'
  calc x * (h * g * h⁻¹) = h * ((h⁻¹ * x * h) * g) * h⁻¹ := by group
    _ = h * (g * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
    _ = h * g * h⁻¹ * x := by group

theorem sylow_centralizer_eq {H : Type*} [Group H] [Finite H]
    (hO : ∀ K : Subgroup H, K.Normal → IsPGroup 2 K → K = ⊥)
    {p a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : Nat.card H = p * 2 ^ a) (P : Sylow p H) (hPn : (P : Subgroup H).Normal) :
    Subgroup.centralizer (P : Set H) = (P : Subgroup H) := by
  have hPcard : Nat.card P = p := card_sylow_eq_prime hp2 hcard P
  have hPcomm := sylow_comm_of_card_prime P hPcard
  set C : Subgroup H := Subgroup.centralizer (P : Set H) with hC
  have hPC : (P : Subgroup H) ≤ C := fun x hx => by
    rw [hC, Subgroup.mem_centralizer_iff]; intro y hy; exact hPcomm y hy x hx
  have hCn : C.Normal := centralizer_normal_of_normal (P : Subgroup H)
  set P' : Subgroup C := (P : Subgroup H).subgroupOf C with hP'
  have hP'card : Nat.card P' = p := by
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP'p : IsPGroup p P' :=
    (P.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hCdvd : Nat.card C ∣ p * 2 ^ a := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hidx : P'.index * p = Nat.card C := by
    have := Subgroup.card_mul_index P'
    rw [hP'card] at this
    rw [mul_comm]
    exact this
  have hidx2 : ∃ c, P'.index = 2 ^ c := by
    have h1 : P'.index ∣ 2 ^ a := by
      have : p * P'.index ∣ p * 2 ^ a := by
        rw [mul_comm p, hidx]; exact hCdvd
      exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos this
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hidx2
  have hpnd : ¬ p ∣ P'.index := by
    rw [hc]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  let S' : Sylow p C := hP'p.toSylow hpnd
  have hcentral : Subgroup.normalizer (S' : Set C) ≤ Subgroup.centralizer (S' : Set C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ P' := hy
    have hy1 : (y : H) ∈ (P : Subgroup H) := hy'
    have hx : (x : H) ∈ Subgroup.centralizer (P : Set H) := x.2
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hx (y : H) hy1
  obtain ⟨K', hK'n, hK'⟩ := exists_normal_complement_of_normalizer_le_centralizer S' hcentral
  have hS'card : Nat.card S' = p := hP'card
  rw [hS'card] at hK'
  have hK'card : Nat.card K' = 2 ^ c := by
    have : Nat.card K' * p = 2 ^ c * p := by rw [hK', ← hidx, hc]
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos this
  have hK'2 : IsPGroup 2 K' := IsPGroup.of_card hK'card
  have hK'idx : ¬ 2 ∣ K'.index := by
    have h1 := Subgroup.card_mul_index K'
    rw [hK'card, ← hidx, hc] at h1
    have : K'.index = p := by
      have h2 : 2 ^ c * K'.index = 2 ^ c * p := by rw [h1]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
    rw [this]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h).symm
  let S2 : Sylow 2 C := hK'2.toSylow hK'idx
  have hS2n : (S2 : Subgroup C).Normal := hK'n
  have hchar : (S2 : Subgroup C).Characteristic := Sylow.characteristic_of_normal S2 hS2n
  have hKn : (K'.map C.subtype).Normal := by
    have : K'.Characteristic := hchar
    exact inferInstance
  have hK2 : IsPGroup 2 (K'.map C.subtype) := hK'2.map _
  have hKbot := hO _ hKn hK2
  have hK'bot : K' = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K' C.subtype_injective).1 hKbot
  rw [hK'bot, Subgroup.card_bot] at hK'card
  have hc0 : c = 0 := by
    have : 2 ^ c = 2 ^ 0 := by rw [← hK'card]; rfl
    exact Nat.pow_right_injective (le_refl 2) this
  subst hc0
  refine (Subgroup.eq_of_le_of_card_ge hPC ?_).symm
  rw [hPcard, ← hidx, hc]
  simp

theorem sylow_two_cyclic_aux {H : Type*} [Group H] [Finite H] {p a : ℕ} [hp : Fact p.Prime]
    (hp57 : p = 5 ∨ p = 7)
    (ha : a ≤ 3) (hcard : Nat.card H = p * 2 ^ a) (P : Sylow p H) (hPn : (P : Subgroup H).Normal)
    (hC : Subgroup.centralizer (P : Set H) = (P : Subgroup H)) (S : Sylow 2 H) :
    IsCyclic S ∧ (p = 5 → a ≤ 2) ∧ (p = 7 → a ≤ 1) := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> decide
  have hPcard : Nat.card P = p := card_sylow_eq_prime hp2 hcard P
  have hScard : Nat.card S = 2 ^ a := card_sylow_two_eq hp2 hcard S
  have : IsCyclic P := isCyclic_of_prime_card hPcard
  have hprime : (Nat.card P).Prime := by rw [hPcard]; exact hp.out
  have hcyc : IsCyclic (MulAut (P : Subgroup H)) := by
    have : IsCyclic (ZMod (Nat.card P))ˣ := ZMod.isCyclic_units_prime hprime
    exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv (G := (P : Subgroup H))).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv (G := (P : Subgroup H))).symm.surjective
  have hcardAut : Nat.card (MulAut (P : Subgroup H)) = p - 1 := by
    rw [IsCyclic.card_mulAut, hPcard, Nat.totient_prime hp.out]
  let f : S →* MulAut (P : Subgroup H) := (MulAut.conjNormal).comp (S : Subgroup H).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs1 : ∀ x : (P : Subgroup H), (s : H) * x * (s : H)⁻¹ = x := by
      intro x
      have h1 : f s = MulAut.conjNormal (s : H) := rfl
      have := congrArg (fun φ : MulAut (P : Subgroup H) => ((φ x : (P : Subgroup H)) : H)) hs
      simp only [h1, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact this
    have hsC : (s : H) ∈ Subgroup.centralizer (P : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hs1 ⟨x, hx⟩
      have h2 : (s : H) * x = x * (s : H) := by
        calc (s : H) * x = ((s : H) * x * (s : H)⁻¹) * s := by group
          _ = x * s := by rw [show ((s : H) * x * (s : H)⁻¹) = x from this]
      exact h2.symm
    rw [hC] at hsC
    have hcop : Nat.Coprime (Nat.card S) (Nat.card P) := by
      rw [hScard, hPcard]
      exact Nat.Coprime.pow_left a (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h))))
    have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj s.2 hsC)
  refine ⟨isCyclic_of_injective f hf, ?_, ?_⟩
  · intro h5
    have hd := Subgroup.card_dvd_of_injective f hf
    rw [hScard, hcardAut, h5] at hd
    interval_cases a <;> simp_all
  · intro h7
    have hd := Subgroup.card_dvd_of_injective f hf
    rw [hScard, hcardAut, h7] at hd
    interval_cases a <;> simp_all

theorem sylow_two_cyclic_of_card {H : Type*} [Group H] [Finite H]
    (hO : ∀ K : Subgroup H, K.Normal → IsPGroup 2 K → K = ⊥)
    {p a : ℕ} [hp : Fact p.Prime] (hp57 : p = 5 ∨ p = 7) (ha : a ≤ 3)
    (hcard : Nat.card H = p * 2 ^ a) (S : Sylow 2 H) :
    IsCyclic S ∧ (p = 5 → a ≤ 2) ∧ (p = 7 → a ≤ 1) := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> decide
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  have hPn := sylow_normal_of_card hO hp57 ha hcard P
  have hC := sylow_centralizer_eq hO hp2 hcard P hPn
  exact sylow_two_cyclic_aux hp57 ha hcard P hPn hC S

theorem cyclic_quotient_of_prime_index_type {X : Type*} [Group X] [Finite X] {N T : Subgroup X}
    (hNn : N.Normal) (hN2 : IsPGroup 2 N)
    (hmax : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K ≤ N)
    (hNT : N ≤ T)
    {p a : ℕ} [hp : Fact p.Prime] (hp57 : p = 5 ∨ p = 7) (ha : a ≤ 3)
    (hcardT : Nat.card T = Nat.card N * 2 ^ a) (hcardX : Nat.card X = p * Nat.card T) :
    (p = 5 → a ≤ 2) ∧ (p = 7 → a ≤ 1) ∧ (1 ≤ a → ∃ g ∈ T, g ^ 2 ^ (a - 1) ∉ N) := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> decide
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hmemker : ∀ x : X, π x = 1 ↔ x ∈ N := fun x => QuotientGroup.eq_one_iff x
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hcardH : Nat.card (X ⧸ N) = p * 2 ^ a := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have : Nat.card (X ⧸ N) * Nat.card N = (p * 2 ^ a) * Nat.card N := by
      rw [← h1, hcardX, hcardT]; ring
    exact Nat.eq_of_mul_eq_mul_right hNpos this
  have hO : ∀ K : Subgroup (X ⧸ N), K.Normal → IsPGroup 2 K → K = ⊥ := by
    intro K hKn hK2
    have hK'n : (K.comap π).Normal := hKn.comap _
    have hK'2 : IsPGroup 2 (K.comap π) := by
      intro x
      obtain ⟨i, hi⟩ := hK2 ⟨π x.1, x.2⟩
      have hi' : π (x.1 ^ 2 ^ i) = 1 := by
        have := congrArg Subtype.val hi
        simpa using this
      have hmem : x.1 ^ 2 ^ i ∈ N := (hmemker _).1 hi'
      obtain ⟨j, hj⟩ := hN2 ⟨x.1 ^ 2 ^ i, hmem⟩
      refine ⟨i + j, ?_⟩
      apply Subtype.ext
      have hj' : (x.1 ^ 2 ^ i) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_add, pow_mul]
      exact hj'
    have hle := hmax _ hK'n hK'2
    refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N k
    have hx : x ∈ K.comap π := hk
    exact (hmemker x).2 (hle hx)
  have hTidx : (T.map π).index = T.index :=
    Subgroup.index_map_eq T (QuotientGroup.mk'_surjective N) (hker.le.trans hNT)
  have hTindex : T.index = p := by
    have := Subgroup.card_mul_index T
    rw [hcardX] at this
    have h2 : Nat.card T * T.index = Nat.card T * p := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  have hcardTm : Nat.card (T.map π) = 2 ^ a := by
    have h1 := Subgroup.card_mul_index (T.map π)
    rw [hTidx, hTindex, hcardH] at h1
    have h2 : Nat.card (T.map π) * p = 2 ^ a * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos h2
  have hTm2 : IsPGroup 2 (T.map π) := IsPGroup.of_card hcardTm
  have hTmidx : ¬ 2 ∣ (T.map π).index := by
    rw [hTidx, hTindex]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h).symm
  let S : Sylow 2 (X ⧸ N) := hTm2.toSylow hTmidx
  obtain ⟨hcyc, h5, h7⟩ := sylow_two_cyclic_of_card hO hp57 ha hcardH S
  refine ⟨h5, h7, fun ha1 => ?_⟩
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard (α := S)
  have hgS : (g : X ⧸ N) ∈ T.map π := g.2
  obtain ⟨t, htT, htg⟩ := hgS
  refine ⟨t, htT, fun hmem => ?_⟩
  have h1 : π (t ^ 2 ^ (a - 1)) = 1 := (hmemker _).2 hmem
  rw [map_pow, htg] at h1
  have hScard : Nat.card S = 2 ^ a := hcardTm
  have hord : orderOf (g : X ⧸ N) = 2 ^ a := by
    rw [← hScard, ← hg]
    exact (Subgroup.orderOf_coe g)
  have hlt : 2 ^ (a - 1) < orderOf (g : X ⧸ N) := by
    rw [hord]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact pow_ne_one_of_lt_orderOf (by positivity) hlt h1

theorem cyclic_quotient_of_prime_index {G : Type*} [Group G] [Finite G] {X N T : Subgroup G}
    (hNX : N ≤ X) (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hmax : ∀ K : Subgroup G, K ≤ X → (∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ N)
    (hNT : N ≤ T) (hTX : T ≤ X)
    {p a : ℕ} [Fact p.Prime] (hp57 : p = 5 ∨ p = 7) (ha : a ≤ 3)
    (hcardT : Nat.card T = Nat.card N * 2 ^ a) (hcardX : Nat.card X = p * Nat.card T) :
    (p = 5 → a ≤ 2) ∧ (p = 7 → a ≤ 1) ∧ (1 ≤ a → ∃ g ∈ T, g ^ 2 ^ (a - 1) ∉ N) := by
  have eN : Nat.card (N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have eT : Nat.card (T.subgroupOf X) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
  have hN'n : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g g.2 n hn
  have hN'2 : IsPGroup 2 (N.subgroupOf X) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hmax' : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K ≤ N.subgroupOf X := by
    intro K hKn hK2
    have hle : K.map X.subtype ≤ N := by
      refine hmax _ ?_ ?_ (hK2.map _)
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro x hx _ ⟨k, hk, rfl⟩
        refine ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, hKn.conj_mem k hk ⟨x, hx⟩, ?_⟩
        simp
    intro k hk
    exact hle ⟨k, hk, rfl⟩
  have key := cyclic_quotient_of_prime_index_type (X := ↥X) hN'n hN'2 hmax'
    (fun x hx => hNT hx) hp57 ha (by rw [eT, eN]; exact hcardT) (by rw [eT]; exact hcardX)
  obtain ⟨h5, h7, h8⟩ := key
  refine ⟨h5, h7, fun ha1 => ?_⟩
  obtain ⟨g, hgT, hgN⟩ := h8 ha1
  refine ⟨(g : G), (Subgroup.mem_subgroupOf.1 hgT), fun hmem => hgN ?_⟩
  rw [Subgroup.mem_subgroupOf]
  simpa using hmem

end CFSG.Quasithin.A10
