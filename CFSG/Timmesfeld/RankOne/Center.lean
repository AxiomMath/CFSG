module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

public section

namespace CFSG.Timmesfeld.RankOne

open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commute_of_mem_comap_of_isCyclic {K : Subgroup X} [K.Normal]
    (hKc : K ≤ Subgroup.center X) {R : Subgroup (X ⧸ K)} (hR : IsCyclic R) {x y : X}
    (hx : x ∈ R.comap (QuotientGroup.mk' K)) (hy : y ∈ R.comap (QuotientGroup.mk' K)) :
    Commute x y := by
  obtain ⟨g, hg⟩ := hR.exists_generator
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective K (g : X ⧸ K)
  have hdecomp : ∀ z ∈ R.comap (QuotientGroup.mk' K), ∃ i : ℤ, ∃ k ∈ K, z = x₀ ^ i * k := by
    intro z hz
    obtain ⟨i, hi⟩ := hg ⟨_, hz⟩
    have hi' : (QuotientGroup.mk' K x₀) ^ i = QuotientGroup.mk' K z := by
      rw [hx₀]
      exact congrArg Subtype.val hi
    refine ⟨i, (x₀ ^ i)⁻¹ * z, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff (N := K)]
    change QuotientGroup.mk' K ((x₀ ^ i)⁻¹ * z) = 1
    rw [map_mul, map_inv, map_zpow, hi', inv_mul_cancel]
  obtain ⟨i, k, hk, rfl⟩ := hdecomp x hx
  obtain ⟨j, k', hk', rfl⟩ := hdecomp y hy
  have hkc := Subgroup.mem_center_iff.1 (hKc hk)
  have hk'c := Subgroup.mem_center_iff.1 (hKc hk')
  have c1 : Commute (x₀ ^ i) (x₀ ^ j) := Commute.zpow_zpow_self x₀ i j
  have c2 : Commute (x₀ ^ i) k' := hk'c (x₀ ^ i)
  have c3 : Commute k (x₀ ^ j) := (hkc (x₀ ^ j)).symm
  have c4 : Commute k k' := hk'c k
  exact (c1.mul_right c2).mul_left (c3.mul_right c4)

theorem eq_bot_of_isCyclic_sylow {K : Subgroup X} [K.Normal] (hKc : K ≤ Subgroup.center X)
    (hKodd : Odd (Nat.card K)) {S : Set X} (hS : Subgroup.closure S = ⊤)
    (hSinv : ∀ s ∈ S, s * s = 1)
    (hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ R : Sylow r (X ⧸ K), IsCyclic R) :
    K = ⊥ := by
  classical
  by_contra hK
  obtain ⟨⟨z, hzK⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK
  replace hz1 : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  set r := (orderOf z).minFac with hr
  have hz1' : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.1 h1)
  have hrp : r.Prime := Nat.minFac_prime hz1'
  have : Fact r.Prime := ⟨hrp⟩
  have hrz : r ∣ orderOf z := Nat.minFac_dvd _
  have hzK' : orderOf z ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨z, hzK⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  have hr2 : r ≠ 2 := by
    rintro hr2
    rw [hr2] at hrz
    exact (Nat.not_even_iff_odd.2 hKodd) (even_iff_two_dvd.2 (hrz.trans hzK'))
  let R : Sylow r (X ⧸ K) := Classical.choice Sylow.nonempty
  set T : Subgroup X := (R : Subgroup (X ⧸ K)).comap (QuotientGroup.mk' K) with hT
  have hcomm : ∀ x y : T, x * y = y * x := fun x y =>
    Subtype.ext (commute_of_mem_comap_of_isCyclic hKc (hcyc r hr2 R) x.2 y.2).eq
  have : IsMulCommutative T := ⟨⟨hcomm⟩⟩
  have hnoinv : ∀ t ∈ T, t * t = 1 → t = 1 := by
    intro t ht htt
    have h2 : orderOf (QuotientGroup.mk' K t) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, htt, map_one])
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 R.isPGroup') ⟨_, ht⟩
    replace hk : orderOf (QuotientGroup.mk' K t) = r ^ k :=
      (Subgroup.orderOf_coe (⟨_, ht⟩ : (R : Subgroup (X ⧸ K)))).trans hk
    have h1 : orderOf (QuotientGroup.mk' K t) = 1 := by
      rw [hk] at h2 ⊢
      rcases k with _ | k
      · rfl
      · exfalso
        have : r ∣ 2 := (dvd_pow_self r (Nat.succ_ne_zero k)).trans h2
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 this)
    have htK : t ∈ K := (QuotientGroup.eq_one_iff t).1 (orderOf_eq_one_iff.1 h1)
    have ht2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, htt])
    have htodd : Odd (orderOf t) := by
      have := orderOf_dvd_natCard (⟨t, htK⟩ : K)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hKodd this
    rcases (Nat.dvd_prime Nat.prime_two).1 ht2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at htodd
      exact absurd htodd (by decide)
  let V : X →* T := MonoidHom.transfer (MonoidHom.id T)
  have hVS : ∀ s ∈ S, V s = 1 := by
    intro s hs
    have hss := hSinv s hs
    have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * s ^ k * g₀ ∈ T → g₀⁻¹ * s ^ k * g₀ = s ^ k := by
      intro k g₀ hg
      have hsq : (g₀⁻¹ * s ^ k * g₀) * (g₀⁻¹ * s ^ k * g₀) = 1 := by
        rw [show (g₀⁻¹ * s ^ k * g₀) * (g₀⁻¹ * s ^ k * g₀) = g₀⁻¹ * (s * s) ^ k * g₀ by
          rw [(Commute.refl s).mul_pow]; group]
        rw [hss, one_pow, mul_one, inv_mul_cancel]
      have h1 := hnoinv _ hg hsq
      rw [h1]
      have : s ^ k = g₀ * (g₀⁻¹ * s ^ k * g₀) * g₀⁻¹ := by group
      rw [this, h1, mul_one, mul_inv_cancel]
    rw [MonoidHom.transfer_eq_pow (MonoidHom.id T) s key, MonoidHom.id_apply]
    apply Subtype.ext
    change s ^ T.index = 1
    apply hnoinv _ (MonoidHom.transfer_eq_pow_aux s key)
    rw [← (Commute.refl s).mul_pow, hss, one_pow]
  have hVz : V z = 1 :=
    (Subgroup.closure_le V.ker).2 (fun s hs => hVS s hs) (hS ▸ Subgroup.mem_top z)
  have hkeyz : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ T → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have := Subgroup.mem_center_iff.1 (hKc (K.pow_mem hzK k)) g₀
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  rw [MonoidHom.transfer_eq_pow (MonoidHom.id T) z hkeyz, MonoidHom.id_apply] at hVz
  have hzi : z ^ T.index = 1 := congrArg Subtype.val hVz
  have hdvd : orderOf z ∣ T.index := orderOf_dvd_of_pow_eq_one hzi
  have hidx : T.index = (R : Subgroup (X ⧸ K)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)
  exact R.not_dvd_index (hidx ▸ (hrz.trans hdvd))

end CFSG.Timmesfeld.RankOne
