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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.Walter.W67

namespace CentralLift

open scoped commutatorElement

variable {G L : Type} [Group G] [Group L] {Z : Subgroup G} (π : G →* L)

theorem inf_eq_bot_of_isPGroup [Finite G] (hZo : Odd (Nat.card Z)) {W : Subgroup G}
    (hW : IsPGroup 2 W) : W ⊓ Z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hW.to_le (inf_le_left : W ⊓ Z ≤ W)) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ Nat.card Z := by
    rw [← Subgroup.orderOf_mk x (Subgroup.mem_inf.mp hx).2]
    exact orderOf_dvd_natCard _
  rw [hk] at hdvd
  rcases k with _ | k
  · simpa using hk
  · exfalso
    have h2 : 2 ∣ Nat.card Z := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
    have := Nat.odd_iff.mp hZo
    omega

theorem injective_restrict (hker : π.ker = Z) {W : Subgroup G} (hWZ : W ⊓ Z = ⊥) :
    Function.Injective (π.comp W.subtype) := by
  intro x y h
  have hmem : (x : G)⁻¹ * y ∈ W ⊓ Z := by
    refine Subgroup.mem_inf.mpr ⟨W.mul_mem (W.inv_mem x.2) y.2, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    have : π x = π y := h
    rw [this, inv_mul_cancel]
  rw [hWZ, Subgroup.mem_bot] at hmem
  exact Subtype.ext (by rw [← mul_inv_cancel_left (x : G) y, hmem, mul_one])

theorem eq_of_inf_eq_bot (hker : π.ker = Z) {W : Subgroup G} (hWZ : W ⊓ Z = ⊥) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) (h : π x = π y) : x = y :=
  congrArg Subtype.val (injective_restrict π hker hWZ (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

theorem orderOf_map_of_inf_eq_bot (hker : π.ker = Z) {W : Subgroup G} (hWZ : W ⊓ Z = ⊥)
    {x : G} (hx : x ∈ W) : orderOf (π x) = orderOf x := by
  have h := orderOf_injective (π.comp W.subtype) (injective_restrict π hker hWZ) ⟨x, hx⟩
  rwa [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.orderOf_mk] at h

theorem card_eq [Finite G] (hπ : Function.Surjective π) (hker : π.ker = Z) :
    Nat.card G = Nat.card Z * Nat.card L := by
  rw [← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
    mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem card_map_sylow [Finite G] (hπ : Function.Surjective π) (hker : π.ker = Z)
    (hZo : Odd (Nat.card Z)) (P : Sylow 2 G) :
    Nat.card ((P : Subgroup G).map π) = Nat.card (P : Subgroup G) ∧
      Nat.card ((P : Subgroup G).map π) = 2 ^ (Nat.card L).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ((P : Subgroup G).map π) = Nat.card (P : Subgroup G) := by
    have := Subgroup.card_map_of_injective (K := ⊤)
      (injective_restrict π hker (inf_eq_bot_of_isPGroup hZo P.isPGroup'))
    rw [Subgroup.card_top] at this
    rw [← this, ← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨h1, ?_⟩
  have hZ0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have hL0 : Nat.card L ≠ 0 := by
    have : Finite L := Finite.of_surjective π hπ
    exact Nat.card_pos.ne'
  rw [h1, P.card_eq_multiplicity, card_eq π hπ hker, Nat.factorization_mul hZ0 hL0]
  have hZ2 : (Nat.card Z).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by
      have := Nat.odd_iff.mp hZo
      omega)
  simp [hZ2]

theorem exists_involution [Finite G] (hπ : Function.Surjective π) (hker : π.ker = Z)
    (hZo : Odd (Nat.card Z)) {j : L} (hj : orderOf j = 2) :
    ∃ J : G, π J = j ∧ orderOf J = 2 := by
  obtain ⟨J₀, rfl⟩ := hπ j
  obtain ⟨m, hm⟩ := hZo
  have hmap : π (J₀ ^ (2 * m + 1)) = π J₀ := by
    rw [map_pow, pow_succ, pow_mul, ← hj, pow_orderOf_eq_one, one_pow, one_mul]
  refine ⟨J₀ ^ (2 * m + 1), hmap, ?_⟩
  have hsq : J₀ ^ 2 ∈ Z := by
    rw [← hker, MonoidHom.mem_ker, map_pow, ← hj, pow_orderOf_eq_one]
  have h1 : (J₀ ^ (2 * m + 1)) ^ 2 = 1 := by
    have : (J₀ ^ 2) ^ (2 * m + 1) = 1 := by
      have h := pow_card_eq_one' (G := Z) (x := ⟨J₀ ^ 2, hsq⟩)
      rw [hm] at h
      exact congrArg Subtype.val h
    rw [← pow_mul, mul_comm, pow_mul]
    exact this
  have hne : J₀ ^ (2 * m + 1) ≠ 1 := by
    intro h0
    rw [h0, map_one] at hmap
    rw [← hmap, orderOf_one] at hj
    omega
  exact orderOf_eq_prime h1 hne

theorem centralizer_eq_comap [Finite G] (hker : π.ker = Z) (hZc : Z ≤ Subgroup.center G)
    (hZo : Odd (Nat.card Z)) {J : G} (hJ : orderOf J = 2) :
    Subgroup.centralizer ({J} : Set G) =
      (Subgroup.centralizer ({π J} : Set L)).comap π := by
  ext g
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, h, map_mul]
  · intro h
    have hc : π g * π J * (π g)⁻¹ = π J := by rw [h]; group
    obtain ⟨z, hz⟩ : ∃ z, z = J⁻¹ * (g * J * g⁻¹) := ⟨_, rfl⟩
    have hzZ : z ∈ Z := by
      rw [← hker, MonoidHom.mem_ker, hz]
      simp only [map_mul, map_inv]
      rw [hc, inv_mul_cancel]
    have hzc : ∀ x : G, x * z = z * x := fun x =>
      (Subgroup.mem_center_iff.mp (hZc hzZ) x)
    have hJ2 : J * J = 1 := by rw [← sq, ← hJ, pow_orderOf_eq_one]
    have h2 : g * J * g⁻¹ = J * z := by rw [hz]; group
    have hz2 : z * z = 1 := by
      have h1 : (g * J * g⁻¹) * (g * J * g⁻¹) = 1 := by
        calc g * J * g⁻¹ * (g * J * g⁻¹) = g * (J * J) * g⁻¹ := by group
          _ = 1 := by rw [hJ2]; group
      rw [h2] at h1
      calc z * z = (J * J) * (z * z) := by rw [hJ2, one_mul]
        _ = J * (J * z) * z := by group
        _ = J * (z * J) * z := by rw [hzc J]
        _ = J * z * (J * z) := by group
        _ = 1 := h1
    have hz1 : z = 1 := by
      have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
      have hodd : Odd (orderOf z) := by
        have hd : orderOf z ∣ Nat.card Z := by
          rw [← Subgroup.orderOf_mk z hzZ]
          exact orderOf_dvd_natCard _
        exact Odd.of_dvd_nat hZo hd
      have : orderOf z = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
        · exact h1
        · rw [h1] at hodd
          exact absurd hodd (by decide)
      exact orderOf_eq_one_iff.mp this
    have : g * J * g⁻¹ = J := by rw [h2, hz1, mul_one]
    calc g * J = g * J * g⁻¹ * g := by group
      _ = J * g := by rw [this]

theorem eq_of_isPGroup_le_comap [Finite G] (hker : π.ker = Z) (hZc : Z ≤ Subgroup.center G)
    (hZo : Odd (Nat.card Z)) {W W' : Subgroup G}
    (hW : IsPGroup 2 W) (hW' : IsPGroup 2 W') (hle : W' ≤ (W.map π).comap π)
    (hcard : Nat.card W' = Nat.card W) : W' = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.comap_map_eq, hker] at hle
  have hZn : Z.Normal := by
    rw [← hker]; exact π.normal_ker
  have hle' : W' ≤ W := by
    intro x hx
    obtain ⟨w, hw, z, hzZ, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle hx)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hW' ⟨w * z, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨k', hk'⟩ := IsPGroup.iff_orderOf.mp hW ⟨w, hw⟩
    rw [Subgroup.orderOf_mk] at hk'
    have hcomm : Commute w z := Subgroup.mem_center_iff.mp (hZc hzZ) w
    have hz2 : z ^ (2 ^ (k + k')) = 1 := by
      have h1 : (w * z) ^ (2 ^ (k + k')) = 1 := by
        rw [pow_add, pow_mul, ← hk, pow_orderOf_eq_one, one_pow]
      have h2 : w ^ (2 ^ (k + k')) = 1 := by
        rw [pow_add, mul_comm, pow_mul, ← hk', pow_orderOf_eq_one, one_pow]
      rw [hcomm.mul_pow, h2, one_mul] at h1
      exact h1
    have hodd : Odd (orderOf z) := by
      have hd : orderOf z ∣ Nat.card Z := by
        rw [← Subgroup.orderOf_mk z hzZ]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat hZo hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2)
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · rw [hj, pow_succ] at hodd
        exact absurd hodd (by simp [Nat.odd_iff, Nat.mul_mod_left])
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    rw [hj, mul_one]
    exact hw
  exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard])

theorem commutatorElement_mul_central_left {a b z : G} (hz : ∀ g : G, g * z = z * g) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {a b z : G} (hz : ∀ g : G, g * z = z * g) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_sup_eq (hZc : Z ≤ Subgroup.center G) [Z.Normal] (X : Subgroup G) :
    ⁅X ⊔ Z, X ⊔ Z⁆ = ⁅X, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨y, hy, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rw [commutatorElement_mul_central_left (Subgroup.mem_center_iff.mp (hZc hz)),
      commutatorElement_mul_central_right (Subgroup.mem_center_iff.mp (hZc hz'))]
    exact Subgroup.commutator_mem_commutator hx hy
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

end CentralLift

end CFSG.Walter.W67
