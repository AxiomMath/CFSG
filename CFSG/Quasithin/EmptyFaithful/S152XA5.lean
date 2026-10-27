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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.S152X

open Equiv Equiv.Perm Subgroup

set_option maxRecDepth 100000

@[expose] def x5 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def y5 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def kv : Finset (Perm (Fin 5)) := {1, x5, y5, x5 * y5}

theorem kv_mul : ∀ a ∈ kv, ∀ b ∈ kv, a * b ∈ kv := by
  unfold kv x5 y5
  decide +kernel

theorem kv_inv : ∀ a ∈ kv, a⁻¹ ∈ kv := by
  unfold kv x5 y5
  decide +kernel

@[expose] def V4 : Subgroup (Perm (Fin 5)) where
  carrier := {p | p ∈ kv}
  mul_mem' := fun {a b} ha hb => kv_mul a ha b hb
  one_mem' := by
    unfold kv
    simp
  inv_mem' := fun {a} ha => kv_inv a ha

theorem mem_V4 {p : Perm (Fin 5)} : p ∈ V4 ↔ p ∈ kv := Iff.rfl

theorem card_kv : kv.card = 4 := by
  unfold kv x5 y5
  decide +kernel

theorem card_V4 : Nat.card V4 = 4 := by
  have h : Nat.card V4 = Nat.card (↑kv : Set (Perm (Fin 5))) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_kv]

theorem V4_le_alt : V4 ≤ alternatingGroup (Fin 5) := by
  intro p hp
  rw [mem_V4] at hp
  rw [mem_alternatingGroup]
  have : ∀ q ∈ kv, Perm.sign q = 1 := by
    unfold kv x5 y5
    decide +kernel
  exact this p hp

theorem normalizes_iff : ∀ g : Perm (Fin 5), Perm.sign g = 1 →
    ((∀ p : Perm (Fin 5), Perm.sign p = 1 → (p ∈ kv ↔ g * p * g⁻¹ ∈ kv)) ↔ g 4 = 4) := by
  unfold kv x5 y5
  decide +kernel

theorem card_stab : (Finset.univ.filter
    (fun g : Perm (Fin 5) => Perm.sign g = 1 ∧ g 4 = 4)).card = 12 := by
  decide +kernel

abbrev A5G : Type := ↥(alternatingGroup (Fin 5))

theorem card_A5G : Nat.card A5G = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem factorization_two_pow_mul' (k n : ℕ) (hn : ¬ 2 ∣ n) : (2 ^ k * n).factorization 2 = k := by
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hn0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hn]

theorem factorization_sixty : (Nat.card A5G).factorization 2 = 2 := by
  rw [card_A5G, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num]
  exact factorization_two_pow_mul' 2 15 (by norm_num)

@[expose] def V4' : Subgroup A5G := V4.subgroupOf (alternatingGroup (Fin 5))

theorem card_V4' : Nat.card V4' = 4 := by
  have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe V4_le_alt).toEquiv
  rw [V4']
  rw [this, card_V4]

theorem mem_normalizer_V4' (g : A5G) : g ∈ Subgroup.normalizer (V4' : Set A5G) ↔
    (g : Perm (Fin 5)) 4 = 4 := by
  rw [Subgroup.mem_normalizer_iff]
  have hg : Perm.sign (g : Perm (Fin 5)) = 1 := mem_alternatingGroup.1 g.2
  rw [← normalizes_iff _ hg]
  constructor
  · intro h p hp
    have := h ⟨p, mem_alternatingGroup.2 hp⟩
    simpa [V4', Subgroup.mem_subgroupOf, mem_V4] using this
  · intro h x
    have := h x.1 (mem_alternatingGroup.1 x.2)
    simpa [V4', Subgroup.mem_subgroupOf, mem_V4] using this

theorem card_normalizer_V4' : Nat.card (Subgroup.normalizer (V4' : Set A5G)) = 12 := by
  have e : ↥(Subgroup.normalizer (V4' : Set A5G)) ≃
      {g : Perm (Fin 5) // Perm.sign g = 1 ∧ g 4 = 4} :=
    { toFun := fun g => ⟨(g.1 : Perm (Fin 5)), mem_alternatingGroup.1 g.1.2,
        (mem_normalizer_V4' g.1).1 g.2⟩
      invFun := fun g => ⟨⟨g.1, mem_alternatingGroup.2 g.2.1⟩, (mem_normalizer_V4' _).2 g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_stab

theorem card_sylow_A5 : Nat.card (Sylow 2 A5G) = 5 := by
  have hp : IsPGroup 2 V4' := IsPGroup.of_card (n := 2) (by rw [card_V4']; norm_num)
  have hidx := Subgroup.card_mul_index V4'
  rw [card_V4', card_A5G] at hidx
  have hodd : ¬ 2 ∣ V4'.index := by
    have : V4'.index = 15 := by omega
    rw [this]
    norm_num
  let P0 : Sylow 2 A5G := hp.toSylow hodd
  rw [Sylow.card_eq_index_normalizer P0]
  have h1 := Subgroup.card_mul_index (Subgroup.normalizer (V4' : Set A5G))
  rw [card_normalizer_V4', card_A5G] at h1
  show (Subgroup.normalizer ((P0 : Subgroup A5G) : Set A5G)).index = 5
  have h0 : (P0 : Subgroup A5G) = V4' := rfl
  rw [h0]
  omega

theorem relIndex_normalizer_A5 (P : Sylow 2 A5G) :
    (P : Subgroup A5G).relIndex (Subgroup.normalizer (P : Set A5G)) = 3 := by
  have hle : (P : Subgroup A5G) ≤ Subgroup.normalizer (P : Set A5G) := Subgroup.le_normalizer
  have h1 := Subgroup.relIndex_mul_index hle
  have h2 : (Subgroup.normalizer (P : Set A5G)).index = 5 := by
    rw [← Sylow.card_eq_index_normalizer P]
    exact card_sylow_A5
  have h3 : (P : Subgroup A5G).index = 15 := by
    have h := Subgroup.card_mul_index (P : Subgroup A5G)
    rw [Sylow.card_eq_multiplicity, factorization_sixty, card_A5G] at h
    omega
  rw [h2, h3] at h1
  omega

theorem relIndex_normalizer_of_surj {X : Type*} [Group X] [Finite X] (ψ : X →* A5G)
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    S.relIndex (Subgroup.normalizer (S : Set X)) = 3 := by
  let P : Sylow 2 X := hS.toSylow hodd
  have hkerS : ψ.ker ≤ S := hker.le_sylow_of_normal P
  let P' : Sylow 2 A5G := Sylow.mapSurjective hψ P
  have hP' : (P' : Subgroup A5G) = S.map ψ := rfl
  have hS' : (S.map ψ).comap ψ = S := Subgroup.comap_map_eq_self hkerS
  set N' := Subgroup.normalizer ((S.map ψ : Subgroup A5G) : Set A5G) with hN'
  have hN : Subgroup.normalizer (S : Set X) = N'.comap ψ := by
    rw [hN', Subgroup.comap_normalizer_eq_of_surjective _ hψ, hS']
  have h3 := relIndex_normalizer_A5 P'
  rw [hP'] at h3
  calc S.relIndex (Subgroup.normalizer (S : Set X)) = S.relIndex (N'.comap ψ) := by rw [hN]
    _ = ((S.map ψ).comap ψ).relIndex (N'.comap ψ) := by rw [hS']
    _ = (S.map ψ).relIndex ((N'.comap ψ).map ψ) := Subgroup.relIndex_comap _ _ _
    _ = 3 := by rw [Subgroup.map_comap_eq_self_of_surjective hψ]; exact h3

end CFSG.Quasithin.S152X
