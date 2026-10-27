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
public import Mathlib.GroupTheory.IsPerfect
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

theorem injective_of_ne_one_central {P J H : Type*} [Group P] [Group J] [Group H]
    [IsSimpleGroup J] [Group.IsPerfect P] (π : P →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center P) (hcard : Nat.card π.ker = 3) (φ : P →* H) {z : P}
    (hz : z ∈ π.ker) (hφ : φ z ≠ 1) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_cases hle : φ.ker ≤ π.ker
  · have hdvd : Nat.card φ.ker ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hfin : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have heq : φ.ker = π.ker := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h3])
      exact hφ (MonoidHom.mem_ker.mp (heq ▸ hz))
  · exfalso
    have hN : (φ.ker.map π).Normal := (MonoidHom.normal_ker φ).map π hπ
    have hne : φ.ker.map π ≠ ⊥ := fun h => hle ((Subgroup.map_eq_bot_iff _).mp h)
    have htop : φ.ker.map π = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
    have key : ∀ a : P, ∃ y ∈ π.ker, φ a = φ y := by
      intro a
      have ha : π a ∈ φ.ker.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.1 ha
      refine ⟨k⁻¹ * a, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hka, inv_mul_cancel]
      · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    have hcomm : commutator P ≤ φ.ker := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨y₁, hy₁, h₁⟩ := key a
      obtain ⟨y₂, hy₂, h₂⟩ := key b
      have hc : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 := by
        rw [← Subgroup.mem_center_iff.1 (hker hy₁) y₂, mul_inv_cancel_right, mul_inv_cancel]
      have hφc := congrArg φ hc
      simp only [map_mul, map_inv, map_one] at hφc
      rw [MonoidHom.mem_ker]
      show φ (a * b * a⁻¹ * b⁻¹) = 1
      simpa only [map_mul, map_inv, h₁, h₂] using hφc
    rw [Group.IsPerfect.commutator_eq_top] at hcomm
    have htop' : φ.ker = ⊤ := top_le_iff.1 hcomm
    exact hφ (MonoidHom.mem_ker.1 (htop' ▸ Subgroup.mem_top z))

theorem normal_and_index_le_two_of_closure_pair {Γ : Type*} [Group Γ] {c d : Γ}
    (hΓ : closure ({c, d} : Set Γ) = ⊤) (K : Subgroup Γ) (hc2 : c ^ 2 = 1) (hd : d ∈ K)
    (hcK : ∀ k ∈ K, c * k * c⁻¹ ∈ K) : K.Normal ∧ K.index ≤ 2 := by
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hle : closure ({c, d} : Set Γ) ≤ normalizer (K : Set Γ) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · refine Subgroup.mem_normalizer_iff.2 fun k => ⟨hcK k, fun hk => ?_⟩
      have h := hcK _ hk
      rw [inv_eq_of_mul_eq_one_right hcc] at h
      have e : g * (g * k * g) * g = (g * g) * k * (g * g) := by simp only [mul_assoc]
      rwa [e, hcc, one_mul, mul_one] at h
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Subgroup.le_normalizer hd
  have hnorm : K.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 (hΓ ▸ hle))
  refine ⟨hnorm, ?_⟩
  let q : Γ →* Γ ⧸ K := QuotientGroup.mk' K
  have hqcc : q c * q c = 1 := by rw [← map_mul, hcc, map_one]
  have hq : ∀ g : Γ, q g = 1 ∨ q g = q c := by
    intro g
    have hg : g ∈ closure ({c, d} : Set Γ) := hΓ ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl ((QuotientGroup.eq_one_iff _).2 hd)
    | one => exact Or.inl (map_one q)
    | mul x y _ _ hx hy =>
      rw [map_mul]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy, hqcc]
    | inv x _ hx =>
      rw [map_inv]
      rcases hx with hx | hx
      · simp [hx]
      · rw [hx]
        exact Or.inr (inv_eq_of_mul_eq_one_right hqcc)
  let f : Fin 2 → Γ ⧸ K := ![1, q c]
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K y
    rcases hq g with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
  calc K.index = Nat.card (Γ ⧸ K) := rfl
    _ ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective f hf
    _ = 2 := by simp

theorem centralizer_eq_and_inv_of_index_two {Γ : Type*} [Group Γ] (K : Subgroup Γ) (x : Γ)
    (hK : K.index = 2) (hx3 : orderOf x = 3) (hxK : ∀ k ∈ K, k * x = x * k)
    (hZ : ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → z ∈ zpowers x)
    (hbad : ∃ b : Γ, b * x ≠ x * b) :
    K = centralizer ({x} : Set Γ) ∧ ∀ b : Γ, b ∉ K → b * x * b⁻¹ = x⁻¹ := by
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hK
  have hle : K ≤ centralizer ({x} : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hxK k hk).symm
  have hne : centralizer ({x} : Set Γ) ≠ ⊤ := by
    intro htop
    obtain ⟨b, hb⟩ := hbad
    have hb' : b ∈ centralizer ({x} : Set Γ) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_centralizer_iff] at hb'
    exact hb (hb' x (Set.mem_singleton x)).symm
  have heq : K = centralizer ({x} : Set Γ) := by
    have hdvd : (centralizer ({x} : Set Γ)).index ∣ 2 := hK ▸ Subgroup.index_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd (Subgroup.index_eq_one.1 h1) hne
    · have hrel := Subgroup.relIndex_mul_index hle
      rw [h2, hK] at hrel
      have h1' : K.relIndex (centralizer ({x} : Set Γ)) = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h1')
  refine ⟨heq, fun b hb => ?_⟩
  have hxmem : x ∈ K := by
    rw [heq, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
  obtain ⟨z, hzdef⟩ : ∃ z, z = b * x * b⁻¹ := ⟨_, rfl⟩
  have hzK : z ∈ K := hzdef ▸ hKn.conj_mem x hxmem b
  have hzc : ∀ k ∈ K, k * z = z * k := by
    intro k hk
    have hk' : b⁻¹ * k * b ∈ K := by simpa using hKn.conj_mem k hk b⁻¹
    have h := hxK _ hk'
    calc k * z = b * ((b⁻¹ * k * b) * x) * b⁻¹ := by rw [hzdef]; group
      _ = b * (x * (b⁻¹ * k * b)) * b⁻¹ := by rw [h]
      _ = z * k := by rw [hzdef]; group
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hZ z hzK hzc)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    omega
  have hz1 : z ≠ 1 := by
    intro h
    apply hx1
    rw [hzdef] at h
    simpa using h
  have hzx : z ≠ x := by
    intro h
    apply hb
    rw [heq, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    rw [hzdef] at h
    calc x * b = (b * x * b⁻¹) * b := by rw [h]
      _ = b * x := by group
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hmod : x ^ (n % 3) = x ^ n := by simpa [hx3] using zpow_mod_orderOf x n
  have hzmod : z = x ^ (n % 3) := by rw [hmod, hn]
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact absurd (by rw [hzmod, h0, zpow_zero]) hz1
  · exact absurd (by rw [hzmod, h1, zpow_one]) hzx
  · rw [← hzdef, hzmod, h2, zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hx3')

theorem commute_of_normal_zpowers {Γ : Type*} [Group Γ] (K : Subgroup Γ)
    [Group.IsPerfect K] {u : Γ} (hn : (zpowers u).Normal) :
    ∀ k ∈ K, k * u = u * k := by
  intro k hk
  let ρ : K →* (ZMod (Nat.card (zpowers u)))ˣ :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).toMonoidHom.comp
      ((MulAut.conjNormal (H := zpowers u)).comp K.subtype)
  have hker : ρ.ker = ⊤ := by
    have h := Abelianization.commutator_subset_ker ρ
    rwa [Group.IsPerfect.commutator_eq_top, top_le_iff] at h
  have h1 : ρ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top _)
  have h2 : (MulAut.conjNormal (H := zpowers u) k) = 1 :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).injective (by simpa [ρ] using h1)
  have h3 := MulAut.conjNormal_apply (H := zpowers u) k ⟨u, Subgroup.mem_zpowers u⟩
  rw [h2] at h3
  have h4 : u = k * u * k⁻¹ := h3
  calc k * u = (k * u * k⁻¹) * k := by group
    _ = u * k := by rw [← h4]

theorem mem_normalizer_zpowers_iff_of_isOfFinOrder {Γ : Type*} [Group Γ] {y : Γ}
    (hy : IsOfFinOrder y) {b : Γ} :
    b ∈ normalizer (zpowers y : Set Γ) ↔ b * y * b⁻¹ ∈ zpowers y := by
  constructor
  · intro hb
    exact (mem_normalizer_iff.1 hb y).1 (mem_zpowers y)
  · intro hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hb
    have hconj : ∀ n : ℤ, b * y ^ n * b⁻¹ = y ^ (k * n) := by
      intro n
      rw [zpow_mul, hk]
      simp [conj_zpow]
    have hfin : Finite (zpowers y) := by
      have := hy.orderOf_pos
      exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
    let c : zpowers y → zpowers y := fun z =>
      ⟨b * (z : Γ) * b⁻¹, by
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 z.2
        exact mem_zpowers_iff.2 ⟨k * n, by rw [← hn, hconj]⟩⟩
    have hinj : Function.Injective c := by
      intro z z' h
      apply Subtype.ext
      have h1 : b * (z : Γ) * b⁻¹ = b * (z' : Γ) * b⁻¹ := congrArg Subtype.val h
      have h2 := mul_right_cancel h1
      exact mul_left_cancel h2
    have hsurj : Function.Surjective c := Finite.surjective_of_injective hinj
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hh
      exact mem_zpowers_iff.2 ⟨k * n, (hconj n).symm⟩
    · intro hh
      obtain ⟨z, hz⟩ := hsurj ⟨b * h * b⁻¹, hh⟩
      have : b * (z : Γ) * b⁻¹ = b * h * b⁻¹ := congrArg Subtype.val hz
      have h2 : (z : Γ) = h := by simpa using this
      rw [← h2]
      exact z.2

end CFSG.Sporadic.Recognition.LyonsSims
