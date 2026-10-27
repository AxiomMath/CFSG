module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
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

open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem exists_complement_of_sylow_complement [Finite G] {r : ℕ} (hr : r.Prime) {N : Subgroup G}
    [N.Normal] [IsMulCommutative N] (hN : IsPGroup r N) (P : Sylow r G)
    (_hNP : N ≤ (P : Subgroup G)) {K : Subgroup G} (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = P) :
    ∃ D : Subgroup G, N ⊓ D = ⊥ ∧ N ⊔ D = ⊤ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hcop : Nat.Coprime (P : Subgroup G).index (Nat.card N) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (hr.coprime_iff_not_dvd.mpr P.not_dvd_index).symm
  obtain ⟨D, -, hD₁, hD₂⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N
    (P : Subgroup G) K hcop hNK hsup
  exact ⟨D, hD₁, hD₂⟩

private theorem exists_complement_containing_pGroup {T : Type*} [Group T] [Finite T] {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) {N P K A : Subgroup T} [N.Normal]
    [IsMulCommutative N] (hN : IsPGroup r N) (hA : IsPGroup p A) (hNK : N ⊓ K = ⊥)
    (hsup : N ⊔ K = P) (hP : ¬ r ∣ P.index) :
    ∃ D : Subgroup T, A ≤ D ∧ N ⊓ D = ⊥ ∧ N ⊔ D = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hcop : Nat.Coprime P.index (Nat.card N) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (hr.coprime_iff_not_dvd.mpr hP).symm
  obtain ⟨D₀, hcompl, hD₁, hD₂⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N P K hcop hNK hsup
  have hindex : D₀.index = Nat.card N := by
    have h3 : 0 < Nat.card D₀ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left h3
      (by rw [Subgroup.card_mul_index, mul_comm, hcompl.card_mul_card])
  have hpdvd : ¬ p ∣ Nat.card (T ⧸ D₀) := by
    rw [← Subgroup.index, hindex, hn]
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (T ⧸ D₀) hpdvd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix : ∀ a ∈ A, h⁻¹ * a * h ∈ D₀ := by
    intro a ha
    have := hx ⟨a⁻¹, A.inv_mem ha⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq] at this
    simpa [mul_assoc] using this
  refine ⟨D₀.comap (MulAut.conj h⁻¹).toMonoidHom, fun a ha => ?_, ?_, ?_⟩
  · simpa [MulAut.conj_apply] using hfix a ha
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxN, hxD⟩ := hx
    have hxD' : h⁻¹ * x * h ∈ D₀ := by simpa [MulAut.conj_apply] using hxD
    have hxN' : h⁻¹ * x * h ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem x hxN h⁻¹
    have : h⁻¹ * x * h ∈ N ⊓ D₀ := ⟨hxN', hxD'⟩
    rw [hD₁, Subgroup.mem_bot] at this
    calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = 1 := by rw [this]; group
  · refine eq_top_iff.mpr fun g _ => ?_
    have hg : h⁻¹ * g * h ∈ N ⊔ D₀ := by rw [hD₂]; trivial
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hg' : g = (h * n * h⁻¹) * (h * d * h⁻¹) := by
      calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
        _ = h * (n * d) * h⁻¹ := by rw [hnd]
        _ = (h * n * h⁻¹) * (h * d * h⁻¹) := by group
    rw [hg']
    refine Subgroup.mul_mem_sup ((inferInstance : N.Normal).conj_mem n hn h) ?_
    have : h⁻¹ * (h * d * h⁻¹) * h = d := by group
    simpa [MulAut.conj_apply, this] using hd

private theorem exists_complement_containing_pGroup_of_le [Finite G] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) {H N P K A : Subgroup G} [IsMulCommutative N]
    (hN : IsPGroup r N) (hA : IsPGroup p A) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hAH : A ≤ H) (hPH : P ≤ H) (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = P)
    (hP : ¬ r ∣ P.relIndex H) :
    ∃ D : Subgroup G, D ≤ H ∧ A ≤ D ∧ N ⊓ D = ⊥ ∧ N ⊔ D = H := by
  have hNH : N ≤ H := (hsup ▸ le_sup_left : N ≤ P).trans hPH
  have hKH : K ≤ H := (hsup ▸ le_sup_right : K ≤ P).trans hPH
  have : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hNK₁ : N.subgroupOf H ⊓ K.subgroupOf H = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have : (x : G) ∈ N ⊓ K := hx
    rw [hNK, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨D₁, hAD₁, hND₁, hNDtop⟩ := exists_complement_containing_pGroup (T := H) hp hr hpr
    (N := N.subgroupOf H) (A := A.subgroupOf H) hN.comap_subtype hA.comap_subtype hNK₁
    (by rw [← Subgroup.subgroupOf_sup hNH hKH, hsup]) hP
  have hDH : D₁.map H.subtype ≤ H := Subgroup.map_subtype_le D₁
  refine ⟨D₁.map H.subtype, hDH, fun a ha => ⟨⟨a, hAH ha⟩, hAD₁ ha, rfl⟩, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxN, y, hy, rfl⟩ := hx
    have : y ∈ N.subgroupOf H ⊓ D₁ := ⟨hxN, hy⟩
    rw [hND₁, Subgroup.mem_bot] at this
    simp [this]
  · refine le_antisymm (sup_le hNH hDH) fun x hx => ?_
    have hx' : (⟨x, hx⟩ : H) ∈ N.subgroupOf H ⊔ D₁ := by rw [hNDtop]; trivial
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    have : x = (n : G) * (d : G) := congrArg Subtype.val hnd.symm
    rw [this]
    exact Subgroup.mul_mem_sup hn ⟨d, hd, rfl⟩

theorem exists_invariant_complement [Finite G] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) {A W N : Subgroup G} (hA : IsPGroup p A) (_hW : Nat.Coprime p (Nat.card W))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hNW : N ≤ W) [IsMulCommutative N]
    (hN : IsPGroup r N) (hWN : W ≤ Subgroup.normalizer (N : Set G))
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (P : Sylow r W)
    (_hNP : N.subgroupOf W ≤ (P : Subgroup W)) {K : Subgroup W}
    (hNK : N.subgroupOf W ⊓ K = ⊥) (hsup : N.subgroupOf W ⊔ K = (P : Subgroup W)) :
    ∃ W₀ : Subgroup G, W₀ ≤ W ∧ A ≤ Subgroup.normalizer (W₀ : Set G) ∧ N ⊓ W₀ = ⊥ ∧
      N ⊔ W₀ = W := by
  have : Fact r.Prime := ⟨hr⟩
  have hWH : W ≤ W ⊔ A := le_sup_left
  have hAH : A ≤ W ⊔ A := le_sup_right
  have hHN : W ⊔ A ≤ Subgroup.normalizer (N : Set G) := sup_le hWN hAN
  have hHW : W ⊔ A ≤ Subgroup.normalizer (W : Set G) := sup_le Subgroup.le_normalizer hAW
  have hNeq : (N.subgroupOf W).map W.subtype = N := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNW]
  have hNK₀ : N ⊓ K.map W.subtype = ⊥ := by
    rw [← hNeq, ← Subgroup.map_inf_eq _ _ _ W.subtype_injective, hNK, Subgroup.map_bot]
  have hsup₀ : N ⊔ K.map W.subtype = (P : Subgroup W).map W.subtype := by
    rw [← hNeq, ← Subgroup.map_sup, hsup]
  have hPH : (P : Subgroup W).map W.subtype ≤ W ⊔ A := (Subgroup.map_subtype_le _).trans hWH
  have hindex : ∃ n : ℕ, W.relIndex (W ⊔ A) = p ^ n := by
    have : Fact p.Prime := ⟨hp⟩
    have hWnormal : (W.subgroupOf (W ⊔ A)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hHW
    have htop : A.subgroupOf (W ⊔ A) ⊔ W.subgroupOf (W ⊔ A) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hAH hWH, sup_comm A W, Subgroup.subgroupOf_self]
    have key : (W.subgroupOf (W ⊔ A)).relIndex (A.subgroupOf (W ⊔ A)) =
        W.relIndex (W ⊔ A) := by
      rw [← Subgroup.relIndex_sup_right, htop, Subgroup.relIndex_top_right]
      rfl
    have hA₁ : IsPGroup p (A.subgroupOf (W ⊔ A)) := hA.comap_subtype
    obtain ⟨n, hn⟩ := hA₁.index ((W.subgroupOf (W ⊔ A)).subgroupOf (A.subgroupOf (W ⊔ A)))
    exact ⟨n, key.symm.trans hn⟩
  have hPindex : ¬ r ∣ ((P : Subgroup W).map W.subtype).relIndex (W ⊔ A) := by
    rw [← Subgroup.relIndex_mul_relIndex _ W (W ⊔ A) (Subgroup.map_subtype_le _) hWH]
    have hPW : ((P : Subgroup W).map W.subtype).relIndex W = (P : Subgroup W).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    rw [hPW]
    obtain ⟨n, hn⟩ := hindex
    rw [hn]
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact P.not_dvd_index h
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h)).symm
  obtain ⟨D, hDH, hAD, hND, hNDH⟩ := exists_complement_containing_pGroup_of_le hp hr hpr hN hA
    hHN hAH hPH hNK₀ hsup₀ hPindex
  refine ⟨D ⊓ W, inf_le_right, ?_, ?_, ?_⟩
  · exact (le_inf (hAD.trans Subgroup.le_normalizer) hAW).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · exact eq_bot_iff.mpr ((inf_le_inf_left N inf_le_left).trans hND.le)
  · refine le_antisymm (sup_le hNW inf_le_right) fun w hw => ?_
    have hwH : w ∈ N ⊔ D := by rw [hNDH]; exact hWH hw
    have hmul : w ∈ (N : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N D (hDH.trans hHN)]
      exact hwH
    obtain ⟨n, hn, d, hd, rfl⟩ := hmul
    have hdW : d ∈ W := by
      have := W.mul_mem (W.inv_mem (hNW hn)) hw
      simpa using this
    exact Subgroup.mul_mem_sup hn ⟨hd, hdW⟩

end CFSG.SignalizerFunctorTheorem.McBride
