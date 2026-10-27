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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Quasithin.H13.VolI

open Subgroup
open scoped commutatorElement MatrixGroups

variable {G : Type*} [Group G]

theorem eq_of_norm_eq_one {Q : Type*} [Group Q] (hc : ∀ a b : Q, a * b = b * a)
    (hs : ∀ a : Q, a * a = 1) {a b c : Q} (h : a * (b * a) * (c * (b * a)) = 1) : a = c := by
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hc }
  have e : a * (b * a) * (c * (b * a)) = (a * a) * (b * b) * (a * c) := by ac_rfl
  rw [e, hs, hs, one_mul, one_mul] at h
  calc a = a * (c * c) := by rw [hs, mul_one]
    _ = (a * c) * c := by rw [mul_assoc]
    _ = c := by rw [h, one_mul]

theorem quotSubgroupOf_comm {U V₁ : Subgroup G} [(V₁.subgroupOf U).Normal]
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁) :
    ∀ a b : ↥U ⧸ V₁.subgroupOf U, a * b = b * a := by
  intro a b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) b
  rw [← map_mul, ← map_mul]
  apply (QuotientGroup.eq).2
  show ((a * b)⁻¹ * (b * a) : ↥U) ∈ V₁.subgroupOf U
  rw [mem_subgroupOf]
  have h := hUc _ (inv_mem b.2) _ (inv_mem a.2)
  simpa [mul_assoc] using h

theorem quotSubgroupOf_sq {U V₁ : Subgroup G} [(V₁.subgroupOf U).Normal]
    (hUs : ∀ x ∈ U, x ^ 2 ∈ V₁) :
    ∀ a : ↥U ⧸ V₁.subgroupOf U, a * a = 1 := by
  intro a
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) a
  rw [← map_mul]
  apply (QuotientGroup.eq_one_iff _).2
  rw [mem_subgroupOf]
  have h := hUs _ a.2
  rwa [pow_two] at h

theorem mem_of_conj_comm_mem {U V₁ W : Subgroup G} {t : G} (hV₁W : V₁ ≤ W) (hWU : W ≤ U)
    (hUN : U ≤ normalizer (V₁ : Set G)) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁)
    (hUs : ∀ x ∈ U, x ^ 2 ∈ V₁) (htW : t ∈ normalizer (W : Set G))
    (hN : ∀ y ∈ U, y * (t * y * t⁻¹) * (t ^ 2 * y * (t ^ 2)⁻¹) ∈ V₁)
    {x : G} (hx : x ∈ U) (hxW : t * x * t⁻¹ * x⁻¹ ∈ W) : x ∈ W := by
  have := normal_subgroupOf_of_le_normalizer hUN
  have hc := quotSubgroupOf_comm hUc
  have hs := quotSubgroupOf_sq hUs
  let π : ↥U →* ↥U ⧸ V₁.subgroupOf U := QuotientGroup.mk' _
  have hπ1 : ∀ a : ↥U, π a = 1 ↔ (a : G) ∈ V₁ := fun a => QuotientGroup.eq_one_iff a
  have hw'W : t * (t * x * t⁻¹ * x⁻¹) * t⁻¹ ∈ W :=
    (mem_normalizer_iff.mp htW _).mp hxW
  have hNx := hN x hx
  have e1 : t * x * t⁻¹ = (t * x * t⁻¹ * x⁻¹) * x := by group
  have e2 : t ^ 2 * x * (t ^ 2)⁻¹ =
      (t * (t * x * t⁻¹ * x⁻¹) * t⁻¹) * ((t * x * t⁻¹ * x⁻¹) * x) := by
    rw [pow_two]; group
  rw [e1, e2] at hNx
  let xa : ↥U := ⟨x, hx⟩
  let wa : ↥U := ⟨_, hWU hxW⟩
  let wa' : ↥U := ⟨_, hWU hw'W⟩
  have hNx' : π (xa * (wa * xa) * (wa' * (wa * xa))) = 1 := (hπ1 _).2 hNx
  simp only [map_mul] at hNx'
  have heq := eq_of_norm_eq_one hc hs hNx'
  have h1 : (xa : G)⁻¹ * wa' ∈ V₁ := by
    have := (QuotientGroup.eq (s := V₁.subgroupOf U)).1 heq
    rwa [mem_subgroupOf] at this
  have e3 : x = (t * (t * x * t⁻¹ * x⁻¹) * t⁻¹) * ((xa : G)⁻¹ * wa')⁻¹ := by
    show x = _ * (x⁻¹ * (t * (t * x * t⁻¹ * x⁻¹) * t⁻¹))⁻¹
    group
  rw [e3]
  exact mul_mem hw'W (inv_mem (hV₁W h1))

theorem norm_mem_of_commutator_sup {U V₁ L₁ : Subgroup G} {t : G}
    (hUN : U ≤ normalizer (V₁ : Set G)) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁)
    (htU : t ∈ normalizer (U : Set G)) (htV₁ : t ∈ normalizer (V₁ : Set G))
    (hL₁U : L₁ ≤ normalizer (U : Set G))
    (ht3 : ∀ u ∈ U, (t ^ 3 * u * (t ^ 3)⁻¹)⁻¹ * u ∈ V₁)
    (hact : ∀ l ∈ L₁, ∃ k : ℕ, ∀ u ∈ U, (l * u * l⁻¹)⁻¹ * (t ^ k * u * (t ^ k)⁻¹) ∈ V₁)
    (hcomm : ⁅U, L₁⁆ ⊔ V₁ = U) :
    ∀ y ∈ U, y * (t * y * t⁻¹) * (t ^ 2 * y * (t ^ 2)⁻¹) ∈ V₁ := by
  have hV₁U : V₁ ≤ U := hcomm ▸ le_sup_right
  have := normal_subgroupOf_of_le_normalizer hUN
  have hc := quotSubgroupOf_comm hUc
  let Q := ↥U ⧸ V₁.subgroupOf U
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hc }
  let ct : ↥U →* ↥U := (U.normalizerMonoidHom ⟨t, htU⟩).toMonoidHom
  have hct : ∀ u : ↥U, ((ct u : ↥U) : G) = t * u * t⁻¹ := fun u =>
    U.normalizerMonoidHom_apply_apply_coe ⟨t, htU⟩ u
  let τ : Q →* Q := QuotientGroup.map _ _ ct (by
    intro v hv
    rw [mem_comap, mem_subgroupOf, hct]
    exact (mem_normalizer_iff.mp htV₁ _).mp hv)
  have hτ : ∀ u : ↥U, τ (QuotientGroup.mk u) = QuotientGroup.mk (ct u) := fun u => rfl
  have hmk : ∀ a b : ↥U, (QuotientGroup.mk a : Q) = QuotientGroup.mk b ↔
      (a : G)⁻¹ * b ∈ V₁ := fun a b => by
    rw [QuotientGroup.eq, mem_subgroupOf]
    rfl
  have hmk1 : ∀ a : ↥U, (QuotientGroup.mk a : Q) = 1 ↔ (a : G) ∈ V₁ := fun a => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hτ3 : ∀ q : Q, τ (τ (τ q)) = q := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hτ, hτ, hτ, hmk]
    have h := ht3 u u.2
    rw [hct, hct, hct]
    have e : t * (t * (t * (u : G) * t⁻¹) * t⁻¹) * t⁻¹ = t ^ 3 * u * (t ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]; group
    rw [e]
    exact h
  let N : Q →* Q := MonoidHom.id Q * τ * τ.comp τ
  have hN : ∀ q, N q = q * τ q * τ (τ q) := fun q => rfl
  have hNτ : ∀ q, N (τ q) = N q := by
    intro q
    rw [hN, hN, hτ3]
    ac_rfl
  have hNk : ∀ k : ℕ, ∀ q, N ((⇑τ)^[k] q) = N q := by
    intro k
    induction k with
    | zero => intro q; rfl
    | succ k ih => intro q; rw [Function.iterate_succ_apply', hNτ, ih]
  have hpow : ∀ (k : ℕ) (u : ↥U), t ^ k * u * (t ^ k)⁻¹ ∈ U := fun k u =>
    (mem_normalizer_iff.mp (pow_mem htU k) u).mp u.2
  have hτk : ∀ (k : ℕ) (u : ↥U),
      (⇑τ)^[k] (QuotientGroup.mk u) = QuotientGroup.mk ⟨t ^ k * u * (t ^ k)⁻¹, hpow k u⟩ := by
    intro k
    induction k with
    | zero =>
      intro u
      rw [Function.iterate_zero_apply]
      congr 1
      apply Subtype.ext
      simp
    | succ k ih =>
      intro u
      rw [Function.iterate_succ_apply', ih, hτ]
      congr 1
      apply Subtype.ext
      rw [hct]
      show t * (t ^ k * (u : G) * (t ^ k)⁻¹) * t⁻¹ = t ^ (k + 1) * u * (t ^ (k + 1))⁻¹
      rw [pow_succ']
      group
  let K : Subgroup G := ((N.comp (QuotientGroup.mk' (V₁.subgroupOf U))).ker).map U.subtype
  have hKmem : ∀ u : ↥U, N (QuotientGroup.mk u) = 1 → (u : G) ∈ K := fun u hu =>
    ⟨u, hu, rfl⟩
  have hK : U ≤ K := by
    calc U = ⁅U, L₁⁆ ⊔ V₁ := hcomm.symm
      _ ≤ K := by
        refine sup_le ?_ ?_
        · rw [commutator_le]
          intro u hu l hl
          have hl' : l * u⁻¹ * l⁻¹ ∈ U := (mem_normalizer_iff.mp (hL₁U hl) _).mp (inv_mem hu)
          have hl'' : l * u * l⁻¹ ∈ U := (mem_normalizer_iff.mp (hL₁U hl) _).mp hu
          have hcU : ⁅u, l⁆ ∈ U := by
            rw [commutatorElement_def]
            have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
            rw [e]
            exact mul_mem hu hl'
          obtain ⟨k, hk⟩ := hact l hl
          refine hKmem ⟨_, hcU⟩ ?_
          have e1 : (⟨⁅u, l⁆, hcU⟩ : ↥U) = ⟨u, hu⟩ * (⟨l * u * l⁻¹, hl''⟩)⁻¹ := by
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
            group
          have e2 : (QuotientGroup.mk ⟨l * u * l⁻¹, hl''⟩ : Q) =
              (⇑τ)^[k] (QuotientGroup.mk ⟨u, hu⟩) := by
            rw [hτk, hmk]
            exact hk u hu
          rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_inv, e2, map_mul, map_inv, hNk,
            mul_inv_cancel]
        · intro v hv
          refine hKmem ⟨v, hV₁U hv⟩ ?_
          rw [(hmk1 _).2 hv, map_one]
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hK hy
  have h1 : N (QuotientGroup.mk y') = 1 := hy'
  rw [hN, hτ, hτ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk1] at h1
  simp only [Subgroup.coe_mul, hct] at h1
  have e : t * (t * (y' : G) * t⁻¹) * t⁻¹ = t ^ 2 * y' * (t ^ 2)⁻¹ := by
    rw [pow_two]; group
  rw [e] at h1
  exact h1

theorem sl2_eq_one_of_fixed {F : Type*} [Field F] [CharP F 2] {m : SL(2, F)} (h3 : m ^ 3 = 1)
    {v : Fin 2 → F} (hv : v ≠ 0) (hmv : m • v = v) : m = 1 := by
  have hM : (m : Matrix (Fin 2) (Fin 2) F).mulVec v = v := hmv
  have hdet : ((m : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hM, Matrix.one_mulVec, sub_self]⟩
  have hdm : (m : Matrix (Fin 2) (Fin 2) F).det = 1 := m.2
  rw [Matrix.det_fin_two] at hdm hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set a := (m : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (m : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (m : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (m : Matrix (Fin 2) (Fin 2) F) 1 1
  have htr : a + d = 0 := by linear_combination hdm - hdet + h2
  have hsq : m ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination a * htr - hdm - h2
    · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination b * htr
    · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination c * htr
    · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination d * htr - hdm - h2
  calc m = m ^ 3 * (m ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hsq]; group

end CFSG.Quasithin.H13.VolI
