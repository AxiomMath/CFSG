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

namespace CFSG.Sporadic.ThSchreier

@[expose] noncomputable def autRestrict {G : Type*} [Group G] (α : MulAut G) (K : Subgroup G)
    (h : K.map (α : G →* G) = K) : MulAut K :=
  (α.subgroupMap K).trans (MulEquiv.subgroupCongr h)

theorem autRestrict_apply {G : Type*} [Group G] (α : MulAut G) (K : Subgroup G)
    (h : K.map (α : G →* G) = K) (x : K) : (autRestrict α K h x : G) = α x := rfl

theorem allInner_of_equiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : ∀ α : MulAut K, ∃ m : K, α = MulAut.conj m) :
    ∀ α : MulAut K', ∃ m : K', α = MulAut.conj m := by
  intro α
  obtain ⟨m, hm⟩ := h ((e.trans α).trans e.symm)
  refine ⟨e m, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut K => β (e.symm x)) hm
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, ← e.apply_symm_apply (α x), h1, map_mul, map_mul, map_inv,
    e.apply_symm_apply]

theorem centralizer_map_conj {G : Type*} [Group G] (g A : G) :
    (Subgroup.centralizer {A}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * A * g⁻¹} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * A * g⁻¹) = g * (y * A) * g⁻¹ := by group
      _ = g * (A * y) * g⁻¹ := by rw [hy]
      _ = g * A * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * A = g⁻¹ * (x * (g * A * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * A * g⁻¹ * x) * g := by rw [hx]
      _ = A * (g⁻¹ * x * g) := by group

theorem centralizer_map_aut {G : Type*} [Group G] (α : MulAut G) (A : G) :
    (Subgroup.centralizer {A}).map (α : G →* G) = Subgroup.centralizer {α A} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show α y * α A = α A * α y
    rw [← map_mul, hy, map_mul]
  · intro hx
    refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
    apply α.injective
    rw [map_mul, map_mul, α.apply_symm_apply, hx]

theorem aut_inner_of_two_centralizers {G : Type*} [Group G] (A r g : G) (M M₁ : Subgroup G)
    (hInv : ∀ u : G, orderOf u = 2 → IsConj A u) (hA : orderOf A = 2)
    (hM : Subgroup.centralizer {A} = M) (hAutM : ∀ α : MulAut M, ∃ m : M, α = MulAut.conj m)
    (hrM : r ∈ M) (hrg : r = g * A * g⁻¹) (hM₁ : M₁ = M.map (MulAut.conj g).toMonoidHom)
    (hZ : ∀ s ∈ M ⊓ M₁, (∀ l ∈ M ⊓ M₁, s * l = l * s) → s ∈ Subgroup.closure {A, r})
    (hgen : M ⊔ M₁ = ⊤) : ∀ α : MulAut G, ∃ x : G, α = MulAut.conj x := by
  intro α
  have hM₁c : M₁ = Subgroup.centralizer {r} := by
    rw [hM₁, ← hM, centralizer_map_conj, hrg]
  have hαA : orderOf (α A) = 2 := by rw [MulEquiv.orderOf_eq]; exact hA
  obtain ⟨c, hc⟩ := isConj_iff.1 (hInv (α A) hαA)
  set α₁ : MulAut G := (MulAut.conj c)⁻¹ * α with hα₁
  have hα₁A : α₁ A = A := by
    rw [hα₁, MulAut.mul_apply, ← hc, MulAut.inv_apply, MulAut.conj_symm_apply]
    group
  have hα₁M : M.map (α₁ : G →* G) = M := by rw [← hM, centralizer_map_aut, hα₁A]
  obtain ⟨m₀, hm₀⟩ := hAutM (autRestrict α₁ M hα₁M)
  have hα₁m : ∀ x ∈ M, α₁ x = m₀ * x * (m₀ : G)⁻¹ := by
    intro x hx
    have h1 := congrArg (fun β : MulAut M => (β ⟨x, hx⟩ : G)) hm₀
    simpa [autRestrict_apply, MulAut.conj_apply] using h1
  set β : MulAut G := (MulAut.conj (m₀ : G))⁻¹ * α₁ with hβ
  have hβM : ∀ x ∈ M, β x = x := by
    intro x hx
    rw [hβ, MulAut.mul_apply, hα₁m x hx, MulAut.inv_apply, MulAut.conj_symm_apply]
    group
  have hβr : β r = r := hβM r hrM
  have hβM₁ : M₁.map (β : G →* G) = M₁ := by rw [hM₁c, centralizer_map_aut, hβr]
  have hAutM₁ : ∀ γ : MulAut M₁, ∃ m : M₁, γ = MulAut.conj m := by
    have e : M ≃* M₁ :=
      ((MulAut.conj g).subgroupMap M).trans (MulEquiv.subgroupCongr hM₁.symm)
    exact allInner_of_equiv e hAutM
  obtain ⟨s, hs⟩ := hAutM₁ (autRestrict β M₁ hβM₁)
  have hβs : ∀ y ∈ M₁, β y = s * y * (s : G)⁻¹ := by
    intro y hy
    have h1 := congrArg (fun γ : MulAut M₁ => (γ ⟨y, hy⟩ : G)) hs
    simpa [autRestrict_apply, MulAut.conj_apply] using h1
  have hAM : A ∈ M := by rw [← hM]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hAM₁ : A ∈ M₁ := by
    rw [hM₁c, Subgroup.mem_centralizer_singleton_iff]
    rw [← hM] at hrM
    exact (Subgroup.mem_centralizer_singleton_iff.1 hrM).symm
  have hsL : ∀ l ∈ M ⊓ M₁, (s : G) * l = l * s := by
    intro l hl
    have e1 := hβM l hl.1
    rw [hβs l hl.2] at e1
    calc (s : G) * l = s * l * (s : G)⁻¹ * s := by group
      _ = l * s := by rw [e1]
  have hsM : (s : G) ∈ M := by
    rw [← hM, Subgroup.mem_centralizer_singleton_iff]
    exact hsL A ⟨hAM, hAM₁⟩
  have hsZ : (s : G) ∈ Subgroup.closure {A, r} := hZ s ⟨hsM, s.2⟩ hsL
  have hrc : ∀ y ∈ M₁, r * y = y * r := by
    intro y hy
    rw [hM₁c, Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy.symm
  have hcl : Subgroup.closure {A, r} ≤ M₁ := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAM₁
    · rw [hM₁c]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hpow : ∀ x ∈ Subgroup.closure {A, r}, ∃ i : ℤ, ∀ y ∈ M₁,
      x * y * x⁻¹ = A ^ i * y * (A ^ i)⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, fun y _ => by rw [zpow_one]⟩
      · refine ⟨0, fun y hy => ?_⟩
        rw [zpow_zero, hrc y hy]
        group
    | one => exact ⟨0, fun y _ => by group⟩
    | mul x x' hx hx' ihx ihx' =>
      obtain ⟨i, hi⟩ := ihx
      obtain ⟨i', hi'⟩ := ihx'
      refine ⟨i + i', fun y hy => ?_⟩
      have hy' : A ^ i' * y * (A ^ i')⁻¹ ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem (M₁.zpow_mem hAM₁ _) hy) (M₁.inv_mem (M₁.zpow_mem hAM₁ _))
      calc x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ := by group
        _ = x * (A ^ i' * y * (A ^ i')⁻¹) * x⁻¹ := by rw [hi' y hy]
        _ = A ^ i * (A ^ i' * y * (A ^ i')⁻¹) * (A ^ i)⁻¹ := hi _ hy'
        _ = A ^ (i + i') * y * (A ^ (i + i'))⁻¹ := by rw [zpow_add]; group
    | inv x hx ihx =>
      obtain ⟨i, hi⟩ := ihx
      refine ⟨-i, fun y hy => ?_⟩
      have hxM : x ∈ M₁ := hcl hx
      have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hxM) hy) (M₁.inv_mem (M₁.inv_mem hxM))
      have e := hi _ hy'
      have e' : y = A ^ i * (x⁻¹ * y * x⁻¹⁻¹) * (A ^ i)⁻¹ := by
        rw [← e]
        group
      calc x⁻¹ * y * x⁻¹⁻¹ = A ^ (-i) * (A ^ i * (x⁻¹ * y * x⁻¹⁻¹) * (A ^ i)⁻¹) *
            (A ^ (-i))⁻¹ := by rw [zpow_neg]; group
        _ = A ^ (-i) * y * (A ^ (-i))⁻¹ := by rw [← e']
  obtain ⟨i, hi⟩ := hpow _ hsZ
  have hβeq : β = MulAut.conj (A ^ i) := by
    have hle : M ⊔ M₁ ≤ MonoidHom.eqLocus (β : G →* G)
        ((MulAut.conj (A ^ i) : MulAut G) : G →* G) := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · show β x = A ^ i * x * (A ^ i)⁻¹
        rw [hβM x hx]
        have hxA : x * A = A * x := by
          rw [← hM] at hx
          exact Subgroup.mem_centralizer_singleton_iff.1 hx
        have hc : Commute x (A ^ i) := (show Commute x A from hxA).zpow_right i
        rw [hc.symm.eq]
        group
      · show β y = A ^ i * y * (A ^ i)⁻¹
        rw [hβs y hy, hi y hy]
    rw [hgen] at hle
    exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)
  refine ⟨c * m₀ * A ^ i, MulEquiv.ext fun x => ?_⟩
  have e1 : α = MulAut.conj c * α₁ := by rw [hα₁, mul_inv_cancel_left]
  have e2 : α₁ = MulAut.conj (m₀ : G) * β := by rw [hβ, mul_inv_cancel_left]
  rw [e1, e2, hβeq]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  group

end CFSG.Sporadic.ThSchreier
