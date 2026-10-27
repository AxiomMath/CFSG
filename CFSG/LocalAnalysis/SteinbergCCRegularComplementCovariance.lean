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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis

theorem submodule_map_linearEquiv_mul {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (a b : V ≃ₗ[K] V) (U : Submodule K V) :
    U.map ((a * b : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (U.map (b : V →ₗ[K] V)).map (a : V →ₗ[K] V) := by
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨b w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem submodule_map_linearEquiv_one {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (U : Submodule K V) : U.map ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) = U := by
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem regular_complement_card_ker_range {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (U R : Submodule (ZMod 2) V) (hUR : IsCompl U R)
    (hU : 0 < Module.finrank (ZMod 2) U) (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hHU : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U) (hHR : ∀ h ∈ H, ∀ r ∈ R, h r = r)
    (hreg : ∀ u ∈ U, ∀ v ∈ U, u ≠ 0 → v ≠ 0 → ∃! h, h ∈ H ∧ h u = v) :
    Nat.card H = 2 ^ Module.finrank (ZMod 2) U - 1 ∧
      ∀ h ∈ H, h ≠ 1 → LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = R ∧
        LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = U := by
  classical
  let b := Module.finBasis (ZMod 2) U
  let u₀ : V := b ⟨0, hU⟩
  have hu₀U : u₀ ∈ U := (b _).2
  have hu₀ : u₀ ≠ 0 := fun h => b.ne_zero _ (Subtype.ext h)
  have hfree : ∀ h ∈ H, ∀ u ∈ U, u ≠ 0 → h u = u → h = 1 := by
    intro h hh u hu hu0 hhu
    obtain ⟨k, -, hk⟩ := hreg u hu u hu hu0 hu0
    exact (hk h ⟨hh, hhu⟩).trans (hk 1 ⟨H.one_mem, rfl⟩).symm
  have hHUmem : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := by
    intro h hh u hu
    rw [← hHU h hh]
    exact Submodule.mem_map_of_mem hu
  have hcard : Nat.card H = 2 ^ Module.finrank (ZMod 2) U - 1 := by
    have hinj : Set.InjOn (fun h : V ≃ₗ[ZMod 2] V => h u₀) (H : Set (V ≃ₗ[ZMod 2] V)) := by
      intro h hh k hk hhk
      obtain ⟨j, -, hj⟩ := hreg u₀ hu₀U (h u₀) (hHUmem h hh u₀ hu₀U) hu₀
        (fun h0 => hu₀ (h.injective (h0.trans h.map_zero.symm)))
      exact (hj h ⟨hh, rfl⟩).trans (hj k ⟨hk, hhk.symm⟩).symm
    have himage : (fun h : V ≃ₗ[ZMod 2] V => h u₀) '' (H : Set (V ≃ₗ[ZMod 2] V)) =
        (U : Set V) \ {0} := by
      ext v
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨hHUmem h hh u₀ hu₀U, fun h0 => hu₀ (h.injective (h0.trans h.map_zero.symm))⟩
      · rintro ⟨hvU, hv0⟩
        obtain ⟨h, ⟨hh, hhv⟩, -⟩ := hreg u₀ hu₀U v hvU hu₀ hv0
        exact ⟨h, hh, hhv⟩
    have hUcard : (U : Set V).ncard = 2 ^ Module.finrank (ZMod 2) U := by
      rw [← Nat.card_coe_set_eq]
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
      rw [Nat.card_zmod] at h
      exact h
    change Nat.card (H : Set (V ≃ₗ[ZMod 2] V)) = _
    rw [Nat.card_coe_set_eq, ← hinj.ncard_image, himage,
      Set.ncard_sdiff_singleton_of_mem (Submodule.zero_mem U), hUcard]
  have hdecomp : ∀ v : V, ∃ u ∈ U, ∃ r ∈ R, u + r = v := by
    intro v
    have hv : v ∈ U ⊔ R := by
      rw [hUR.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, r, hr, huv⟩ := Submodule.mem_sup.mp hv
    exact ⟨u, hu, r, hr, huv⟩
  have hker : ∀ h ∈ H, h ≠ 1 →
      LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = R := by
    intro h hh hne
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hv
      obtain ⟨u, hu, r, hr, rfl⟩ := hdecomp v
      have hhu : h u = u := by
        have h1 : h (u + r) = h u + r := by rw [map_add, hHR h hh r hr]
        exact add_right_cancel (h1.symm.trans hv)
      by_cases hu0 : u = 0
      · rw [hu0, zero_add]
        exact hr
      · exact absurd (hfree h hh u hu hu0 hhu) hne
    · intro r hr
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hHR h hh r hr
  have hrange : ∀ h ∈ H, h ≠ 1 →
      LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = U := by
    intro h hh hne
    set φ : V →ₗ[ZMod 2] V := (h : V →ₗ[ZMod 2] V) - LinearMap.id with hφ
    have hφU : ∀ u ∈ U, φ u ∈ U := fun u hu => by
      rw [hφ, LinearMap.sub_apply, LinearMap.id_apply]
      exact U.sub_mem (hHUmem h hh u hu) hu
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨u, hu, r, hr, rfl⟩ := hdecomp v
      have hφr : φ r = 0 := by
        rw [hφ, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        exact hHR h hh r hr
      rw [map_add, hφr, add_zero]
      exact hφU u hu
    · let ψ : U →ₗ[ZMod 2] U := φ.restrict hφU
      have hψinj : Function.Injective ψ := by
        refine (injective_iff_map_eq_zero ψ).mpr fun u hu => ?_
        by_contra hu0
        apply hne
        refine hfree h hh u u.2 (fun h0 => hu0 (Subtype.ext h0)) ?_
        have h1 : φ u = 0 := congrArg Subtype.val hu
        rw [hφ, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
        exact h1
      intro w hw
      obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.mp hψinj ⟨w, hw⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  exact ⟨hcard, fun h hh hne => ⟨hker h hh hne, hrange h hh hne⟩⟩

theorem binary_regular_complement_stabilizer_covariance {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U R : Submodule (ZMod 2) V)
    (hUR : IsCompl U R) (hn : 3 ≤ Module.finrank (ZMod 2) U)
    (M : Subgroup (V ≃ₗ[ZMod 2] V)) (Δ : Set (Submodule (ZMod 2) V)) (hRΔ : R ∈ Δ)
    (htrans : ∀ Q ∈ Δ, ∀ Q' ∈ Δ, ∃ g ∈ M, Q.map (g : V →ₗ[ZMod 2] V) = Q')
    (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hHnormal : ∀ a ∈ M, R.map (a : V →ₗ[ZMod 2] V) = R → ∀ h ∈ H, a * h * a⁻¹ ∈ H)
    (hHU : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U)
    (hHR : ∀ h ∈ H, ∀ r ∈ R, h r = r)
    (hreg : ∀ u ∈ U, ∀ v ∈ U, u ≠ 0 → v ≠ 0 → ∃! h, h ∈ H ∧ h u = v) :
    Nat.card H = 2 ^ Module.finrank (ZMod 2) U - 1 ∧
      (∀ h ∈ H, h ≠ 1 →
        LinearMap.ker ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = R ∧
          LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = U) ∧
      (∀ a ∈ M, R.map (a : V →ₗ[ZMod 2] V) = R → U.map (a : V →ₗ[ZMod 2] V) = U) ∧
      (∀ Q ∈ Δ, ∃ g ∈ M, R.map (g : V →ₗ[ZMod 2] V) = Q) ∧
      (∀ g ∈ M, ∀ g' ∈ M, R.map (g : V →ₗ[ZMod 2] V) = R.map (g' : V →ₗ[ZMod 2] V) →
        U.map (g : V →ₗ[ZMod 2] V) = U.map (g' : V →ₗ[ZMod 2] V)) ∧
      (∀ g ∈ M, IsCompl (U.map (g : V →ₗ[ZMod 2] V)) (R.map (g : V →ₗ[ZMod 2] V))) ∧
      (∀ a ∈ M, ∀ g ∈ M, ∀ g' ∈ M,
        R.map (g' : V →ₗ[ZMod 2] V) = (R.map (g : V →ₗ[ZMod 2] V)).map (a : V →ₗ[ZMod 2] V) →
        U.map (g' : V →ₗ[ZMod 2] V) = (U.map (g : V →ₗ[ZMod 2] V)).map (a : V →ₗ[ZMod 2] V)) := by
  classical
  obtain ⟨hcard, hkr⟩ := regular_complement_card_ker_range U R hUR (by omega) H hHU hHR hreg
  have hrange : ∀ h ∈ H, h ≠ 1 →
      LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id) = U := fun h hh hne =>
    (hkr h hh hne).2
  let b := Module.finBasis (ZMod 2) U
  let u₀ : V := b ⟨0, by omega⟩
  let u₁ : V := b ⟨1, by omega⟩
  have hu₀U : u₀ ∈ U := (b _).2
  have hu₁U : u₁ ∈ U := (b _).2
  have hu₀ : u₀ ≠ 0 := fun h => b.ne_zero _ (Subtype.ext h)
  have hu₁ : u₁ ≠ 0 := fun h => b.ne_zero _ (Subtype.ext h)
  have hu₀₁ : u₀ ≠ u₁ := fun h => by
    have := b.injective (Subtype.ext h)
    simp [Fin.ext_iff] at this
  obtain ⟨h₀, ⟨hh₀, hh₀u⟩, -⟩ := hreg u₀ hu₀U u₁ hu₁U hu₀ hu₁
  have hh₀ne : h₀ ≠ 1 := fun h => hu₀₁ (by rw [← hh₀u, h]; rfl)
  have hMR : ∀ a ∈ M, R.map (a : V →ₗ[ZMod 2] V) = R → U.map (a : V →ₗ[ZMod 2] V) = U := by
    intro a ha haR
    have hh₁ := hHnormal a ha haR h₀ hh₀
    have hh₁ne : a * h₀ * a⁻¹ ≠ 1 := fun h => hh₀ne (conj_eq_one_iff.mp h)
    have hle : U.map (a : V →ₗ[ZMod 2] V) ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hrange h₀ hh₀ hh₀ne] at hu
      obtain ⟨v, rfl⟩ := hu
      rw [← hrange _ hh₁ hh₁ne]
      refine ⟨a v, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.symm_apply_apply]
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq a U)
  have hwd : ∀ g ∈ M, ∀ g' ∈ M, R.map (g : V →ₗ[ZMod 2] V) = R.map (g' : V →ₗ[ZMod 2] V) →
      U.map (g : V →ₗ[ZMod 2] V) = U.map (g' : V →ₗ[ZMod 2] V) := by
    intro g hg g' hg' hgg'
    have hR : R.map ((g⁻¹ * g' : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = R := by
      rw [submodule_map_linearEquiv_mul, ← hgg', ← submodule_map_linearEquiv_mul, inv_mul_cancel,
        submodule_map_linearEquiv_one]
    have hU := hMR (g⁻¹ * g') (M.mul_mem (M.inv_mem hg) hg') hR
    calc U.map (g : V →ₗ[ZMod 2] V)
        = (U.map ((g⁻¹ * g' : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)).map (g : V →ₗ[ZMod 2] V) := by
          rw [hU]
      _ = U.map ((g * (g⁻¹ * g') : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) :=
          (submodule_map_linearEquiv_mul _ _ _).symm
      _ = U.map (g' : V →ₗ[ZMod 2] V) := by rw [mul_inv_cancel_left]
  refine ⟨hcard, hkr, hMR,
    fun Q hQ => htrans R hRΔ Q hQ, hwd, fun g _ => Submodule.isCompl_map g hUR, ?_⟩
  intro a ha g hg g' hg' h
  rw [← submodule_map_linearEquiv_mul] at h ⊢
  exact hwd g' hg' (a * g) (M.mul_mem ha hg) h

end CFSG.LocalAnalysis
