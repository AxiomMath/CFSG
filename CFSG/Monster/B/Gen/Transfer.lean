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

namespace CFSG.Monster.B

variable {G : Type*} [Group G]

theorem dihedral_conj {a b : G} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : (a * b) ^ (2 * k + 1) = 1) : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hac : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]
  have hack : a * (a * b) ^ k * a⁻¹ = ((a * b) ^ k)⁻¹ := by
    have h := map_pow (MulAut.conj a) (a * b) k
    rw [MulAut.conj_apply, MulAut.conj_apply, hac, inv_pow] at h
    exact h
  have h1 : (a * b) ^ k * a = a * ((a * b) ^ k)⁻¹ := by
    rw [← hack, ha', ← mul_assoc, ← mul_assoc, ha, one_mul]
  have h2 : ((a * b) ^ k)⁻¹ * ((a * b) ^ k)⁻¹ = a * b := by
    have h : (a * b) ^ (2 * k) * (a * b) = 1 := by
      rw [← pow_succ]
      exact hk
    rw [← mul_inv_rev, ← pow_add, ← two_mul, inv_eq_of_mul_eq_one_right h]
  rw [h1, mul_assoc, h2, ← mul_assoc, ha, one_mul]

theorem eq_top_of_transfer {J H : Subgroup G} {τ x w : G}
    (hS : Subgroup.closure (insert τ (J : Set G)) = ⊤)
    (hJ : ∀ g, g ∈ J ↔ g * x = x * g) (hJH : J ≤ H) (hx : x * x = 1) (hw : w * w = 1)
    (hwH : w ∈ H) (hcomm : (τ⁻¹ * x * τ) * x = x * (τ⁻¹ * x * τ)) {k l : ℕ}
    (hk : (x * w) ^ (2 * k + 1) = 1) (hl : (w * (τ⁻¹ * x * τ)) ^ (2 * l + 1) = 1) :
    H = ⊤ := by
  have hx'J : τ⁻¹ * x * τ ∈ J := (hJ _).2 hcomm
  have hxJ : x ∈ J := (hJ x).2 rfl
  have hx'2 : (τ⁻¹ * x * τ) * (τ⁻¹ * x * τ) = 1 := by
    calc (τ⁻¹ * x * τ) * (τ⁻¹ * x * τ) = τ⁻¹ * (x * x) * τ := by group
      _ = 1 := by rw [hx]; group
  have h1 := dihedral_conj hx hw hk
  have h2 := dihedral_conj hw hx'2 hl
  have hσH : (w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k ∈ H :=
    H.mul_mem (H.pow_mem (H.mul_mem hwH (hJH hx'J)) _) (H.pow_mem (H.mul_mem (hJH hxJ) hwH) _)
  have hσ : ((w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k) * x *
      ((w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k)⁻¹ = τ⁻¹ * x * τ := by
    calc ((w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k) * x *
          ((w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k)⁻¹ =
        (w * (τ⁻¹ * x * τ)) ^ l * ((x * w) ^ k * x * ((x * w) ^ k)⁻¹) *
          ((w * (τ⁻¹ * x * τ)) ^ l)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = τ⁻¹ * x * τ := by rw [h1, h2]
  set σ := (w * (τ⁻¹ * x * τ)) ^ l * (x * w) ^ k with hσdef
  have hτσ : τ * σ ∈ J := by
    rw [hJ]
    have h : σ * x = (τ⁻¹ * x * τ) * σ := by rw [← hσ, inv_mul_cancel_right]
    calc τ * σ * x = τ * (σ * x) := mul_assoc _ _ _
      _ = τ * ((τ⁻¹ * x * τ) * σ) := by rw [h]
      _ = x * (τ * σ) := by group
  have hτ : τ ∈ H := by
    have h := H.mul_mem (hJH hτσ) (H.inv_mem hσH)
    rwa [mul_inv_cancel_right] at h
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact hτ
  · exact hJH hg

theorem surjective_of_transfer {B S : Type*} [Group B] [Group S] (ι : B →* S) (u : S)
    {J : Subgroup S} {τ x : S} (K : Subgroup B)
    (hS : Subgroup.closure (insert τ (J : Set S)) = ⊤)
    (hJ : ∀ g, g ∈ J ↔ g * x = x * g)
    (hJK : ∀ g ∈ J, ∃ k ∈ K, g = u⁻¹ * ι k * u) (hx : x * x = 1)
    (hcomm : (τ⁻¹ * x * τ) * x = x * (τ⁻¹ * x * τ)) (W : B)
    (hw : (u⁻¹ * ι W * u) * (u⁻¹ * ι W * u) = 1) {k l : ℕ}
    (hk : (x * (u⁻¹ * ι W * u)) ^ (2 * k + 1) = 1)
    (hl : ((u⁻¹ * ι W * u) * (τ⁻¹ * x * τ)) ^ (2 * l + 1) = 1) :
    Function.Surjective ι := by
  set H : Subgroup S := ι.range.map (MulAut.conj u⁻¹).toMonoidHom with hH
  have memH : ∀ b : B, u⁻¹ * ι b * u ∈ H := by
    intro b
    refine ⟨ι b, ⟨b, rfl⟩, ?_⟩
    simp
  have hJH : J ≤ H := by
    intro g hg
    obtain ⟨k', -, rfl⟩ := hJK g hg
    exact memH k'
  have htop := eq_top_of_transfer (H := H) hS hJ hJH hx hw (memH W) hcomm hk hl
  intro s
  have hs : u⁻¹ * s * u ∈ H := htop ▸ Subgroup.mem_top _
  obtain ⟨t, ⟨b, rfl⟩, hbt⟩ := hs
  refine ⟨b, ?_⟩
  have h1 : u⁻¹ * ι b * u = u⁻¹ * s * u := by
    rw [← hbt]
    simp
  have h2 := congrArg (fun y => u * y * u⁻¹) h1
  simpa [mul_assoc] using h2

theorem isSimpleGroup_of_bijective {B S : Type*} [Group B] [Group S] [IsSimpleGroup S]
    (ι : B →* S) (hinj : Function.Injective ι) (hsurj : Function.Surjective ι) :
    IsSimpleGroup B :=
  (MulEquiv.ofBijective ι ⟨hinj, hsurj⟩).isSimpleGroup

theorem exists_embedding_of_intertwiner {A S : Type*} [Monoid A] [Group S] (β : S →* Aˣ)
    (hβ : Function.Injective β) (a₁ a₂ : A) (T : Aˣ) (s₁ s₂ : S)
    (h₁ : (T : A) * a₁ * ↑T⁻¹ = β s₁) (h₂ : (T : A) * a₂ * ↑T⁻¹ = β s₂) :
    ∃ ι : (Submonoid.closure ({a₁, a₂} : Set A))ˣ →* S, Function.Injective ι ∧
      ∀ u, ((β (ι u) : Aˣ) : A) =
        (T : A) * ((u : Submonoid.closure ({a₁, a₂} : Set A)) : A) * ↑T⁻¹ := by
  set P := Submonoid.closure ({a₁, a₂} : Set A) with hP
  have hmem : ∀ p ∈ P, ∃ g : S, ((β g : Aˣ) : A) = (T : A) * p * ↑T⁻¹ := by
    intro p hp
    induction hp using Submonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨s₁, h₁.symm⟩
      · exact ⟨s₂, h₂.symm⟩
    | one => exact ⟨1, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g * g', ?_⟩
      rw [map_mul, Units.val_mul, hg, hg']
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  choose f hf using fun u : Pˣ => hmem ((u : P) : A) (u : P).2
  have hfmul : ∀ u v : Pˣ, f (u * v) = f u * f v := by
    intro u v
    apply hβ
    apply Units.ext
    rw [map_mul, Units.val_mul, hf, hf, hf, Units.val_mul, Submonoid.coe_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hfone : f 1 = 1 := by
    apply hβ
    apply Units.ext
    rw [hf, map_one]
    simp
  refine ⟨⟨⟨f, hfone⟩, hfmul⟩, ?_, hf⟩
  intro u v huv
  have h := hf u
  change f u = f v at huv
  rw [huv, hf v] at h
  have h' : ((u : P) : A) = ((v : P) : A) := by
    have := congrArg (fun y => (↑T⁻¹ : A) * y * (T : A)) h
    simpa [mul_assoc] using this.symm
  exact Units.ext (Subtype.ext h')

end CFSG.Monster.B
