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
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne.K133

open Module
open scoped commutatorElement

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem perfect_trivial_on_section [FiniteDimensional K V] (ρ : G →* Module.End K V)
    (hG : Group.IsPerfect G) {W' W : Submodule K V} (hle : W' ≤ W)
    (hdim : finrank K W ≤ finrank K W' + 1)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hW' : ∀ g, ∀ w ∈ W', ρ g w ∈ W') :
    ∀ g, ∀ w ∈ W, ρ g w - w ∈ W' := by
  classical
  by_cases hEq : finrank K W ≤ finrank K W'
  · have h1 : W' = W := Submodule.eq_of_le_of_finrank_le hle hEq
    intro g w hw
    have hw' : w ∈ W' := h1 ▸ hw
    exact W'.sub_mem (hW' g w hw') hw'
  · have hlt : W' < W := lt_of_le_of_ne hle (fun h => hEq (h ▸ le_rfl))
    obtain ⟨f₀, hf₀W, hf₀W'⟩ := IsConcreteLE.exists_of_lt hlt
    have hspan : W' ⊔ (K ∙ f₀) = W := by
      have hle2 : W' ⊔ (K ∙ f₀) ≤ W :=
        sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hf₀W)
      have hlt2 : W' < W' ⊔ (K ∙ f₀) := by
        refine lt_of_le_of_ne le_sup_left fun h => hf₀W' ?_
        rw [h]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self f₀)
      have h3 : finrank K W' < finrank K ↥(W' ⊔ (K ∙ f₀)) :=
        Submodule.finrank_lt_finrank_of_lt hlt2
      exact Submodule.eq_of_le_of_finrank_le hle2 (by omega)
    have hdecomp : ∀ w ∈ W, ∃ w' ∈ W', ∃ c : K, w = w' + c • f₀ := by
      intro w hw
      rw [← hspan] at hw
      obtain ⟨w', hw', z, hz, hwz⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact ⟨w', hw', c, hwz.symm⟩
    have hl : ∀ g, ∃ l : K, ∀ w ∈ W, ρ g w - l • w ∈ W' := by
      intro g
      obtain ⟨w₁, hw₁, l, hl⟩ := hdecomp (ρ g f₀) (hW g f₀ hf₀W)
      refine ⟨l, fun w hw => ?_⟩
      obtain ⟨w', hw', c, rfl⟩ := hdecomp w hw
      have h1 : ρ g (w' + c • f₀) - l • (w' + c • f₀) =
          (ρ g w' - l • w') + c • w₁ := by
        rw [map_add, map_smul, hl]
        simp only [smul_add, smul_smul]
        module
      rw [h1]
      exact W'.add_mem (W'.sub_mem (hW' g w' hw') (W'.smul_mem l hw')) (W'.smul_mem c hw₁)
    let S : Subgroup G :=
      { carrier := {g | ∀ w ∈ W, ρ g w - w ∈ W'}
        one_mem' := by
          intro w hw
          simp
        mul_mem' := by
          intro g h hg hh w hw
          have h1 := hh w hw
          have h2 := hg w hw
          have : ρ (g * h) w - w = ρ g (ρ h w - w) + (ρ g w - w) := by
            rw [map_mul, Module.End.mul_apply, map_sub]
            abel
          rw [this]
          exact W'.add_mem (hW' g _ h1) h2
        inv_mem' := by
          intro g hg w hw
          have h2 := hg w hw
          have : ρ g⁻¹ w - w = -(ρ g⁻¹ (ρ g w - w)) := by
            rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            simp
          rw [this]
          exact W'.neg_mem (hW' g⁻¹ _ h2) }
    have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ S := by
      intro a b u hu
      obtain ⟨la, hla⟩ := hl a
      obtain ⟨lb, hlb⟩ := hl b
      set w : V := ρ ((b * a)⁻¹) u with hwdef
      have hwW : w ∈ W := hW _ u hu
      have hwu : ρ (b * a) w = u := by
        rw [hwdef, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have hcu : ρ ⁅a, b⁆ u = ρ (a * b) w := by
        rw [← hwu, ← Module.End.mul_apply, ← map_mul]
        congr 2
        rw [commutatorElement_def]
        group
      have hab : ρ (a * b) w - (la * lb) • w ∈ W' := by
        have e1 : ρ (a * b) w - (la * lb) • w =
            ρ a (ρ b w - lb • w) + lb • (ρ a w - la • w) := by
          rw [map_mul, Module.End.mul_apply, map_sub, map_smul]
          simp only [smul_sub, smul_smul]
          module
        rw [e1]
        exact W'.add_mem (hW' a _ (hlb w hwW)) (W'.smul_mem lb (hla w hwW))
      have hba : ρ (b * a) w - (lb * la) • w ∈ W' := by
        have e1 : ρ (b * a) w - (lb * la) • w =
            ρ b (ρ a w - la • w) + la • (ρ b w - lb • w) := by
          rw [map_mul, Module.End.mul_apply, map_sub, map_smul]
          simp only [smul_sub, smul_smul]
          module
        rw [e1]
        exact W'.add_mem (hW' b _ (hla w hwW)) (W'.smul_mem la (hlb w hwW))
      have : ρ ⁅a, b⁆ u - u = (ρ (a * b) w - (la * lb) • w) - (ρ (b * a) w - (lb * la) • w) := by
        rw [hcu, ← hwu, mul_comm lb la]
        abel
      rw [this]
      exact W'.sub_mem hab hba
    have htop : S = ⊤ := by
      have h1 : (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), ⊤⁆ := (hG.commutator_eq_top).symm
      refine eq_top_iff.2 ?_
      rw [h1, Subgroup.commutator_le]
      intro a _ b _
      exact hcomm a b
    intro g w hw
    have : g ∈ S := by rw [htop]; exact Subgroup.mem_top g
    exact this w hw

theorem perfect_unipotent_of_nilpotent_three [FiniteDimensional K V] (hV : finrank K V = 3)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G)
    {n : Module.End K V} (hn0 : n ≠ 0) (hnil : IsNilpotent n)
    (hcomm : ∀ g, ρ g * n = n * ρ g) : ∀ g, (ρ g - 1) ^ 3 = 0 := by
  classical
  have chain : ∀ W₁ W₂ : Submodule K V, W₁ ≤ W₂ → finrank K W₁ ≤ 1 →
      finrank K W₂ ≤ finrank K W₁ + 1 → 3 ≤ finrank K W₂ + 1 →
      (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) → (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) →
      ∀ g, (ρ g - 1) ^ 3 = 0 := by
    intro W₁ W₂ h12 hd1 hd2 hd3 hi1 hi2 g
    have e1 := perfect_trivial_on_section ρ hG (W' := ⊥) (W := W₁) bot_le
      (by simpa using hd1) hi1 (by
        intro g w hw
        rw [Submodule.mem_bot] at hw ⊢
        simp [hw])
    have e2 := perfect_trivial_on_section ρ hG (W' := W₁) (W := W₂) h12 hd2 hi2 hi1
    have e3 := perfect_trivial_on_section ρ hG (W' := W₂) (W := ⊤) le_top
      (by simpa [hV] using hd3) (fun g w _ => Submodule.mem_top) hi2
    ext v
    have h3 : ρ g v - v ∈ W₂ := e3 g v Submodule.mem_top
    have h2 : ρ g (ρ g v - v) - (ρ g v - v) ∈ W₁ := e2 g _ h3
    have h1 : ρ g (ρ g (ρ g v - v) - (ρ g v - v)) - (ρ g (ρ g v - v) - (ρ g v - v)) = 0 := by
      have := e1 g _ h2
      rwa [Submodule.mem_bot] at this
    have h4 : (((ρ g - 1 : Module.End K V)) ^ 3) v =
        ρ g (ρ g (ρ g v - v) - (ρ g v - v)) - (ρ g (ρ g v - v) - (ρ g v - v)) := by
      rw [pow_three]
      simp [Module.End.mul_apply]
    rw [h4, h1]
    rfl
  have hn3 : n ^ 3 = 0 := by
    have h1 := IsNilpotent.charpoly_eq_X_pow_finrank hnil
    have h2 := LinearMap.aeval_self_charpoly n
    rw [h1, hV] at h2
    simpa using h2
  have hinvK : ∀ k : ℕ, ∀ g, ∀ w ∈ LinearMap.ker (n ^ k), ρ g w ∈ LinearMap.ker (n ^ k) := by
    intro k g w hw
    have hc : ρ g * n ^ k = n ^ k * ρ g := ((Commute.pow_right (show Commute (ρ g) n from hcomm g) k)).eq
    have : (n ^ k) (ρ g w) = ρ g ((n ^ k) w) := by
      rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply]
    rw [LinearMap.mem_ker] at hw ⊢
    rw [this, hw, map_zero]
  have hinvR : ∀ k : ℕ, ∀ g, ∀ w ∈ LinearMap.range (n ^ k), ρ g w ∈ LinearMap.range (n ^ k) := by
    intro k g w hw
    obtain ⟨y, rfl⟩ := hw
    have hc : ρ g * n ^ k = n ^ k * ρ g := ((Commute.pow_right (show Commute (ρ g) n from hcomm g) k)).eq
    refine ⟨ρ g y, ?_⟩
    rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply]
  by_cases h2 : n ^ 2 = 0
  ·
    have hle : LinearMap.range n ≤ LinearMap.ker n := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have : (n ^ 2) y = 0 := by rw [h2]; rfl
      simpa [pow_two, Module.End.mul_apply] using this
    have hrn := LinearMap.finrank_range_add_finrank_ker n
    have hmono := Submodule.finrank_mono hle
    have hpos : 1 ≤ finrank K (LinearMap.range n) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      apply hn0
      ext y
      have : n y ∈ LinearMap.range n := ⟨y, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    refine chain (LinearMap.range n) (LinearMap.ker n) hle (by omega) (by omega) (by omega)
      (by simpa using hinvR 1) (by simpa using hinvK 1)
  ·
    have hle : LinearMap.range (n ^ 2) ≤ LinearMap.range n := by
      rw [pow_two]
      exact LinearMap.range_comp_le_range n n
    have hstrict : LinearMap.range (n ^ 2) < LinearMap.range n := by
      refine lt_of_le_of_ne hle fun heq => ?_
      apply hn0
      ext y
      have h1 : n y ∈ LinearMap.range (n ^ 2) := by rw [heq]; exact ⟨y, rfl⟩
      obtain ⟨z₁, hz₁⟩ := h1
      have h2 : n z₁ ∈ LinearMap.range (n ^ 2) := by rw [heq]; exact ⟨z₁, rfl⟩
      obtain ⟨z₂, hz₂⟩ := h2
      have h3 : n y = 0 := by
        rw [← hz₁]
        have : (n ^ 2) z₁ = n (n z₁) := by simp [pow_two, Module.End.mul_apply]
        rw [this, ← hz₂]
        have h4 : n ((n ^ 2) z₂) = (n ^ 3) z₂ := by
          rw [pow_succ' n 2, Module.End.mul_apply]
        rw [h4, hn3]
        rfl
      simpa using h3
    have hnetop : LinearMap.range n ≠ ⊤ := by
      intro htop
      have hsurj : ∀ y, ∃ z, n z = y := fun y => by
        have : y ∈ LinearMap.range n := by rw [htop]; exact Submodule.mem_top
        exact this
      have hV0 : ∀ y : V, y = 0 := by
        intro y
        obtain ⟨z₁, rfl⟩ := hsurj y
        obtain ⟨z₂, rfl⟩ := hsurj z₁
        obtain ⟨z₃, rfl⟩ := hsurj z₂
        have : (n ^ 3) z₃ = n (n (n z₃)) := by simp [pow_three, Module.End.mul_apply]
        rw [← this, hn3]
        rfl
      have hsub : Subsingleton V := ⟨fun a b => by rw [hV0 a, hV0 b]⟩
      have := Module.finrank_zero_of_subsingleton (R := K) (M := V)
      omega
    have hr1 : finrank K (LinearMap.range n) < 3 := by
      rw [← hV]
      exact Submodule.finrank_lt hnetop
    have hr2 : finrank K (LinearMap.range (n ^ 2)) < finrank K (LinearMap.range n) :=
      Submodule.finrank_lt_finrank_of_lt hstrict
    have hr3 : 1 ≤ finrank K (LinearMap.range (n ^ 2)) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      apply h2
      ext y
      have : (n ^ 2) y ∈ LinearMap.range (n ^ 2) := ⟨y, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    exact chain (LinearMap.range (n ^ 2)) (LinearMap.range n) hle (by omega) (by omega) (by omega)
      (hinvR 2) (by simpa using hinvR 1)

end CFSG.RankThree.PartOne.K133
