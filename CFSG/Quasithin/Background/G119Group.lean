module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import Mathlib.Algebra.Module.StablyFree.Basic
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

namespace CFSG.Quasithin

namespace G11

theorem g119_isPerfect_generalLinearGroup_zmod2 {n : ℕ} (hn : 3 ≤ n) :
    Group.IsPerfect (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
  refine Group.IsPerfect.ofSurjective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)) ?_
  intro g
  have hg : g ∈ MonoidHom.range
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _) := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  exact hg

theorem g119_eq_top_of_normal_sup_zpowers {G : Type*} [Group G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (a : G) (h : N ⊔ Subgroup.zpowers a = ⊤) : N = ⊤ := by
  have hcyc : Subgroup.zpowers (QuotientGroup.mk' N a) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) h
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      at h1
    exact h1
  have : IsCyclic (G ⧸ N) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨_, hcyc⟩
  have hsub : Subsingleton (G ⧸ N) := inferInstance
  refine (Subgroup.eq_top_iff' N).mpr fun g => ?_
  have : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff g).mp (by simpa using this)

theorem g119_eq_top_of_mulEquiv_glFin {G : Type*} [Group G] {n : ℕ} (hn : 3 ≤ n)
    (e : G ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (N : Subgroup G) [N.Normal] (a : G)
    (h : N ⊔ Subgroup.zpowers a = ⊤) : N = ⊤ := by
  have : Group.IsPerfect (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    g119_isPerfect_generalLinearGroup_zmod2 hn
  have : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact g119_eq_top_of_normal_sup_zpowers N a h

theorem g119_card_linearEquiv_eq_card_glFin {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] {n : ℕ} (h : Module.finrank (ZMod 2) M = n) :
    Nat.card (M ≃ₗ[ZMod 2] M) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) M h
  exact (Nat.card_congr (((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M)).toEquiv)).symm

theorem g119_eq_top_of_card_glFin {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    {n : ℕ} (h : Module.finrank (ZMod 2) M = n) (G : Subgroup (M ≃ₗ[ZMod 2] M))
    (e : ↥G ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : G = ⊤ := by
  have : Finite (M ≃ₗ[ZMod 2] M) :=
    Finite.of_injective (fun f : M ≃ₗ[ZMod 2] M => (f : M → M)) DFunLike.coe_injective
  refine G.eq_top_of_card_eq ?_
  rw [Nat.card_congr e.toEquiv, g119_card_linearEquiv_eq_card_glFin h]

theorem g119_not_isSwap_mul_of_commute {α : Type*} [DecidableEq α] {s t : Equiv.Perm α}
    (hs : s.IsSwap) (ht : t.IsSwap) (hc : s * t = t * s) (hne : s ≠ t) : ¬ (s * t).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  rintro ⟨e, f, hef, h⟩
  have hne' : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hne rfl
    · exact hne (Equiv.swap_comm _ _)
  have ha := congrArg (· a) hc
  have hb := congrArg (· b) hc
  have hc' := congrArg (· c) hc
  have hd := congrArg (· d) hc
  have ha' := congrArg (· a) h
  have hb' := congrArg (· b) h
  have hc'' := congrArg (· c) h
  have hd' := congrArg (· d) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at ha hb hc' hd ha' hb' hc'' hd'
  grind

theorem g119_eq_alternatingGroup_of_decomp {α : Type*} [DecidableEq α] [Fintype α]
    (N : Subgroup (Equiv.Perm α)) (hN : N ≤ alternatingGroup α) {s : Equiv.Perm α}
    (hs : s.IsSwap) (hdec : ∀ g : Equiv.Perm α, g ∈ N ∨ g * s ∈ N) : N = alternatingGroup α := by
  refine le_antisymm hN fun g hg => ?_
  rcases hdec g with h | h
  · exact h
  · exfalso
    have h1 := Equiv.Perm.mem_alternatingGroup.mp (hN h)
    have h2 := Equiv.Perm.mem_alternatingGroup.mp hg
    rw [map_mul, h2, hs.sign_eq] at h1
    exact absurd h1 (by decide)

theorem g119_mulEquiv_alternatingGroup_of_range {G : Type*} [Group G] {α : Type*} [DecidableEq α]
    [Fintype α] (ψ : G →* Equiv.Perm α) (hψ : Function.Injective ψ)
    (hr : ψ.range = alternatingGroup α) :
    ∃ φ : G ≃* ↥(alternatingGroup α),
      ∀ g, ((φ g : ↥(alternatingGroup α)) : Equiv.Perm α) = ψ g := by
  have hmem : ∀ g, ψ g ∈ alternatingGroup α := fun g => by
    rw [← hr]
    exact ⟨g, rfl⟩
  let ψ' : G →* ↥(alternatingGroup α) := ψ.codRestrict (alternatingGroup α) hmem
  have hinj : Function.Injective ψ' := fun x y hxy => hψ (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective ψ' := by
    intro x
    obtain ⟨g, hg⟩ : (x : Equiv.Perm α) ∈ ψ.range := by
      rw [hr]
      exact x.2
    exact ⟨g, Subtype.ext hg⟩
  exact ⟨MulEquiv.ofBijective ψ' ⟨hinj, hsurj⟩, fun g => rfl⟩

end G11

end CFSG.Quasithin
