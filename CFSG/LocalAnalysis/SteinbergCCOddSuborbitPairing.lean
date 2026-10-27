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

open MulAction

theorem odd_degree_two_suborbit_pairing {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    [IsPretransitive G Ω] (hN : Odd (Nat.card Ω)) (α : Ω) (S T : Set Ω)
    (hS : ∃ β, β ≠ α ∧ orbit (stabilizer G α) β = S)
    (hT : ∃ γ, γ ≠ α ∧ orbit (stabilizer G α) γ = T) (hST : S ≠ T)
    (hcover : ∀ x : Ω, x ≠ α → x ∈ S ∨ x ∈ T) (hs : Odd S.ncard) :
    (∀ β ∈ S, ∀ β' ∈ S, orbit G (α, β) = orbit G (α, β')) ∧
      (∀ γ ∈ T, ∀ γ' ∈ T, orbit G (α, γ) = orbit G (α, γ')) ∧
      S.ncard = T.ncard ∧
      ∀ β ∈ S, ∀ γ ∈ T,
        Prod.swap '' orbit G (α, β) = orbit G (α, γ) ∧
        Prod.swap '' orbit G (α, γ) = orbit G (α, β) ∧
        ∀ x y : Ω, x ≠ y → Xor ((x, y) ∈ orbit G (α, β)) ((y, x) ∈ orbit G (α, β)) := by
  classical
  obtain ⟨β₀, hβ₀α, hβ₀S⟩ := hS
  obtain ⟨γ₀, hγ₀α, hγ₀T⟩ := hT
  have hfib : ∀ β y : Ω, (α, y) ∈ orbit G (α, β) ↔ y ∈ orbit (stabilizer G α) β := by
    intro β y
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨⟨g, congrArg Prod.fst hg⟩, congrArg Prod.snd hg⟩
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G), ?_⟩
      show (h : G) • (α, β) = (α, (h : G) • β)
      rw [Prod.smul_mk, mem_stabilizer_iff.mp h.2]
  have hSorb : ∀ β ∈ S, orbit G (α, β) = orbit G (α, β₀) := fun β hβ =>
    orbit_eq_iff.mpr ((hfib β₀ β).mpr (by rw [hβ₀S]; exact hβ))
  have hTorb : ∀ γ ∈ T, orbit G (α, γ) = orbit G (α, γ₀) := fun γ hγ =>
    orbit_eq_iff.mpr ((hfib γ₀ γ).mpr (by rw [hγ₀T]; exact hγ))
  have hβ₀mem : β₀ ∈ S := by rw [← hβ₀S]; exact mem_orbit_self β₀
  have hγ₀mem : γ₀ ∈ T := by rw [← hγ₀T]; exact mem_orbit_self γ₀
  have hoff : ∀ β : Ω, β ≠ α → ∀ p ∈ orbit G (α, β), p.1 ≠ p.2 := by
    rintro β hβ p ⟨g, rfl⟩ h
    exact hβ (smul_left_cancel g h).symm
  have hcov : ∀ x y : Ω, x ≠ y → (x, y) ∈ orbit G (α, β₀) ∨ (x, y) ∈ orbit G (α, γ₀) := by
    intro x y hxy
    obtain ⟨g, hg⟩ := exists_smul_eq G x α
    have hgy : g • y ≠ α := fun h => hxy (smul_left_cancel g (hg.trans h.symm))
    have hmem : (x, y) ∈ orbit G (α, g • y) := ⟨g⁻¹, by
      show g⁻¹ • (α, g • y) = (x, y)
      rw [Prod.smul_mk, ← hg, inv_smul_smul, inv_smul_smul]⟩
    rcases hcover _ hgy with h | h
    · left
      rwa [← hSorb _ h]
    · right
      rwa [← hTorb _ h]
  have hdisj : ∀ p, p ∈ orbit G (α, β₀) → p ∉ orbit G (α, γ₀) := by
    intro p hpS hpT
    have h3 : (α, γ₀) ∈ orbit G (α, β₀) := by
      rw [← orbit_eq_iff.mpr hpS, orbit_eq_iff.mpr hpT]
      exact mem_orbit_self _
    apply hST
    rw [← hβ₀S, ← hγ₀T]
    exact (orbit_eq_iff.mpr ((hfib β₀ γ₀).mp h3)).symm
  have hcard : ∀ β : Ω,
      (orbit G (α, β)).ncard = (orbit (stabilizer G α) β).ncard * Nat.card Ω := by
    intro β
    have hstab : stabilizer G (α, β) = stabilizer G α ⊓ stabilizer G β := by
      ext g
      simp only [mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_mk, Prod.mk.injEq]
    have hstab' : stabilizer (stabilizer G α) β = (stabilizer G β).subgroupOf (stabilizer G α) := by
      ext h
      simp only [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
    rw [← index_stabilizer, ← index_stabilizer, ← index_stabilizer_of_transitive G α, hstab,
      hstab', ← Subgroup.relIndex_mul_index (inf_le_left : stabilizer G α ⊓ stabilizer G β ≤ _),
      Subgroup.inf_relIndex_left]
    rfl
  have hkey : ∀ p ∈ orbit G (α, β₀), Prod.swap p ∉ orbit G (α, β₀) := by
    intro p hp hsp
    have hinv : ∀ q ∈ orbit G (α, β₀), Prod.swap q ∈ orbit G (α, β₀) := by
      intro q hq
      rw [← orbit_eq_iff.mpr hp] at hq
      obtain ⟨g, rfl⟩ := hq
      obtain ⟨k, hk⟩ := hsp
      change k • (α, β₀) = Prod.swap p at hk
      refine ⟨g * k, ?_⟩
      show (g * k) • (α, β₀) = Prod.swap (g • p)
      rw [mul_smul, hk]
      rfl
    let σ : Equiv.Perm (orbit G (α, β₀)) :=
      { toFun := fun q => ⟨Prod.swap q.1, hinv q.1 q.2⟩
        invFun := fun q => ⟨Prod.swap q.1, hinv q.1 q.2⟩
        left_inv := fun q => Subtype.ext (Prod.swap_swap q.1)
        right_inv := fun q => Subtype.ext (Prod.swap_swap q.1) }
    have hσ : σ ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      exact Equiv.ext fun q => Subtype.ext (Prod.swap_swap q.1)
    have : Fintype (orbit G (α, β₀)) := Fintype.ofFinite _
    have hodd : ¬ 2 ∣ Fintype.card (orbit G (α, β₀)) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcard, hβ₀S]
      exact (hs.mul hN).not_two_dvd_nat
    obtain ⟨q, hq⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
    exact hoff β₀ hβ₀α q.1 q.2 (congrArg Prod.snd (congrArg Subtype.val hq))
  have hswapS : ∀ q ∈ orbit G (α, β₀), Prod.swap q ∈ orbit G (α, γ₀) := by
    intro q hq
    have hne : (Prod.swap q).1 ≠ (Prod.swap q).2 := (hoff β₀ hβ₀α q hq).symm
    exact (hcov _ _ hne).resolve_left (hkey q hq)
  have hswapT : ∀ p ∈ orbit G (α, γ₀), Prod.swap p ∈ orbit G (α, β₀) := by
    intro p hp
    have h1 : (β₀, α) ∈ orbit G (α, γ₀) := hswapS _ (mem_orbit_self _)
    rw [← orbit_eq_iff.mpr h1] at hp
    obtain ⟨g, rfl⟩ := hp
    exact ⟨g, rfl⟩
  have himS : Prod.swap '' orbit G (α, β₀) = orbit G (α, γ₀) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hswapS q hq
    · intro hp
      exact ⟨Prod.swap p, hswapT p hp, Prod.swap_swap p⟩
  have himT : Prod.swap '' orbit G (α, γ₀) = orbit G (α, β₀) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hswapT q hq
    · intro hp
      exact ⟨Prod.swap p, hswapS p hp, Prod.swap_swap p⟩
  have hcardST : S.ncard = T.ncard := by
    have : Nonempty Ω := ⟨α⟩
    have h := Set.ncard_image_of_injective (orbit G (α, β₀)) Prod.swap_injective
    rw [himS, hcard, hcard, hβ₀S, hγ₀T] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  refine ⟨fun β hβ β' hβ' => (hSorb β hβ).trans (hSorb β' hβ').symm,
    fun γ hγ γ' hγ' => (hTorb γ hγ).trans (hTorb γ' hγ').symm, hcardST,
    fun β hβ γ hγ => ?_⟩
  rw [hSorb β hβ, hTorb γ hγ]
  refine ⟨himS, himT, fun x y hxy => ?_⟩
  rcases hcov x y hxy with h | h
  · exact Or.inl ⟨h, fun h' => hdisj _ h' (hswapS _ h)⟩
  · exact Or.inr ⟨hswapT _ h, fun h' => hdisj _ h' h⟩

end CFSG.LocalAnalysis
