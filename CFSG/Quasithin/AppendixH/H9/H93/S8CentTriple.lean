module

public import CFSG.Quasithin.AppendixH.H9.H93.S8CentTriple.AltCentralizerOrder
public import CFSG.Quasithin.AppendixH.H9.H93.S8CentTriple.Z2S4Embedding
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

namespace CFSG.ASVolI.ChH

open Equiv

theorem altInfCentralizer_triple {u : Perm (Fin 8)} (hu : u.cycleType = {2, 2, 2}) :
    Nonempty (↥(alternatingGroup (Fin 8) ⊓ Subgroup.centralizer ({u} : Set (Perm (Fin 8)))) ≃*
      (Multiplicative (ZMod 2) × Perm (Fin 4))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_stdTripleTransposition.trans hu.symm))
  let f : Multiplicative (ZMod 2) × Perm (Fin 4) →* Perm (Fin 8) :=
    (MulAut.conj c).toMonoidHom.comp z2S4Embed
  have hf : ∀ x, f x ∈ alternatingGroup (Fin 8) ⊓
      Subgroup.centralizer ({u} : Set (Perm (Fin 8))) := by
    intro x
    have hx := z2S4Embed_mul_stdTripleTransposition x
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Perm.mem_alternatingGroup]
      show Perm.sign (c * z2S4Embed x * c⁻¹) = 1
      rw [map_mul, map_mul, map_inv, sign_z2S4Embed]
      simp
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      show u * (c * z2S4Embed x * c⁻¹) = c * z2S4Embed x * c⁻¹ * u
      rw [← hc]
      calc c * stdTripleTransposition * c⁻¹ * (c * z2S4Embed x * c⁻¹)
          = c * (stdTripleTransposition * z2S4Embed x) * c⁻¹ := by group
        _ = c * (z2S4Embed x * stdTripleTransposition) * c⁻¹ := by rw [hx]
        _ = c * z2S4Embed x * c⁻¹ * (c * stdTripleTransposition * c⁻¹) := by group
  let φ : Multiplicative (ZMod 2) × Perm (Fin 4) →*
      ↥(alternatingGroup (Fin 8) ⊓ Subgroup.centralizer ({u} : Set (Perm (Fin 8)))) :=
    f.codRestrict _ hf
  have hinj : Function.Injective φ := by
    intro x y h
    exact z2S4Embed_injective ((MulAut.conj c).injective (congrArg Subtype.val h))
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [nat_card_altInfCentralizer_triple hu, Nat.card_prod, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card (α := Perm (Fin 4))]
    simp [Fintype.card_perm, Nat.factorial]
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end CFSG.ASVolI.ChH
