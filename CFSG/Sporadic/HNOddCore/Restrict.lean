module

public import CFSG.Sporadic.Schreier.ONPermArr
public import Certificates.Data.CFSGNative.ONSchreier.Tools
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

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {N : ℕ}

structure PtList (N : ℕ) (F : Array ℕ) : Prop where
  lt : ∀ k < F.size, F[k]! < N
  inj : ∀ k < F.size, ∀ l < F.size, F[k]! = F[l]! → k = l

@[expose] def PtList.pt {F : Array ℕ} (hF : PtList N F) (k : Fin F.size) : Fin N :=
  ⟨F[(k : ℕ)]!, hF.lt k k.2⟩

theorem PtList.pt_val {F : Array ℕ} (hF : PtList N F) (k : Fin F.size) :
    ((hF.pt k : Fin N) : ℕ) = F[(k : ℕ)]! := rfl

theorem PtList.pt_injective {F : Array ℕ} (hF : PtList N F) : Function.Injective hF.pt :=
  fun k l h => Fin.ext (hF.inj k k.2 l l.2 (congrArg Fin.val h))

theorem pointsOK_spec {F rpos : Array ℕ} (h : pointsOK N F rpos = true) :
    rpos.size = N ∧ ∀ k < F.size, F[k]! < N ∧ rpos[F[k]!]! = k := by
  unfold pointsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have := allBelowN_spec h.2 hk
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem ptList_of_pointsOK {F rpos : Array ℕ} (h : pointsOK N F rpos = true) : PtList N F where
  lt k hk := ((pointsOK_spec h).2 k hk).1
  inj k hk l hl he := by
    rw [← ((pointsOK_spec h).2 k hk).2, ← ((pointsOK_spec h).2 l hl).2, he]

section Action

variable {G : Type*} [Group G] [MulAction G (Fin N)] {F : Array ℕ} (hF : PtList N F)

@[expose] def Preserves (K : Subgroup G) : Prop :=
  ∀ g ∈ K, ∀ k : Fin F.size, ∃ l : Fin F.size, g • hF.pt k = hF.pt l

variable {hF} {K : Subgroup G} (hK : Preserves hF K)

@[expose] def resFun (g : K) (k : Fin F.size) : Fin F.size := Classical.choose (hK g g.2 k)

theorem pt_resFun (g : K) (k : Fin F.size) : hF.pt (resFun hK g k) = (g : G) • hF.pt k :=
  (Classical.choose_spec (hK g g.2 k)).symm

theorem resFun_one (k : Fin F.size) : resFun hK 1 k = k :=
  hF.pt_injective (by rw [pt_resFun, Subgroup.coe_one, one_smul])

theorem resFun_mul (g h : K) (k : Fin F.size) :
    resFun hK (g * h) k = resFun hK g (resFun hK h k) :=
  hF.pt_injective (by rw [pt_resFun, pt_resFun, pt_resFun, Subgroup.coe_mul, mul_smul])

@[expose] def resHom : K →* Equiv.Perm (Fin F.size) where
  toFun g :=
    { toFun := resFun hK g
      invFun := resFun hK g⁻¹
      left_inv := fun k => by rw [← resFun_mul, inv_mul_cancel, resFun_one]
      right_inv := fun k => by rw [← resFun_mul, mul_inv_cancel, resFun_one] }
  map_one' := Equiv.ext fun k => resFun_one hK k
  map_mul' g h := Equiv.ext fun k => resFun_mul hK g h k

theorem resHom_apply (g : K) (k : Fin F.size) : resHom hK g k = resFun hK g k := rfl

theorem pt_resHom (g : K) (k : Fin F.size) : hF.pt (resHom hK g k) = (g : G) • hF.pt k :=
  pt_resFun hK g k

theorem prep_resHom {rpos : Array ℕ} (hpos : pointsOK N F rpos = true) {T : Array ℕ} (g : K)
    (hT : PRep N T (MulAction.toPerm (g : G))) :
    PRep F.size (restrictTab T F rpos) (resHom hK g) := by
  intro k
  have hk : (k : ℕ) < F.size := k.2
  have h1 : (restrictTab T F rpos)[(k : ℕ)]! = rpos[T[F[(k : ℕ)]!]!]! := by
    rw [restrictTab, getElem!_pos _ _ (by simp [hk]), Array.getElem_map,
      ← getElem!_pos F (k : ℕ) hk]
  rw [h1]
  have e1 : T[F[(k : ℕ)]!]! = (((g : G) • hF.pt k : Fin N) : ℕ) := by
    have := hT (hF.pt k)
    rwa [MulAction.toPerm_apply] at this
  rw [e1, ← pt_resHom hK g k, PtList.pt_val]
  exact ((pointsOK_spec hpos).2 _ (resHom hK g k).2).2

end Action

section Fixed

variable {G : Type*} [Group G] [MulAction G (Fin N)] {F : Array ℕ} (hF : PtList N F)

theorem fixed_preserved {t : G} (hfix : ∀ x : Fin N, t • x = x ↔ ∃ k : Fin F.size, hF.pt k = x) :
    Preserves hF (Subgroup.centralizer {t}) := by
  intro g hg k
  have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hk : t • hF.pt k = hF.pt k := (hfix _).2 ⟨k, rfl⟩
  obtain ⟨l, hl⟩ := (hfix (g • hF.pt k)).1 (by rw [← mul_smul, ← hgt, mul_smul, hk])
  exact ⟨l, hl.symm⟩

end Fixed

end CFSG.Sporadic.HNOddCore
