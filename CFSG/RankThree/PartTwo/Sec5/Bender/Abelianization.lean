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

namespace CFSG.RankThree.PartTwo.Sec5.Bender

open CFSG
open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose] def abConj (P : Subgroup X) :
    Subgroup.normalizer (P : Set X) →* MulAut (Abelianization P) where
  toFun g := (P.normalizerMonoidHom g).abelianizationCongr
  map_one' := by
    refine MulEquiv.ext fun v => QuotientGroup.induction_on v fun y => ?_
    change (P.normalizerMonoidHom 1).abelianizationCongr (Abelianization.of y) =
      (1 : MulAut (Abelianization P)) (Abelianization.of y)
    rw [abelianizationCongr_of, map_one]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun v => QuotientGroup.induction_on v fun y => ?_
    change (P.normalizerMonoidHom (g * h)).abelianizationCongr (Abelianization.of y) =
      ((P.normalizerMonoidHom g).abelianizationCongr *
        (P.normalizerMonoidHom h).abelianizationCongr) (Abelianization.of y)
    rw [MulAut.mul_apply, abelianizationCongr_of,
      abelianizationCongr_of, abelianizationCongr_of, map_mul]
    rfl

theorem abConj_of (P : Subgroup X) (g : Subgroup.normalizer (P : Set X)) (y : P) :
    abConj P g (Abelianization.of y) =
      Abelianization.of ⟨(g : X) * y * (g : X)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2⟩ := rfl

theorem of_eq_one_of_mem_commutator (P : Subgroup X) {z : X} (hz : z ∈ ⁅P, P⁆) (hzP : z ∈ P) :
    Abelianization.of (⟨z, hzP⟩ : P) = 1 := by
  have hmap : (commutator P).map P.subtype = ⁅P, P⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hmap] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  change Abelianization.of z' = 1
  rw [← MonoidHom.mem_ker, Abelianization.ker_of]
  exact hz'




@[expose] def abImage (P S : Subgroup X) : Subgroup (MulAut (Abelianization P)) :=
  (S.subgroupOf (Subgroup.normalizer (P : Set X))).map (abConj P)

theorem mem_abImage {P S : Subgroup X} {s : X} (hs : s ∈ S)
    (hsP : s ∈ Subgroup.normalizer (P : Set X)) : abConj P ⟨s, hsP⟩ ∈ abImage P S :=
  ⟨⟨s, hsP⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩

theorem norm_abImage_eq_one {P S : Subgroup X} (hS : S ≤ Subgroup.normalizer (P : Set X))
    (hPS : ⁅P, S⁆ = P) [Fintype (abImage P S)] (v : Abelianization P) :
    ∏ t : abImage P S, (t : MulAut (Abelianization P)) v = 1 := by
  classical
  let N : Abelianization P →* Abelianization P :=
    ∏ t : abImage P S, (t : MulAut (Abelianization P)).toMonoidHom
  have hN : ∀ u, N u = ∏ t : abImage P S, (t : MulAut (Abelianization P)) u := fun u => by
    simp [N]
  have hinv : ∀ τ ∈ abImage P S, ∀ u, N (τ u) = N u := by
    intro τ hτ u
    rw [hN, hN]
    exact Fintype.prod_equiv (Equiv.mulRight ⟨τ, hτ⟩) _ _ fun t => rfl
  have hmemP : ∀ y, y ∈ Subgroup.closure {g | ∃ g₁ ∈ P, ∃ g₂ ∈ S, ⁅g₁, g₂⁆ = g} → y ∈ P := by
    intro y hy
    rw [← Subgroup.commutator_def, hPS] at hy
    exact hy
  have key : ∀ y, y ∈ ⁅P, S⁆ → ∀ hyP : y ∈ P, N (Abelianization.of ⟨y, hyP⟩) = 1 := by
    intro y hy
    rw [Subgroup.commutator_def] at hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg
      intro hyP
      have hg₂N := hS hg₂
      have hc : (g₂ * g₁⁻¹ * g₂⁻¹) ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hg₂N _).mp (P.inv_mem hg₁)
      have hsplit : (⟨⁅g₁, g₂⁆, hyP⟩ : P) = ⟨g₁, hg₁⟩ * ⟨g₂ * g₁⁻¹ * g₂⁻¹, hc⟩ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul]
        group
      have hconj : Abelianization.of (⟨g₂ * g₁⁻¹ * g₂⁻¹, hc⟩ : P) =
          (abConj P ⟨g₂, hg₂N⟩ (Abelianization.of ⟨g₁, hg₁⟩))⁻¹ := by
        rw [← map_inv, ← map_inv]
        rfl
      rw [hsplit, map_mul, hconj, map_mul, map_inv, hinv _ (mem_abImage hg₂ hg₂N),
        mul_inv_cancel]
    | one =>
      intro hyP
      have : (⟨1, hyP⟩ : P) = 1 := rfl
      rw [this, map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hyP
      have : (⟨y * z, hyP⟩ : P) = ⟨y, hmemP y hy⟩ * ⟨z, hmemP z hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz, one_mul]
    | inv y hy ih =>
      intro hyP
      have : (⟨y⁻¹, hyP⟩ : P) = (⟨y, hmemP y hy⟩ : P)⁻¹ := rfl
      rw [this, map_inv, map_inv, ih, inv_one]
  refine QuotientGroup.induction_on v fun x => ?_
  have h1 := key x (hPS.symm ▸ x.2) x.2
  rw [hN] at h1
  exact h1

theorem eq_one_of_forall_abImage_fixed {P S : Subgroup X}
    (hS : S ≤ Subgroup.normalizer (P : Set X))
    (hPS : ⁅P, S⁆ = P) [Fintype (abImage P S)] {p : ℕ}
    (hcop : Nat.Coprime p (Nat.card (abImage P S)))
    {u : Abelianization P} (hup : u ^ p = 1) (hu : ∀ t ∈ abImage P S, t u = u) : u = 1 := by
  classical
  have h1 := norm_abImage_eq_one hS hPS u
  rw [Finset.prod_congr rfl (fun (t : abImage P S) _ => hu t.1 t.2), Finset.prod_const,
    Finset.card_univ] at h1
  have h2 := (pow_gcd_eq_one (a := u) (m := Fintype.card (abImage P S)) (n := p)).mpr ⟨h1, hup⟩
  rw [Nat.gcd_comm, ← Nat.card_eq_fintype_card, Nat.Coprime.gcd_eq_one hcop, pow_one] at h2
  exact h2


theorem abConj_eq_one_of_mem_centralizer {P : Subgroup X} (g : Subgroup.normalizer (P : Set X))
    (hg : (g : X) ∈ Subgroup.centralizer (P : Set X)) : abConj P g = 1 := by
  refine MulEquiv.ext fun v => QuotientGroup.induction_on v fun y => ?_
  change abConj P g (Abelianization.of y) = Abelianization.of y
  rw [abConj_of]
  congr 1
  apply Subtype.ext
  change (g : X) * y * (g : X)⁻¹ = y
  rw [← Subgroup.mem_centralizer_iff.mp hg y y.2, mul_inv_cancel_right]

theorem mem_normalizer_map_subtype_of_normal {N : Subgroup X} {H : Subgroup N} (hH : H.Normal)
    (c : N) : (c : X) ∈ Subgroup.normalizer ((H.map N.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨c * h * c⁻¹, hH.conj_mem h hh c, rfl⟩
  · rintro ⟨h, hh, hhy⟩
    change (h : X) = (c : X) * y * (c : X)⁻¹ at hhy
    have hyN : y ∈ N := by
      have : y = (c : X)⁻¹ * (h : X) * c := by rw [hhy]; group
      rw [this]
      exact N.mul_mem (N.mul_mem (N.inv_mem c.2) h.2) c.2
    refine ⟨c⁻¹ * h * c, ?_, ?_⟩
    · have := hH.conj_mem h hh c⁻¹
      simpa using this
    · change (c : X)⁻¹ * (h : X) * c = y
      rw [hhy]
      group

end CFSG.RankThree.PartTwo.Sec5.Bender
