module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Subgroup CFSG

namespace CFSG.RankThree.PartOne

theorem exists_lift_elementaryAbelian {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H)
    {p : ℕ} (hp : p.Prime) (hker : ¬ p ∣ Nat.card ρ.ker) (E : Subgroup H) (hE : E ≤ ρ.range)
    [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2) :
    ∃ E₀ : Subgroup G, IsElementaryAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧ E₀.map ρ = E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 2 hp.ne_zero)
  set P' : Subgroup G := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : H) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P'))
  have hScard : Nat.card S = p ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero 2 hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
      intro x hx hρx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have h1 : orderOf (x' : G) ∣ p ^ 2 := by
        rw [← hScard]
        have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
        simpa [Subgroup.orderOf_coe] using this
      have h2 : orderOf (x' : G) ∣ Nat.card ρ.ker := by
        have hmem : (x' : G) ∈ ρ.ker := hρx
        have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
        simpa [Subgroup.orderOf_coe] using this
      have hcop : Nat.Coprime (p ^ 2) (Nat.card ρ.ker) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup G := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  refine ⟨E₀, ?_, hE₀card, hmapE⟩
  have hEx : ∀ x ∈ E₀, ρ x ∈ E := fun x hx => hmapE ▸ Subgroup.mem_map_of_mem _ hx
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exponent_dvd_p := ?_ }
  · apply hSinj _ (Subgroup.mul_mem _ a.2 b.2) _ (Subgroup.mul_mem _ b.2 a.2)
    have := (IsMulCommutative.is_comm (M := E)).comm ⟨ρ a, hEx _ a.2⟩ ⟨ρ b, hEx _ b.2⟩
    simpa using congrArg Subtype.val this
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    apply hSinj _ (Subgroup.pow_mem _ x.2 p) _ (Subgroup.one_mem _)
    have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (ρ x) (hEx _ x.2)
    simpa using this

end CFSG.RankThree.PartOne
