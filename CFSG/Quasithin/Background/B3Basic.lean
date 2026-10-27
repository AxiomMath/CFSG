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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Cases
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

namespace CFSG.Quasithin.B3

@[expose] def cj {G : Type*} [Group G] (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_cj {G : Type*} [Group G] {g : G} {A : Subgroup G} {x : G} :
    x ∈ cj g A ↔ g⁻¹ * x * g ∈ A := by
  unfold cj
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (A : Subgroup G)
    (hA : IsPGroup 2 A) : ∃ g : G, cj g A ≤ T := by
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  refine ⟨g, ?_⟩
  have h1 : (g • P : Sylow 2 G).toSubgroup = T.toSubgroup := by rw [hg]
  have h2 : (g • P : Sylow 2 G).toSubgroup = P.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [← h1, h2]
  exact Subgroup.map_mono hAP

def extSub {G : Type*} [Group G] (K' : Subgroup G) (x : G) (hx : x * x = 1)
    (hcomm : ∀ k ∈ K', x * k = k * x) : Subgroup G where
  carrier := {y | y ∈ K' ∨ x * y ∈ K'}
  one_mem' := Or.inl K'.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (K'.mul_mem ha hb)
    · right
      have : x * (a * b) = a * (x * b) := by
        rw [← mul_assoc, hcomm a ha, mul_assoc]
      rw [this]
      exact K'.mul_mem ha hb
    · right
      rw [← mul_assoc]
      exact K'.mul_mem ha hb
    · left
      have h1 : a = x * a * x := by
        have := hcomm (x * a) ha
        rw [← mul_assoc, hx, one_mul] at this
        exact this
      have h2 : a * b = (x * a) * (x * b) := by
        calc a * b = (x * a * x) * b := by rw [← h1]
          _ = (x * a) * (x * b) := by rw [mul_assoc]
      rw [h2]
      exact K'.mul_mem ha hb
  inv_mem' := by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (K'.inv_mem hy)
    · right
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
      have hyk : y = x * (x * y) := by rw [← mul_assoc, hx, one_mul]
      have hxy : x * y = y * x := by
        have hk := hcomm (x * y) hy
        have : y * x = x * y := by
          calc y * x = (x * (x * y)) * x := by rw [← hyk]
            _ = x * ((x * y) * x) := by rw [mul_assoc]
            _ = x * (x * (x * y)) := by rw [← hk]
            _ = x * y := by rw [← hyk]
        exact this.symm
      have hc : Commute x y := hxy
      have h' : x * y⁻¹ = y⁻¹ * x := hc.inv_right
      have : x * y⁻¹ = (x * y)⁻¹ := by
        rw [mul_inv_rev, hxinv, h']
      rw [this]
      exact K'.inv_mem hy

theorem mem_extSub {G : Type*} [Group G] {K' : Subgroup G} {x : G} {hx : x * x = 1}
    {hcomm : ∀ k ∈ K', x * k = k * x} {y : G} :
    y ∈ extSub K' x hx hcomm ↔ y ∈ K' ∨ x * y ∈ K' := Iff.rfl

theorem exists_mem_of_isEA_le {G : Type*} [Group G] [DecidableEq G] [Finite G] (T : Subgroup G)
    (D : List (Finset G))
    (h1 : ({1} : Finset G) ∈ D)
    (hext : ∀ A ∈ D, ∀ s : G, s ∈ T → s * s = 1 → s ∉ A → (∀ a ∈ A, a * s = s * a) →
      (A ∪ A.image (· * s)) ∈ D)
    (K : Subgroup G) (hKT : K ≤ T) (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hsq : ∀ x ∈ K, x * x = 1) :
    ∃ A ∈ D, ∀ x, x ∈ A ↔ x ∈ K := by
  classical
  induction' hn : Nat.card K using Nat.strong_induction_on with k ih generalizing K
  by_cases hK : K = ⊥
  · subst hK
    refine ⟨{1}, h1, fun x => ?_⟩
    simp [Subgroup.mem_bot]
  · set S : Set (Subgroup G) := {L | L ≤ K ∧ L ≠ K} with hS
    have hSne : S.Nonempty := ⟨⊥, bot_le, fun h => hK h.symm⟩
    obtain ⟨K', hK'S, hK'max⟩ :=
      Set.exists_max_image S (fun L => Nat.card L) (Set.toFinite S) hSne
    obtain ⟨hK'le, hK'ne⟩ := hK'S
    obtain ⟨x, hxK, hxK'⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hK'le hK'ne)
    have hxx : x * x = 1 := hsq x hxK
    have hxc : ∀ k ∈ K', x * k = k * x := fun k hk => hcomm x hxK k (hK'le hk)
    let L := extSub K' x hxx hxc
    have hLK : L ≤ K := by
      intro y hy
      rcases hy with hy | hy
      · exact hK'le hy
      · have : y = x * (x * y) := by rw [← mul_assoc, hxx, one_mul]
        rw [this]
        exact K.mul_mem hxK (hK'le hy)
    have hK'L : K' ≤ L := fun y hy => Or.inl hy
    have hxL : x ∈ L := Or.inr (by rw [hxx]; exact K'.one_mem)
    have hLeq : L = K := by
      by_contra hne
      have hcard := hK'max L ⟨hLK, hne⟩
      have : K' = L := Subgroup.eq_of_le_of_card_ge hK'L hcard
      exact hxK' (this ▸ hxL)
    have hmemK : ∀ y, y ∈ K ↔ y ∈ K' ∨ x * y ∈ K' := by
      intro y
      rw [← hLeq]
      exact Iff.rfl
    have hlt : Nat.card K' < k := by
      rw [← hn]
      by_contra hge
      push Not at hge
      exact hK'ne (Subgroup.eq_of_le_of_card_ge hK'le hge)
    obtain ⟨A', hA'D, hA'⟩ := ih _ hlt K' (hK'le.trans hKT)
      (fun a ha b hb => hcomm a (hK'le ha) b (hK'le hb))
      (fun a ha => hsq a (hK'le ha)) rfl
    have hxA' : x ∉ A' := fun h => hxK' ((hA' x).1 h)
    have hcommA' : ∀ a ∈ A', a * x = x * a := fun a ha =>
      (hxc a ((hA' a).1 ha)).symm
    refine ⟨_, hext A' hA'D x (hKT hxK) hxx hxA' hcommA', fun y => ?_⟩
    rw [hmemK y, Finset.mem_union, Finset.mem_image, hA' y]
    constructor
    · rintro (hy | ⟨a, ha, rfl⟩)
      · exact Or.inl hy
      · right
        have hak := (hA' a).1 ha
        have : x * (a * x) = a := by
          rw [← mul_assoc, hxc a hak, mul_assoc, hxx, mul_one]
        rw [this]
        exact hak
    · rintro (hy | hy)
      · exact Or.inl hy
      · right
        refine ⟨x * y, (hA' _).2 hy, ?_⟩
        have hyK : y ∈ K := (hmemK y).2 (Or.inr hy)
        calc x * y * x = x * (y * x) := mul_assoc _ _ _
          _ = x * (x * y) := by rw [hcomm y hyK x hxK]
          _ = y := by rw [← mul_assoc, hxx, one_mul]

end CFSG.Quasithin.B3
