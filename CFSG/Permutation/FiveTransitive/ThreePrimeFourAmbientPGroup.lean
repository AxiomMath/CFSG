module

public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

namespace CFSG

namespace FiveTransitive.ThreePrimeFourAmbientPGroup

open MulAction Subgroup FixedNormalizerAction

private theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ} [Fact p.Prime]
    (hp : 17 ≤ p) (P : Subgroup (Equiv.Perm X))
    (hn : Fintype.card X = 3 * p + 4)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) = 4 := by
  classical
  have hpd : p ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left (by
    intro he; exact hne (Subgroup.card_eq_one.mp he))
  have hlt : Nat.card (fixedPoints Q X) < 5 := by
    by_contra hh
    have hlarge : 5 ≤ (fixedPoints Q X).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
    let i : Q →* fixingSubgroup P s := Q.subtype.codRestrict (fixingSubgroup P s)
      (fun q => (mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx q))
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : fixingSubgroup P s => z.val) hab)
    exact hfree s hs (hpd.trans (Subgroup.card_dvd_of_injective i hi))
  have hm := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hm
  rw [Nat.card_eq_fintype_card (α := X),hn] at hm
  have he : (3 * p + 4) % p = 4 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 4 < p)]
  rw [he,Nat.mod_eq_of_lt (by omega : Nat.card (fixedPoints Q X) < p)] at hm
  exact hm.symm

private theorem card_eq_prime
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ} [Fact p.Prime]
    (hp : 17 ≤ p) (P : Subgroup (Equiv.Perm X))
    (hn : Fintype.card X = 3 * p + 4)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥) : Nat.card Q = p := by
  have hf := fixed_card hp P hn hfree Q hQ hne
  have hfreeQ : ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    let R : Subgroup P := (zpowers q).map Q.subtype
    have hR : IsPGroup p R := (hQ.to_subgroup (zpowers q)).map Q.subtype
    have hqR : q.val ∈ R := ⟨q,mem_zpowers q,rfl⟩
    have hRne : R ≠ ⊥ := by
      intro he
      have hh := hqR
      rw [he,mem_bot] at hh
      exact hq (Subtype.ext hh)
    have hrfix := fixed_card hp P hn hfree R hR hRne
    have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
      intro y hy r
      obtain ⟨a,ha,hea⟩ := r.property
      change r.val • y = y
      rw [← hea]
      rcases hy with rfl | hy
      · exact (zpowers_le.mpr (show q ∈ stabilizer Q y from hqx)) ha
      · exact hy a
    have hlo := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hx,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hf,hrfix] at hlo
    omega
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (fun q x hx => (hx q).symm ▸ hx) hfreeQ
  rw [← Nat.card_coe_set_eq,hf,Nat.card_eq_fintype_card (α := X),hn,Nat.add_sub_cancel] at hd
  have hle : Nat.card Q ≤ 3 * p := Nat.le_of_dvd (by omega) hd
  obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp hQ
  have hk1 : k ≤ 1 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 2 ≤ k)
    rw [← hk] at hpow
    have hmul := Nat.mul_le_mul_right p hp
    nlinarith
  have hk0 : k ≠ 0 := by
    intro he
    rw [he,pow_zero] at hk
    exact hne (Subgroup.card_eq_one.mp hk)
  simpa only [show k = 1 by omega,pow_one] using hk

private theorem cycle_type
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (g : Equiv.Perm X) (hg : orderOf g = p)
    (hn : Fintype.card X = 3 * p + 4)
    (hf : Nat.card (Function.fixedPoints g) = 4) : g.cycleType = {p,p,p} := by
  have hs : g.support.card = 3 * p := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.sum_cycleType,hn] at hf
    have hle := Finset.card_le_univ g.support
    rw [hn] at hle
    omega
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rwa [hg])
  have hsum := g.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hg,hs] at hsum
  have hk3 : k + 1 = 3 := Nat.mul_right_cancel hp.pos hsum
  rw [hk,hg,hk3]
  simp

theorem exists_generator
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p)
    (P : Subgroup (Equiv.Perm X)) (hn : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) :
    ∃ u : P, orderOf u = p ∧ u.val.cycleType = {p,p,p} ∧
      Nat.card (Fixed (X := X) (zpowers u)) = 4 ∧ Image (X := X) (zpowers u) = ⊤ := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive P X 5 (by omega) h5
  rw [hn] at hd
  have hpdesc : p ∣ (3 * p + 4).descFactorial 5 := by
    rw [Nat.descFactorial_eq_prod_range]
    have hfactor := Finset.dvd_prod_of_mem (fun i => 3 * p + 4 - i)
      (show 4 ∈ Finset.range 5 by decide)
    rw [Nat.add_sub_cancel] at hfactor
    exact (dvd_mul_left p 3).trans hfactor
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := P) p (hpdesc.trans hd)
  have hR : IsPGroup p (zpowers u) := IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers,hu,pow_one])
  obtain ⟨S,hRS⟩ := hR.exists_le_sylow
  have hSne : (S : Subgroup P) ≠ ⊥ := by
    intro he
    have hh := hRS (mem_zpowers u)
    rw [he,mem_bot] at hh
    rw [hh,orderOf_one] at hu
    exact hp.ne_one hu.symm
  have hScard := card_eq_prime hp17 P hn hfree (S : Subgroup P) S.isPGroup' hSne
  have hSfix := fixed_card hp17 P hn hfree (S : Subgroup P) S.isPGroup' hSne
  have heq : zpowers u = (S : Subgroup P) := Subgroup.eq_of_le_of_card_ge hRS
    (by rw [Nat.card_zpowers,hu,hScard])
  have hufix : Nat.card (Function.fixedPoints u.val) = 4 := by
    have hset : fixedPoints (zpowers u) X = Function.fixedPoints u.val := by
      ext x
      constructor
      · intro hx; exact hx ⟨u,mem_zpowers u⟩
      · intro hx q; exact (zpowers_le.mpr (show u ∈ stabilizer P x from hx)) q.property
    rw [← hset,heq]
    exact hSfix
  refine ⟨u,hu,cycle_type hp u.val ((Subgroup.orderOf_coe u).trans hu) hn hufix,?_,?_⟩
  · rw [heq,fixed_eq]
    exact hSfix
  · rw [heq]
    exact AmbientSylowSmallFixedImage.sylow_fixed_image p 4 hp (by omega)
      P (by omega) h5 S hSfix

end FiveTransitive.ThreePrimeFourAmbientPGroup

end CFSG
