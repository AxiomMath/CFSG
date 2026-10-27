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
public import Mathlib.GroupTheory.Goursat
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

namespace CFSG

namespace FiveTransitive.SimpleGoursat

open Subgroup

private theorem simple_subgroup_le_goursatFst
    (A B : Type) [Group A] [Group B] [Finite A] [Finite B]
    (I : Subgroup (A × B))
    (hfst :
      Function.Surjective
        (Prod.fst ∘ I.subtype))
    (hsnd :
      Function.Surjective
        (Prod.snd ∘ I.subtype))
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hcard : Nat.card B < Nat.card Q) :
    Q ≤ I.goursatFst := by
  let M : Subgroup A := I.goursatFst
  let N : Subgroup B := I.goursatSnd
  letI : M.Normal := by
    dsimp only [M]
    exact Subgroup.normal_goursatFst hfst
  letI : N.Normal := by
    dsimp only [N]
    exact Subgroup.normal_goursatSnd hsnd
  let K : Subgroup Q :=
    M.comap Q.subtype
  letI : K.Normal := by
    dsimp only [K]
    exact Subgroup.Normal.comap inferInstance Q.subtype
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with
      hKbot | hKtop
  · let qmap : Q →* A ⧸ M :=
      (QuotientGroup.mk' M).comp Q.subtype
    have hqmapKer : qmap.ker = ⊥ := by
      ext q
      rw [MonoidHom.mem_ker]
      change
        ((QuotientGroup.mk' M) (q : A) = 1) ↔
          q ∈ (⊥ : Subgroup Q)
      rw [QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      change q ∈ K ↔ q ∈ (⊥ : Subgroup Q)
      rw [hKbot]
    have hqmapInjective : Function.Injective qmap := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hqmapKer
    have hQleQuot :
        Nat.card Q ≤ Nat.card (A ⧸ M) :=
      Nat.card_le_card_of_injective qmap hqmapInjective
    obtain ⟨e, _⟩ :=
      Subgroup.goursat_surjective hfst hsnd
    have hquotEq :
        Nat.card (A ⧸ M) =
          Nat.card (B ⧸ N) :=
      Nat.card_congr e.toEquiv
    have hquotLe :
        Nat.card (B ⧸ N) ≤ Nat.card B :=
      Nat.card_le_card_of_surjective
        (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)
    omega
  · intro q hq
    have hqK : (⟨q, hq⟩ : Q) ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top _
    exact hqK

private theorem simple_subgroup_le_goursatFst_of_not_dvd
    (A B : Type) [Group A] [Group B] [Finite A] [Finite B]
    (I : Subgroup (A × B))
    (hfst :
      Function.Surjective
        (Prod.fst ∘ I.subtype))
    (hsnd :
      Function.Surjective
        (Prod.snd ∘ I.subtype))
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hcard : ¬Nat.card Q ∣ Nat.card B) :
    Q ≤ I.goursatFst := by
  let M : Subgroup A := I.goursatFst
  let N : Subgroup B := I.goursatSnd
  letI : M.Normal := by
    dsimp only [M]
    exact Subgroup.normal_goursatFst hfst
  letI : N.Normal := by
    dsimp only [N]
    exact Subgroup.normal_goursatSnd hsnd
  let K : Subgroup Q :=
    M.comap Q.subtype
  letI : K.Normal := by
    dsimp only [K]
    exact Subgroup.Normal.comap inferInstance Q.subtype
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with
      hKbot | hKtop
  · let qmap : Q →* A ⧸ M :=
      (QuotientGroup.mk' M).comp Q.subtype
    have hqmapKer : qmap.ker = ⊥ := by
      ext q
      rw [MonoidHom.mem_ker]
      change
        ((QuotientGroup.mk' M) (q : A) = 1) ↔
          q ∈ (⊥ : Subgroup Q)
      rw [QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      change q ∈ K ↔ q ∈ (⊥ : Subgroup Q)
      rw [hKbot]
    have hqmapInjective : Function.Injective qmap := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hqmapKer
    have hQdvdQuot :
        Nat.card Q ∣ Nat.card (A ⧸ M) :=
      Subgroup.card_dvd_of_injective
        qmap hqmapInjective
    obtain ⟨e, _⟩ :=
      Subgroup.goursat_surjective hfst hsnd
    have hquotEq :
        Nat.card (A ⧸ M) =
          Nat.card (B ⧸ N) :=
      Nat.card_congr e.toEquiv
    have hQdvdQuotB :
        Nat.card Q ∣ Nat.card (B ⧸ N) := by
      rwa [hquotEq] at hQdvdQuot
    have hQdvdB : Nat.card Q ∣ Nat.card B :=
      hQdvdQuotB.trans N.card_quotient_dvd_card
    exact (hcard hQdvdB).elim
  · intro q hq
    have hqK : (⟨q, hq⟩ : Q) ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top _
    exact hqK

theorem exists_lift_with_aux_eq_one
    (L A B : Type) [Group L] [Group A] [Group B]
    [Finite L] [Finite A] [Finite B]
    (f : L →* A) (g : L →* B)
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hQ : Q ≤ f.range)
    (hcard : Nat.card g.range < Nat.card Q)
    (q : A) (hq : q ∈ Q) :
    ∃ l : L, f l = q ∧ g l = 1 := by
  let J : Subgroup A := f.range
  let R : Subgroup B := g.range
  let fJ : L →* J := f.rangeRestrict
  let gR : L →* R := g.rangeRestrict
  let pair : L →* J × R :=
    fJ.prod gR
  let I : Subgroup (J × R) :=
    pair.range
  have hfst :
      Function.Surjective
        (Prod.fst ∘ I.subtype) := by
    intro j
    obtain ⟨l, hl⟩ := j.prop
    let i : I :=
      ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  have hsnd :
      Function.Surjective
        (Prod.snd ∘ I.subtype) := by
    intro r
    obtain ⟨l, hl⟩ := r.prop
    let i : I :=
      ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  let QJ : Subgroup J :=
    Q.subgroupOf J
  letI : IsSimpleGroup QJ :=
    (Subgroup.subgroupOfEquivOfLe hQ).isSimpleGroup
  have hQJcard :
      Nat.card QJ = Nat.card Q :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have hQJle :
      QJ ≤ I.goursatFst := by
    apply simple_subgroup_le_goursatFst
      J R I hfst hsnd QJ
    simpa only [R, hQJcard] using hcard
  let qJ : J := ⟨q, hQ hq⟩
  have hqJ : qJ ∈ QJ := by
    change q ∈ Q
    exact hq
  have hqFirst : qJ ∈ I.goursatFst :=
    hQJle hqJ
  have hpair :
      (qJ, (1 : R)) ∈ I :=
    I.goursatFst_prod_goursatSnd_le
      ⟨hqFirst, Subgroup.one_mem _⟩
  obtain ⟨l, hl⟩ := hpair
  refine ⟨l, ?_, ?_⟩
  · have hfirst :=
      congrArg (fun z : J × R => (z.1 : A)) hl
    exact hfirst
  · have hsecond :=
      congrArg (fun z : J × R => (z.2 : B)) hl
    exact hsecond

theorem exists_lift_with_aux_eq_one_of_not_dvd
    (L A B : Type) [Group L] [Group A] [Group B]
    [Finite L] [Finite A] [Finite B]
    (f : L →* A) (g : L →* B)
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hQ : Q ≤ f.range)
    (hcard : ¬Nat.card Q ∣ Nat.card g.range)
    (q : A) (hq : q ∈ Q) :
    ∃ l : L, f l = q ∧ g l = 1 := by
  let J : Subgroup A := f.range
  let R : Subgroup B := g.range
  let fJ : L →* J := f.rangeRestrict
  let gR : L →* R := g.rangeRestrict
  let pair : L →* J × R :=
    fJ.prod gR
  let I : Subgroup (J × R) :=
    pair.range
  have hfst :
      Function.Surjective
        (Prod.fst ∘ I.subtype) := by
    intro j
    obtain ⟨l, hl⟩ := j.prop
    let i : I :=
      ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  have hsnd :
      Function.Surjective
        (Prod.snd ∘ I.subtype) := by
    intro r
    obtain ⟨l, hl⟩ := r.prop
    let i : I :=
      ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  let QJ : Subgroup J :=
    Q.subgroupOf J
  letI : IsSimpleGroup QJ :=
    (Subgroup.subgroupOfEquivOfLe hQ).isSimpleGroup
  have hQJcard :
      Nat.card QJ = Nat.card Q :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have hQJle :
      QJ ≤ I.goursatFst := by
    apply simple_subgroup_le_goursatFst_of_not_dvd
      J R I hfst hsnd QJ
    simpa only [R, hQJcard] using hcard
  let qJ : J := ⟨q, hQ hq⟩
  have hqJ : qJ ∈ QJ := by
    change q ∈ Q
    exact hq
  have hqFirst : qJ ∈ I.goursatFst :=
    hQJle hqJ
  have hpair :
      (qJ, (1 : R)) ∈ I :=
    I.goursatFst_prod_goursatSnd_le
      ⟨hqFirst, Subgroup.one_mem _⟩
  obtain ⟨l, hl⟩ := hpair
  refine ⟨l, ?_, ?_⟩
  · have hfirst :=
      congrArg (fun z : J × R => (z.1 : A)) hl
    exact hfirst
  · have hsecond :=
      congrArg (fun z : J × R => (z.2 : B)) hl
    exact hsecond

end FiveTransitive.SimpleGoursat

end CFSG
