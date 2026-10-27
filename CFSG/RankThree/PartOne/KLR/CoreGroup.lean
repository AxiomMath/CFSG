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

namespace CFSG.RankThree.PartOne.KLR

@[expose] def NoSolvableRadical {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ P → (∀ u ∈ P, ∀ v ∈ N, u * v * u⁻¹ ∈ N) → Group.IsSolvable N → N = ⊥

theorem noSolvableRadical_bot {G : Type*} [Group G] : NoSolvableRadical (⊥ : Subgroup G) :=
  fun _ hN _ _ => le_bot_iff.1 hN

theorem noSolvableRadical_of_mulEquiv {G X : Type*} [Group G] [Group X] [IsSimpleGroup X]
    (hX : ¬ Group.IsSolvable X) {P : Subgroup G} (e : P ≃* X) : NoSolvableRadical P := by
  intro N hNP hnorm hsol
  set N' : Subgroup P := N.subgroupOf P with hN'
  have hN'norm : N'.Normal := ⟨fun m hm g => by
    show ((g : G) * (m : G) * (g : G)⁻¹) ∈ N
    exact hnorm g g.2 m hm⟩
  have hN'sol : Group.IsSolvable N' := by
    have e' : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNP
    exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have hmapn : (N'.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hN'norm e.toMonoidHom e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map e.toMonoidHom) with h | h
  · have h1 : N' = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective N' e.injective).1 h
    refine le_bot_iff.1 fun x hx => ?_
    have : (⟨x, hNP hx⟩ : P) ∈ N' := hx
    rw [h1, Subgroup.mem_bot] at this
    have h2 : x = 1 := congrArg Subtype.val this
    rw [h2]
    exact Subgroup.one_mem _
  · exfalso
    apply hX
    have hsurj : Function.Surjective (e.toMonoidHom.comp N'.subtype) := by
      intro y
      have hy : y ∈ N'.map e.toMonoidHom := by rw [h]; exact Subgroup.mem_top y
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨⟨z, hz⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj

theorem odd_card_of_solvable_normal_of_involutions {D G : Type*} [Group D] [Finite D] [Group G]
    (ψ : D →* G) (hψ : Function.Injective ψ) (P : Subgroup G) (hPψ : P ≤ ψ.range)
    (hP : NoSolvableRadical P) (hinv : ∀ d : D, d ^ 2 = 1 → ψ d ∈ P)
    (V : Subgroup D) [V.Normal] [Group.IsSolvable V] : Odd (Nat.card V) := by
  by_contra hodd
  have heven : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 heven
  have hv2 : ((v : D)) ^ 2 = 1 := by
    have : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
    exact congrArg Subtype.val this
  have hv1 : (v : D) ≠ 1 := fun h => by
    have : v = 1 := Subtype.ext h
    rw [this, orderOf_one] at hv
    exact absurd hv (by norm_num)
  have hψv : ψ v ∈ P := hinv v hv2
  set N : Subgroup G := V.map ψ ⊓ P with hN
  have hNsol : Group.IsSolvable (V.map ψ) := by
    have e : V ≃* V.map ψ := Subgroup.equivMapOfInjective V ψ hψ
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left : N ≤ V.map ψ))
      (Subgroup.inclusion_injective _)
  have hnorm : ∀ u ∈ P, ∀ w ∈ N, u * w * u⁻¹ ∈ N := by
    intro u hu w hw
    obtain ⟨d, rfl⟩ := hPψ hu
    obtain ⟨v', hv', rfl⟩ := hw.1
    refine ⟨?_, ?_⟩
    · refine ⟨d * v' * d⁻¹, (inferInstance : V.Normal).conj_mem v' hv' d, ?_⟩
      simp
    · exact P.mul_mem (P.mul_mem hu hw.2) (P.inv_mem hu)
  have hN1 := hP N inf_le_right hnorm hNs
  have : ψ v ∈ N := ⟨⟨v, v.2, rfl⟩, hψv⟩
  rw [hN1, Subgroup.mem_bot, ← map_one ψ] at this
  exact hv1 (hψ this)

theorem exists_conj_mem_of_card_dvd {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (T : Subgroup Γ) (hT : p ^ (Nat.card Γ).factorization p ∣ Nat.card T) {x : Γ}
    (hx : orderOf x = p) : ∃ c : Γ, c * x * c⁻¹ ∈ T := by
  classical
  have hTΓ : Nat.card T ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card T
  have hfac : (Nat.card T).factorization p = (Nat.card Γ).factorization p := by
    have h1 : (Nat.card T).factorization p ≤ (Nat.card Γ).factorization p :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2 hTΓ) p
    have h2 : (Nat.card Γ).factorization p ≤ (Nat.card T).factorization p := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos.ne')).1 hT
      exact this
    exact le_antisymm h1 h2
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  set P' : Subgroup Γ := (P : Subgroup T).map T.subtype with hP'
  have hP'card : Nat.card P' = p ^ (Nat.card Γ).factorization p := by
    have h1 : Nat.card P' = Nat.card (P : Subgroup T) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).symm.toEquiv
    rw [h1, P.card_eq_multiplicity, hfac]
  let Q₀ : Sylow p Γ := Sylow.ofCard P' hP'card
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  have hxQ : x ∈ (Q : Subgroup Γ) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨g⁻¹, ?_⟩
  have hQ₀ : ((Q₀ : Subgroup Γ)) = P' := rfl
  rw [hQ₀] at hxQ
  obtain ⟨t, -, ht⟩ := hxQ
  have h2 : g⁻¹ * x * g = (t : Γ) := by
    have : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      simp [MulAut.smul_def]
    rw [← this, ← ht]
    rfl
  rw [inv_inv, h2]
  exact t.2

end CFSG.RankThree.PartOne.KLR
