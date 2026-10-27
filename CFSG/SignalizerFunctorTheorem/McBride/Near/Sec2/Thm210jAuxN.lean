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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped IsMulCommutative commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_fixed_ne_one {W X T R : Subgroup Γ} [IsMulCommutative W] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hTW : T ≤ Subgroup.normalizer (W : Set Γ)) (hTX : ∀ t ∈ T, ∀ w ∈ W, ⁅t, w⁆ ∈ X)
    (hRW : R ≤ Subgroup.centralizer (W : Set Γ))
    (hRℓ : ∀ t ∈ T, (∃ k : ℕ, t ^ (ℓ ^ k) = 1) → t ∈ R) {v : Γ} (hvW : v ∈ W) (hvX : v ∉ X)
    (hv1 : v ^ ℓ = 1) : ∃ u ∈ W, u ≠ 1 ∧ ∀ t ∈ T, t * u * t⁻¹ = u := by
  classical
  have := Fact.mk hℓ
  let ψ : ↥T →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hTW)
  have hψ : ∀ (t : ↥T) (w : ↥W), ((ψ t w : ↥W) : Γ) = t * w * (t : Γ)⁻¹ := fun t w => by
    simp [ψ]
  let R' : Subgroup ↥T := R.subgroupOf T
  have hidx : ¬ ℓ ∣ R'.index := by
    obtain ⟨P⟩ : Nonempty (Sylow ℓ ↥T) := inferInstance
    have hPR : (P : Subgroup ↥T) ≤ R' := by
      intro x hx
      have h1 : ∃ k : ℕ, ((x : ↥T) : Γ) ^ (ℓ ^ k) = 1 := by
        obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg (fun y : ↥P => (((y : ↥T)) : Γ)) hk⟩
      exact hRℓ _ x.2 h1
    exact fun hd => P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hPR))
  let v₀ : ↥W := ⟨v, hvW⟩
  have hRfix : ∀ r ∈ R', ψ r v₀ = v₀ := by
    intro r hr
    apply Subtype.ext
    rw [hψ]
    have hrR : (r : Γ) ∈ R := hr
    have := Subgroup.mem_centralizer_iff.mp (hRW hrR) v hvW
    show (r : Γ) * v * (r : Γ)⁻¹ = v
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  let φq : ↥T ⧸ R' → ↥W := fun q => Quotient.liftOn' q (fun g => ψ g v₀) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ R' := QuotientGroup.leftRel_apply.mp hab
    have : b = a * (a⁻¹ * b) := by group
    show ψ a v₀ = ψ b v₀
    rw [this, map_mul, MulAut.mul_apply, hRfix _ hab'])
  have hφq : ∀ g : ↥T, φq (g : ↥T ⧸ R') = ψ g v₀ := fun g => rfl
  have : Fintype (↥T ⧸ R') := Fintype.ofFinite _
  let N : ↥W := ∏ q : ↥T ⧸ R', φq q
  have hNfix : ∀ t : ↥T, ψ t N = N := by
    intro t
    have h1 : ψ t N = ∏ q : ↥T ⧸ R', ψ t (φq q) := map_prod (ψ t) _ _
    rw [h1]
    refine Fintype.prod_equiv (MulAction.toPerm t) _ _ fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ψ t (φq g) = φq ((t • g : ↥T) : ↥T ⧸ R')
      rw [hφq, hφq, smul_eq_mul, map_mul, MulAut.mul_apply]
  let X'' : Subgroup ↥W := X.subgroupOf W
  have : X''.Normal := Subgroup.normal_of_isMulCommutative X''
  let π : ↥W →* ↥W ⧸ X'' := QuotientGroup.mk' X''
  have hπφ : ∀ g : ↥T, π (ψ g v₀) = π v₀ := by
    intro g
    refine ((QuotientGroup.eq (s := X'')).mpr ?_).symm
    rw [Subgroup.mem_subgroupOf]
    have h1 := hTX g g.2 v hvW
    have h2 : v₀⁻¹ * ψ g v₀ = ψ g v₀ * v₀⁻¹ := mul_comm _ _
    rw [h2]
    have h3 : (((ψ g v₀ * v₀⁻¹ : ↥W)) : Γ) = ⁅(g : Γ), v⁆ := by
      rw [commutatorElement_def]
      simp [hψ, v₀]
    rw [h3]
    exact h1
  have hπN : π N = (π v₀) ^ Fintype.card (↥T ⧸ R') := by
    have h1 : π N = ∏ q : ↥T ⧸ R', π (φq q) := map_prod π _ _
    rw [h1, Finset.prod_congr rfl (g := fun _ => π v₀), Finset.prod_const, Finset.card_univ]
    intro q _
    induction q using QuotientGroup.induction_on with
    | H g => rw [hφq]; exact hπφ g
  have hN1 : N ≠ 1 := by
    intro hN
    have h1 : (π v₀) ^ Fintype.card (↥T ⧸ R') = 1 := by rw [← hπN, hN, map_one]
    have h2 : v₀ ^ Fintype.card (↥T ⧸ R') ∈ X'' := by
      rw [← map_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have h3 : v ^ Fintype.card (↥T ⧸ R') ∈ X := h2
    have hcop : Nat.Coprime (Fintype.card (↥T ⧸ R')) ℓ := by
      rw [Fintype.card_eq_nat_card]
      exact ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hidx).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
    have h4 : v = (v ^ Fintype.card (↥T ⧸ R')) ^ m := by
      have hnm : Fintype.card (↥T ⧸ R') * m =
          ℓ * (Fintype.card (↥T ⧸ R') * m / ℓ) + 1 := by
        have := Nat.div_add_mod (Fintype.card (↥T ⧸ R') * m) ℓ
        rw [hm] at this
        exact this.symm
      rw [← pow_mul, hnm, pow_add, pow_mul, hv1, one_pow, one_mul, pow_one]
    exact hvX (h4 ▸ pow_mem h3 m)
  refine ⟨(N : Γ), N.2, fun h => hN1 (Subtype.ext h), fun t ht => ?_⟩
  have := congrArg Subtype.val (hNfix ⟨t, ht⟩)
  rw [hψ] at this
  exact this

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210
