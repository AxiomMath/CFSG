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

namespace CFSG.Quasithin.S1565

open scoped BigOperators

variable {X : Type} [Group X] {W : Type} [CommGroup W]

@[expose] def InvSub (φ : X →* MulAut W) (A : Subgroup W) : Prop :=
  ∀ x : X, ∀ a ∈ A, φ x a ∈ A

@[expose] def FixMod (φ : X →* MulAut W) (S : Subgroup X) (A : Subgroup W) (w : W) : Prop :=
  ∀ s ∈ S, φ s w * w⁻¹ ∈ A

@[expose] def FixProp (φ : X →* MulAut W) (B : Subgroup X) (A A' : Subgroup W) : Prop :=
  ∀ w ∈ A', FixMod φ B A w → FixMod φ ⊤ A w

@[expose] def ChiefPair (φ : X →* MulAut W) (A A' : Subgroup W) : Prop :=
  A < A' ∧ InvSub φ A ∧ InvSub φ A' ∧
    ∀ C : Subgroup W, InvSub φ C → A ≤ C → C ≤ A' → C = A ∨ C = A'

@[expose] def TrivOn (φ : X →* MulAut W) (A A' : Subgroup W) : Prop :=
  ∀ x : X, ∀ a ∈ A', φ x a * a⁻¹ ∈ A

@[expose] def NoFixedOn (φ : X →* MulAut W) (B : Subgroup X) (A A' : Subgroup W) : Prop :=
  ∀ a ∈ A', (∀ b ∈ B, φ b a * a⁻¹ ∈ A) → a ∈ A

@[expose] def ChiefFreeBelow (φ : X →* MulAut W) (B : Subgroup X) (J : Subgroup W) : Prop :=
  ∀ A A' : Subgroup W, A' ≤ J → ChiefPair φ A A' → TrivOn φ A A' ∨ NoFixedOn φ B A A'

theorem norm_step [Finite X] (φ : X →* MulAut W) (hW2 : ∀ w : W, w ^ 2 = 1) (B : Subgroup X)
    (hB : Odd B.index) {A A'' : Subgroup W} (hA : InvSub φ A) {w : W}
    (hw'' : FixMod φ ⊤ A'' w) (hwB : FixMod φ B A w) :
    ∃ u ∈ A'', FixMod φ ⊤ A (w * u) ∧ FixMod φ B A u := by
  classical
  have : Fintype (X ⧸ B) := Fintype.ofFinite _
  set c : X → W := fun x => φ x w * w⁻¹ with hc
  have hcA'' : ∀ x, c x ∈ A'' := fun x => hw'' x (Subgroup.mem_top x)
  have hcmul : ∀ y x, c (y * x) = φ y (c x) * c y := by
    intro y x
    simp only [hc, map_mul, MulAut.mul_apply, map_inv]
    group
  have hcB : ∀ x, ∀ b ∈ B, c (x * b) * (c x)⁻¹ ∈ A := by
    intro x b hb
    have h1 : c (x * b) = φ x (c b) * c x := hcmul x b
    have h2 : c b ∈ A := hwB b hb
    have : c (x * b) * (c x)⁻¹ = φ x (c b) := by rw [h1]; group
    rw [this]
    exact hA x _ h2
  set u : W := ∏ q : X ⧸ B, c q.out with hu
  have huA'' : u ∈ A'' := Subgroup.prod_mem _ fun q _ => hcA'' _
  have hcy : ∀ y : X, φ y u * c y * u⁻¹ ∈ A := by
    intro y
    have hperm : ∏ q : X ⧸ B, c (y • q).out = u := by
      have := Equiv.prod_comp (MulAction.toPerm y : X ⧸ B ≃ X ⧸ B) (fun q => c q.out)
      simpa [hu] using this
    have hrat : ∀ q : X ⧸ B, c (y * q.out) * (c (y • q).out)⁻¹ ∈ A := by
      intro q
      have hmem : (y * q.out)⁻¹ * (y • q).out ∈ B := by
        rw [← QuotientGroup.eq]
        have h1 : (QuotientGroup.mk (y • q).out : X ⧸ B) = y • q := Quotient.out_eq' _
        have h2 : (QuotientGroup.mk (y * q.out) : X ⧸ B) = y • q := by
          conv_rhs => rw [← QuotientGroup.out_eq' q]
          rfl
        rw [h1, h2]
      have := hcB (y * q.out) _ hmem
      have e : y * q.out * ((y * q.out)⁻¹ * (y • q).out) = (y • q).out := by group
      rw [e] at this
      have h3 : c (y * q.out) * (c (y • q).out)⁻¹ = ((c (y • q).out) * (c (y * q.out))⁻¹)⁻¹ := by
        group
      rw [h3]
      exact A.inv_mem this
    have hprod : (∏ q : X ⧸ B, c (y * q.out)) * (∏ q : X ⧸ B, c (y • q).out)⁻¹ ∈ A := by
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      exact Subgroup.prod_mem _ fun q _ => hrat q
    have hexp : ∏ q : X ⧸ B, c (y * q.out) = φ y u * c y := by
      have : ∀ q : X ⧸ B, c (y * q.out) = φ y (c q.out) * c y := fun q => hcmul y q.out
      simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod]
      have hm : Fintype.card (X ⧸ B) = B.index := by
        rw [Subgroup.index, Nat.card_eq_fintype_card]
      rw [hm]
      obtain ⟨k, hk⟩ := hB
      rw [hk, pow_succ, pow_mul, hW2, one_pow, one_mul]
    rw [hexp, hperm] at hprod
    exact hprod
  refine ⟨u, huA'', ?_, ?_⟩
  · intro y _
    have e : φ y (w * u) * (w * u)⁻¹ = φ y u * c y * u⁻¹ := by
      simp only [hc, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact hcy y
  · intro b hb
    have hfix : φ b (w * u) * (w * u)⁻¹ ∈ A := by
      have e : φ b (w * u) * (w * u)⁻¹ = φ b u * c b * u⁻¹ := by
        simp only [hc, map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [e]
      exact hcy b
    have e : φ b u * u⁻¹ = (φ b (w * u) * (w * u)⁻¹) * (φ b w * w⁻¹)⁻¹ := by
      simp only [map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact A.mul_mem hfix (A.inv_mem (hwB b hb))

theorem fixProp_compose [Finite X] (φ : X →* MulAut W) (hW2 : ∀ w : W, w ^ 2 = 1)
    (B : Subgroup X) (hB : Odd B.index) {A A'' B' : Subgroup W} (hA : InvSub φ A) (hAA : A ≤ A'')
    (h1 : FixProp φ B A A'') (h2 : FixProp φ B A'' B') : FixProp φ B A B' := by
  intro w hw hwB
  have hwB'' : FixMod φ B A'' w := fun b hb => hAA (hwB b hb)
  have hw'' : FixMod φ ⊤ A'' w := h2 w hw hwB''
  obtain ⟨u, hu, hfix, hfixB⟩ := norm_step φ hW2 B hB hA hw'' hwB
  have hfixu : FixMod φ ⊤ A u := h1 u hu hfixB
  intro s hs
  have e : φ s w * w⁻¹ = (φ s (w * u) * (w * u)⁻¹) * (φ s u * u⁻¹)⁻¹ := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  exact A.mul_mem (hfix s hs) (A.inv_mem (hfixu s hs))

theorem fixProp_of_chiefFactor {φ : X →* MulAut W} {B : Subgroup X} {A A' : Subgroup W}
    (hA : InvSub φ A) (h : TrivOn φ A A' ∨ NoFixedOn φ B A A') : FixProp φ B A A' := by
  intro w hw hwB
  rcases h with h | h
  · exact fun x _ => h x w hw
  · have hwA : w ∈ A := h w hw hwB
    exact fun x _ => A.mul_mem (hA x w hwA) (A.inv_mem hwA)

theorem fixProp_of_interval [Finite X] [Finite W] (φ : X →* MulAut W)
    (hW2 : ∀ w : W, w ^ 2 = 1) (B : Subgroup X) (hB : Odd B.index) {B' : Subgroup W}
    (hB' : InvSub φ B') :
    ∀ A : Subgroup W, InvSub φ A → A ≤ B' →
      (∀ A₁ A₂ : Subgroup W, A ≤ A₁ → A₂ ≤ B' → ChiefPair φ A₁ A₂ →
        TrivOn φ A₁ A₂ ∨ NoFixedOn φ B A₁ A₂) → FixProp φ B A B' := by
  intro A
  induction A using WellFoundedGT.induction with
  | _ A ih =>
    intro hA hAB' hcf
    by_cases hAeq : A = B'
    · subst hAeq
      intro w hw _ x _
      exact A.mul_mem (hA x w hw) (A.inv_mem hw)
    · have hlt : A < B' := lt_of_le_of_ne hAB' hAeq
      obtain ⟨C₀, ⟨hC₀inv, hAC₀, hC₀B'⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
        {C : Subgroup W | InvSub φ C ∧ A < C ∧ C ≤ B'} ⟨B', hB', hlt, le_rfl⟩
      have hchief : ChiefPair φ A C₀ := by
        refine ⟨hAC₀, hA, hC₀inv, fun C hCinv hAC hCC₀ => ?_⟩
        by_cases hCA : C = A
        · exact Or.inl hCA
        · right
          have hAlt : A < C := lt_of_le_of_ne hAC (Ne.symm hCA)
          by_contra hne
          exact hmin C ⟨hCinv, hAlt, hCC₀.trans hC₀B'⟩ (lt_of_le_of_ne hCC₀ hne)
      have h1 : FixProp φ B A C₀ := fixProp_of_chiefFactor hA (hcf A C₀ le_rfl hC₀B' hchief)
      have h2 : FixProp φ B C₀ B' :=
        ih C₀ hAC₀ hC₀inv hC₀B' fun A₁ A₂ hA₁ hA₂ hp => hcf A₁ A₂ (hAC₀.le.trans hA₁) hA₂ hp
      exact fixProp_compose φ hW2 B hB hA hAC₀.le h1 h2

end CFSG.Quasithin.S1565
