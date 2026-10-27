module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59


section Identities

variable {E : Type*} [Ring E] (g : E) (h2 : (2 : E) = 0) (hg : g ^ 7 = 1)

include h2 hg

theorem id_aux {a b Q1 Q2 : E} (e : a - b = (g ^ 7 - 1) * Q1 + 2 * Q2) : a = b := by
  rw [hg, sub_self, zero_mul, h2, zero_mul, add_zero] at e
  exact sub_eq_zero.mp e

theorem id_R1 :
    (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) + (1 + g + g^2 + g^4) + (1 + g^3 + g^5 + g^6) = 1 := by
  refine id_aux g h2 hg (Q1 := 0)
    (Q2 := (1 : E) + g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R2_00 :
    (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) * (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) =
      (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) := by
  refine id_aux g h2 hg (Q1 := 6 • (1 : E) + 5 • g + 4 • g^2 + 3 • g^3 + 2 • g^4 + g^5)
    (Q2 := 3 • (1 : E) + 3 • g + 3 • g^2 + 3 • g^3 + 3 • g^4 + 3 • g^5 + 3 • g^6) ?_
  noncomm_ring

theorem id_R2_01 :
    (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) * (1 + g + g^2 + g^4) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + 2 • g + g^2 + g^3)
    (Q2 := 2 • (1 : E) + 2 • g + 2 • g^2 + 2 • g^3 + 2 • g^4 + 2 • g^5 + 2 • g^6) ?_
  noncomm_ring

theorem id_R2_02 :
    (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) * (1 + g^3 + g^5 + g^6) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + 3 • g + 3 • g^2 + 2 • g^3 + 2 • g^4 + g^5)
    (Q2 := 2 • (1 : E) + 2 • g + 2 • g^2 + 2 • g^3 + 2 • g^4 + 2 • g^5 + 2 • g^6) ?_
  noncomm_ring

theorem id_R2_10 :
    (1 + g + g^2 + g^4) * (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + 2 • g + g^2 + g^3)
    (Q2 := 2 • (1 : E) + 2 • g + 2 • g^2 + 2 • g^3 + 2 • g^4 + 2 • g^5 + 2 • g^6) ?_
  noncomm_ring

theorem id_R2_11 :
    (1 + g + g^2 + g^4) * (1 + g + g^2 + g^4) = (1 + g + g^2 + g^4) := by
  refine id_aux g h2 hg (Q1 := g)
    (Q2 := g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R2_12 :
    (1 + g + g^2 + g^4) * (1 + g^3 + g^5 + g^6) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + g + g^2 + g^3)
    (Q2 := 2 • (1 : E) + g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R2_20 :
    (1 + g^3 + g^5 + g^6) * (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + 3 • g + 3 • g^2 + 2 • g^3 + 2 • g^4 + g^5)
    (Q2 := 2 • (1 : E) + 2 • g + 2 • g^2 + 2 • g^3 + 2 • g^4 + 2 • g^5 + 2 • g^6) ?_
  noncomm_ring

theorem id_R2_21 :
    (1 + g^3 + g^5 + g^6) * (1 + g + g^2 + g^4) = 0 := by
  refine id_aux g h2 hg (Q1 := 3 • (1 : E) + g + g^2 + g^3)
    (Q2 := 2 • (1 : E) + g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R2_22 :
    (1 + g^3 + g^5 + g^6) * (1 + g^3 + g^5 + g^6) = (1 + g^3 + g^5 + g^6) := by
  refine id_aux g h2 hg (Q1 := 2 • g + 2 • g^2 + g^3 + 2 • g^4 + g^5)
    (Q2 := g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R3 :
    (g + 1) * (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) = 0 := by
  refine id_aux g h2 hg (Q1 := (1 : E))
    (Q2 := (1 : E) + g + g^2 + g^3 + g^4 + g^5 + g^6) ?_
  noncomm_ring

theorem id_R4a :
    (1 + g^3 + g^6 + g^12) = (1 + g^3 + g^5 + g^6) := by
  refine id_aux g h2 hg (Q1 := g^5)
    (Q2 := 0) ?_
  noncomm_ring

theorem id_R4b :
    (1 + g^15 + g^25 + g^30) = (1 + g + g^2 + g^4) := by
  refine id_aux g h2 hg (Q1 := g + g^2 + g^4 + g^8 + g^9 + g^11 + g^16 + g^18 + g^23)
    (Q2 := 0) ?_
  noncomm_ring


theorem exp_theta0 : (1 + g + g^2 + g^3 + g^4 + g^5 + g^6) =
    1 + (g + g^3 + g^5) * (g + 1) := by
  noncomm_ring

end Identities

section Twist

theorem mul_pow_comm {E : Type*} [Ring E] (g h : E) (m : ℕ) (hh : h * g = g ^ m * h) (k : ℕ) :
    h * g ^ k = g ^ (m * k) * h := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hh, ← mul_assoc, ← pow_add, ← Nat.mul_succ]

theorem four_pow_mod (a : ℕ) : 4 ^ a % 7 = 4 ^ (a % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

variable {W : Type*} [AddCommGroup W] [Finite W]

theorem card_eq_two_pow_of_exp_two (hW : ∀ x : W, x + x = 0) (K : AddSubgroup W) :
    ∃ a : ℕ, Nat.card K = 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Multiplicative K) := fun x => ⟨1, by
    have h : (Multiplicative.toAdd x) + (Multiplicative.toAdd x) = 0 := by
      apply Subtype.ext
      exact hW _
    have h2 : x ^ (2 ^ 1) = 1 := by
      apply Multiplicative.toAdd.injective
      simpa [pow_one, two_nsmul] using h
    exact h2⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, hn⟩

theorem twist_card (hW : ∀ x : W, x + x = 0)
    (g h₁ h₂ : AddMonoid.End W) (hg : g ^ 7 = 1) (hh₁ : h₁ * g = g ^ 3 * h₁)
    (hh₂ : h₂ * g = g ^ 5 * h₂) (hi₁ : Function.Injective h₁) (hi₂ : Function.Injective h₂) :
    ∃ j : ℕ, Nat.card W = Nat.card {x : W // g x = x} * 64 ^ j := by
  classical
  have h2 : (2 : AddMonoid.End W) = 0 := by
    ext w
    rw [show (2 : AddMonoid.End W) = 1 + 1 from one_add_one_eq_two.symm]
    exact hW w
  have hW' : ∀ a b : W, a + b = 0 → a = b := fun a b h => by
    calc a = a + (b + b) := by rw [hW b, add_zero]
      _ = (a + b) + b := by rw [add_assoc]
      _ = b := by rw [h, zero_add]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ : AddMonoid.End W, θ = 1 + g + g^2 + g^3 + g^4 + g^5 + g^6 :=
    ⟨_, rfl⟩
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ : AddMonoid.End W, θ = 1 + g + g^2 + g^4 := ⟨_, rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ : AddMonoid.End W, θ = 1 + g^3 + g^5 + g^6 := ⟨_, rfl⟩
  have R1 : θ₀ + θ₁ + θ₂ = 1 := by rw [hθ₀, hθ₁, hθ₂]; exact id_R1 g h2 hg
  have r00 : θ₀ * θ₀ = θ₀ := by rw [hθ₀]; exact id_R2_00 g h2 hg
  have r01 : θ₀ * θ₁ = 0 := by rw [hθ₀, hθ₁]; exact id_R2_01 g h2 hg
  have r02 : θ₀ * θ₂ = 0 := by rw [hθ₀, hθ₂]; exact id_R2_02 g h2 hg
  have r10 : θ₁ * θ₀ = 0 := by rw [hθ₀, hθ₁]; exact id_R2_10 g h2 hg
  have r11 : θ₁ * θ₁ = θ₁ := by rw [hθ₁]; exact id_R2_11 g h2 hg
  have r12 : θ₁ * θ₂ = 0 := by rw [hθ₁, hθ₂]; exact id_R2_12 g h2 hg
  have r20 : θ₂ * θ₀ = 0 := by rw [hθ₀, hθ₂]; exact id_R2_20 g h2 hg
  have r21 : θ₂ * θ₁ = 0 := by rw [hθ₁, hθ₂]; exact id_R2_21 g h2 hg
  have r22 : θ₂ * θ₂ = θ₂ := by rw [hθ₂]; exact id_R2_22 g h2 hg
  have r3 : (g + 1) * θ₀ = 0 := by rw [hθ₀]; exact id_R3 g h2 hg
  have e1 : h₁ * g = g ^ 3 * h₁ := hh₁
  have e2 : h₁ * g ^ 2 = g ^ 6 * h₁ := by simpa using mul_pow_comm g h₁ 3 hh₁ 2
  have e4 : h₁ * g ^ 4 = g ^ 12 * h₁ := by simpa using mul_pow_comm g h₁ 3 hh₁ 4
  have e3 : h₁ * g ^ 3 = g ^ 9 * h₁ := by simpa using mul_pow_comm g h₁ 3 hh₁ 3
  have f1 : h₂ * g = g ^ 5 * h₂ := hh₂
  have f3 : h₂ * g ^ 3 = g ^ 15 * h₂ := by simpa using mul_pow_comm g h₂ 5 hh₂ 3
  have f5 : h₂ * g ^ 5 = g ^ 25 * h₂ := by simpa using mul_pow_comm g h₂ 5 hh₂ 5
  have f6 : h₂ * g ^ 6 = g ^ 30 * h₂ := by simpa using mul_pow_comm g h₂ 5 hh₂ 6
  have R4a : h₁ * θ₁ = θ₂ * h₁ := by
    calc h₁ * θ₁ = h₁ * (1 + g + g^2 + g^4) := by rw [hθ₁]
      _ = h₁ + g ^ 3 * h₁ + g ^ 6 * h₁ + g ^ 12 * h₁ := by
        rw [mul_add, mul_add, mul_add, mul_one, e1, e2, e4]
      _ = (1 + g ^ 3 + g ^ 6 + g ^ 12) * h₁ := by noncomm_ring
      _ = θ₂ * h₁ := by rw [id_R4a g h2 hg, hθ₂]
  have R4b : h₂ * θ₂ = θ₁ * h₂ := by
    calc h₂ * θ₂ = h₂ * (1 + g^3 + g^5 + g^6) := by rw [hθ₂]
      _ = h₂ + g ^ 15 * h₂ + g ^ 25 * h₂ + g ^ 30 * h₂ := by
        rw [mul_add, mul_add, mul_add, mul_one, f3, f5, f6]
      _ = (1 + g ^ 15 + g ^ 25 + g ^ 30) * h₂ := by noncomm_ring
      _ = θ₁ * h₂ := by rw [id_R4b g h2 hg, hθ₁]
  have hm : ∀ (A B : AddMonoid.End W) (x : W), (A * B) x = A (B x) := fun _ _ _ => rfl
  have ap : ∀ (A B : AddMonoid.End W) (x : W), A * B = 0 → A (B x) = 0 := fun A B x h => by
    have := congrArg (fun T : AddMonoid.End W => T x) h
    simpa [hm] using this
  have ai : ∀ (A B : AddMonoid.End W) (x : W), A * B = B → A (B x) = B x := fun A B x h => by
    have := congrArg (fun T : AddMonoid.End W => T x) h
    simpa [hm] using this
  have hcard : Nat.card W = Nat.card (AddMonoidHom.range θ₀) *
      (Nat.card (AddMonoidHom.range θ₁) * Nat.card (AddMonoidHom.range θ₂)) := by
    let e : W ≃ (AddMonoidHom.range θ₀) × (AddMonoidHom.range θ₁) × (AddMonoidHom.range θ₂) :=
      { toFun := fun w => (⟨θ₀ w, w, rfl⟩, ⟨θ₁ w, w, rfl⟩, ⟨θ₂ w, w, rfl⟩)
        invFun := fun p => (p.1 : W) + (p.2.1 : W) + (p.2.2 : W)
        left_inv := fun w => by
          have := congrArg (fun T : AddMonoid.End W => T w) R1
          exact this
        right_inv := fun p => by
          obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, ⟨_, c, rfl⟩⟩ := p
          refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
          · show θ₀ (θ₀ a + θ₁ b + θ₂ c) = θ₀ a
            rw [map_add, map_add, ai _ _ a r00, ap _ _ b r01, ap _ _ c r02, add_zero, add_zero]
          · show θ₁ (θ₀ a + θ₁ b + θ₂ c) = θ₁ b
            rw [map_add, map_add, ap _ _ a r10, ai _ _ b r11, ap _ _ c r12, zero_add, add_zero]
          · show θ₂ (θ₀ a + θ₁ b + θ₂ c) = θ₂ c
            rw [map_add, map_add, ap _ _ a r20, ap _ _ b r21, ai _ _ c r22, zero_add, zero_add] }
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  have hK₀ : ∀ x : W, x ∈ AddMonoidHom.range θ₀ ↔ g x = x := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      have h := congrArg (fun T : AddMonoid.End W => T z) r3
      have h' : g (θ₀ z) + θ₀ z = 0 := h
      exact hW' _ _ h'
    · intro hx
      refine ⟨x, ?_⟩
      have hexp : θ₀ = 1 + (g + g ^ 3 + g ^ 5) * (g + 1) := by
        rw [hθ₀]; exact exp_theta0 g h2 hg
      have hgx : (g + 1) x = 0 := by
        show g x + x = 0
        rw [hx]; exact hW x
      rw [hexp]
      show x + (g + g ^ 3 + g ^ 5) ((g + 1) x) = x
      rw [hgx, map_zero, add_zero]
  have hmem₁ : ∀ y, y ∈ AddMonoidHom.range θ₁ → h₁ y ∈ AddMonoidHom.range θ₂ := by
    rintro _ ⟨z, rfl⟩
    refine ⟨h₁ z, ?_⟩
    have := congrArg (fun T : AddMonoid.End W => T z) R4a
    exact this.symm
  have hmem₂ : ∀ y, y ∈ AddMonoidHom.range θ₂ → h₂ y ∈ AddMonoidHom.range θ₁ := by
    rintro _ ⟨z, rfl⟩
    refine ⟨h₂ z, ?_⟩
    have := congrArg (fun T : AddMonoid.End W => T z) R4b
    exact this.symm
  have hK12 : Nat.card (AddMonoidHom.range θ₁) = Nat.card (AddMonoidHom.range θ₂) := by
    apply le_antisymm
    · exact Nat.card_le_card_of_injective (fun y => ⟨h₁ y, hmem₁ y y.2⟩)
        (fun a b hab => Subtype.ext (hi₁ (congrArg Subtype.val hab)))
    · exact Nat.card_le_card_of_injective (fun y => ⟨h₂ y, hmem₂ y y.2⟩)
        (fun a b hab => Subtype.ext (hi₂ (congrArg Subtype.val hab)))
  have hmod : Nat.card W ≡ Nat.card {x : W // g x = x} [MOD 7] := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI := Fintype.ofFinite W
    let σ : Equiv.Perm W :=
      { toFun := fun x => g x
        invFun := fun x => (g ^ 6) x
        left_inv := fun x => by
          show (g ^ 6) (g x) = x
          rw [← hm, ← pow_succ, hg]
          rfl
        right_inv := fun x => by
          show g ((g ^ 6) x) = x
          rw [← hm, ← pow_succ', hg]
          rfl }
    have hσn : ∀ (n : ℕ) (x : W), (σ ^ n) x = (g ^ n) x := by
      intro n
      induction n with
      | zero => intro x; rfl
      | succ n ih =>
        intro x
        rw [pow_succ, pow_succ]
        show (σ ^ n) (σ x) = (g ^ n * g) x
        rw [ih]
        rfl
    have hσ : σ ^ 7 = 1 := by
      ext x
      rw [hσn]
      have := congrArg (fun T : AddMonoid.End W => T x) hg
      simpa using this
    have hcm := Equiv.Perm.card_compl_support_modEq (p := 7) (n := 1) (σ := σ)
      (by simpa using hσ)
    have hsup : σ.supportᶜ.card = Nat.card {x : W // g x = x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext x
      simp [Equiv.Perm.mem_support, σ]
    rw [hsup, ← Nat.card_eq_fintype_card] at hcm
    exact hcm.symm
  obtain ⟨a, ha⟩ := card_eq_two_pow_of_exp_two hW (AddMonoidHom.range θ₁)
  obtain ⟨c, hc⟩ := card_eq_two_pow_of_exp_two hW (AddMonoidHom.range θ₀)
  have hfix : Nat.card {x : W // g x = x} = Nat.card (AddMonoidHom.range θ₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hK₀ x).symm)
  have h44 : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by
    rw [← mul_pow]
    norm_num
  have hW4 : Nat.card W = 2 ^ c * 4 ^ a := by
    rw [hcard, hc, ← hK12, ha, h44]
  have hmod' : 2 ^ c * 4 ^ a ≡ 2 ^ c [MOD 7] := by
    have := hmod
    rwa [hW4, hfix, hc] at this
  have hcop : Nat.Coprime 7 (2 ^ c) := Nat.Coprime.pow_right _ (by norm_num)
  have h4 : 4 ^ a ≡ 1 [MOD 7] :=
    Nat.ModEq.cancel_left_of_coprime hcop (by rw [mul_one]; exact hmod')
  have h3 : a % 3 = 0 := by
    have h := four_pow_mod a
    have h' : 4 ^ a % 7 = 1 := h4
    rw [h'] at h
    have hlt : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : a % 3
    · rfl
    · norm_num at h
    · norm_num at h
  refine ⟨a / 3, ?_⟩
  rw [hW4, hfix, hc]
  congr 1
  conv_lhs => rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h3), mul_comm, pow_mul]
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

end Twist


section Sub

variable {𝒢 : Type*} [Group 𝒢]

noncomputable def conjEnd (E : Subgroup 𝒢) :
    ↥(Subgroup.normalizer (E : Set 𝒢)) →* AddMonoid.End (Additive ↥E) where
  toFun n := MonoidHom.toAdditive ((E.normalizerMonoidHom n : MulAut ↥E) : ↥E →* ↥E)
  map_one' := by
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul ((E.normalizerMonoidHom 1) (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' a b := by
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul ((E.normalizerMonoidHom (a * b)) (Additive.toMul x)) =
      Additive.ofMul ((E.normalizerMonoidHom a) ((E.normalizerMonoidHom b) (Additive.toMul x)))
    rw [map_mul]
    rfl

theorem conjEnd_apply (E : Subgroup 𝒢) (n : ↥(Subgroup.normalizer (E : Set 𝒢)))
    (x : Additive ↥E) :
    ((conjEnd E n x).toMul : 𝒢) = (n : 𝒢) * (x.toMul : 𝒢) * (n : 𝒢)⁻¹ := by
  rfl

theorem twist_sub (E : Subgroup 𝒢) [Finite E] (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {g h₁ h₂ : 𝒢}
    (hgE : g ∈ Subgroup.normalizer (E : Set 𝒢)) (h₁E : h₁ ∈ Subgroup.normalizer (E : Set 𝒢))
    (h₂E : h₂ ∈ Subgroup.normalizer (E : Set 𝒢)) (hg : g ^ 7 = 1)
    (hh₁ : h₁ * g * h₁⁻¹ = g ^ 3) (hh₂ : h₂ * g * h₂⁻¹ = g ^ 5) :
    ∃ j : ℕ, Nat.card E = Nat.card ↥(E ⊓ Subgroup.centralizer ({g} : Set 𝒢)) * 64 ^ j := by
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with
    mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  have hW : ∀ x : Additive ↥E, x + x = 0 := fun x => by
    apply Additive.toMul.injective
    show x.toMul * x.toMul = 1
    exact Subtype.ext (by simpa [sq] using hE2 _ x.toMul.2)
  let gn : ↥(Subgroup.normalizer (E : Set 𝒢)) := ⟨g, hgE⟩
  let h₁n : ↥(Subgroup.normalizer (E : Set 𝒢)) := ⟨h₁, h₁E⟩
  let h₂n : ↥(Subgroup.normalizer (E : Set 𝒢)) := ⟨h₂, h₂E⟩
  have hgn : gn ^ 7 = 1 := Subtype.ext (by simpa [gn] using hg)
  have hh₁n : h₁n * gn = gn ^ 3 * h₁n := Subtype.ext (by
    simpa [gn, h₁n] using (mul_inv_eq_iff_eq_mul.mp hh₁))
  have hh₂n : h₂n * gn = gn ^ 5 * h₂n := Subtype.ext (by
    simpa [gn, h₂n] using (mul_inv_eq_iff_eq_mul.mp hh₂))
  have hinj : ∀ n : ↥(Subgroup.normalizer (E : Set 𝒢)), Function.Injective (conjEnd E n) :=
    fun n x y hxy => by
      apply Additive.toMul.injective
      apply Subtype.ext
      have := congrArg (fun z => ((Additive.toMul z : ↥E) : 𝒢)) hxy
      simp only [conjEnd_apply] at this
      simpa using this
  obtain ⟨j, hj⟩ := twist_card hW (conjEnd E gn) (conjEnd E h₁n) (conjEnd E h₂n)
    (by rw [← map_pow, hgn, map_one])
    (by rw [← map_mul, ← map_pow, ← map_mul, hh₁n])
    (by rw [← map_mul, ← map_pow, ← map_mul, hh₂n]) (hinj h₁n) (hinj h₂n)
  refine ⟨j, ?_⟩
  have hc : Nat.card (Additive ↥E) = Nat.card E := Nat.card_congr Additive.toMul
  have hf : Nat.card {x : Additive ↥E // conjEnd E gn x = x} =
      Nat.card ↥(E ⊓ Subgroup.centralizer ({g} : Set 𝒢)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.toMul : 𝒢),
          Subgroup.mem_inf.mpr ⟨x.1.toMul.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩⟩
        invFun := fun y => ⟨Additive.ofMul ⟨(y : 𝒢), y.2.1⟩, ?_⟩
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    · have := congrArg (fun z => ((Additive.toMul z : ↥E) : 𝒢)) x.2
      simp only [conjEnd_apply] at this
      simp only [gn] at this
      calc (x.1.toMul : 𝒢) * g = (g * (x.1.toMul : 𝒢) * g⁻¹) * g := by rw [this]
        _ = g * (x.1.toMul : 𝒢) := by group
    · apply Additive.toMul.injective
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      show g * (y : 𝒢) * g⁻¹ = (y : 𝒢)
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
  rw [← hc, hj, hf]

end Sub

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
