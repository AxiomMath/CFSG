module

import CFSG.RankThree.PartTwo.Source.EightActionCentralizer
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
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
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
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

namespace CFSG.RankThree.PartTwo.Source

variable {G : Type*} [Group G]

theorem mem_centralizer_of_kleinFour {E : Subgroup G} (hE : IsKleinFour E) {x : G}
    (hx3 : x ^ 3 = 1) (hxE : x ∈ Subgroup.normalizer (E : Set G)) {e : G} (heE : e ∈ E)
    (he1 : e ≠ 1) (hxe : x * e = e * x) : x ∈ Subgroup.centralizer (E : Set G) := by
  have key : ∀ g : E, x * g * x⁻¹ = g := by
    intro g
    by_cases hg1 : g = 1
    · rw [hg1, Subgroup.coe_one, mul_one, mul_inv_cancel]
    by_cases hge : (g : G) = e
    · rw [hge, hxe, mul_inv_cancel_right]
    have hσ : ∀ h : E, x * h * x⁻¹ ∈ E := fun h => (Subgroup.mem_normalizer_iff.mp hxE h).mp h.2
    let σ : E → E := fun h => ⟨x * h * x⁻¹, hσ h⟩
    have hσ1 : σ g ≠ 1 := by
      intro h
      apply hg1
      apply Subtype.ext
      have h' : x * (g : G) * x⁻¹ = 1 := congrArg Subtype.val h
      calc (g : G) = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = 1 := by rw [h']; group
    let e' : E := ⟨e, heE⟩
    have he'1 : e' ≠ 1 := fun h => he1 (congrArg Subtype.val h)
    have hge' : g ≠ e' := fun h => hge (congrArg Subtype.val h)
    have hσe : σ g ≠ e' := by
      intro h
      apply hge
      have h' : x * (g : G) * x⁻¹ = e := congrArg Subtype.val h
      calc (g : G) = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x⁻¹ * e * x := by rw [h']
        _ = e := by rw [mul_assoc, ← hxe, inv_mul_cancel_left]
    by_contra hne
    have hσg : σ g ≠ g := fun h => hne (congrArg Subtype.val h)
    have h1 := IsKleinFour.eq_mul_of_ne_all he'1 hg1 (Ne.symm hge') hσ1 hσe hσg
    have h1' : x * (g : G) * x⁻¹ = e * g := congrArg Subtype.val h1
    have hee : e * e = 1 := congrArg Subtype.val (IsKleinFour.mul_self e')
    have h2 : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = e * g := by
      calc x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = x * (x * (e * g) * x⁻¹) * x⁻¹ := by rw [h1']
        _ = x * (e * (x * g * x⁻¹)) * x⁻¹ := by
            rw [show x * (e * g) * x⁻¹ = (x * e) * g * x⁻¹ by group, hxe]; group
        _ = x * (e * (e * g)) * x⁻¹ := by rw [h1']
        _ = x * g * x⁻¹ := by rw [← mul_assoc e e, hee, one_mul]
        _ = e * g := h1'
    have h3 : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := by
      have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
      calc x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = x * (x * x) * g * (x * (x * x))⁻¹ := by group
        _ = g := by rw [hx3', one_mul, inv_one, mul_one]
    rw [h3] at h2
    apply he1
    calc e = e * g * (g : G)⁻¹ := by group
      _ = g * (g : G)⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel _
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := key ⟨h, hh⟩
  calc h * x = x * h * x⁻¹ * x := by rw [this]
    _ = x * h := by group

theorem kleinFour_mul_comm {P : Subgroup G} (hP : IsKleinFour P) {p q : G} (hp : p ∈ P)
    (hq : q ∈ P) : p * q = q * p :=
  congrArg Subtype.val (isMulCommutative_iff.mp (@IsKleinFour.isMulCommutative P _ hP) ⟨p, hp⟩
    ⟨q, hq⟩)

theorem kleinFour_sq {P : Subgroup G} (hP : IsKleinFour P) {p : G} (hp : p ∈ P) : p ^ 2 = 1 := by
  rw [sq]
  exact congrArg Subtype.val (@IsKleinFour.mul_self P _ hP ⟨p, hp⟩)

theorem commute_of_le_centralizer {P Q : Subgroup G} (h : P ≤ Subgroup.centralizer (Q : Set G))
    {p q : G} (hp : p ∈ P) (hq : q ∈ Q) : Commute p q :=
  (Subgroup.mem_centralizer_iff.mp (h hp) q hq).symm

theorem mem_sup_zpowers_iff {H : Subgroup G} {s : G} (hs2 : s ^ 2 = 1)
    (hsH : ∀ h ∈ H, h * s = s * h) {t : G} :
    t ∈ H ⊔ Subgroup.zpowers s ↔ t ∈ H ∨ t * s ∈ H := by
  have hss : s * s = 1 := by rw [← sq]; exact hs2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have key : ∀ t, t * s ∈ H → s * t = t * s := by
    intro t ht
    have h := hsH (t * s) ht
    calc s * t = s * (t * s) * s := by rw [mul_assoc, mul_assoc, hss, mul_one]
      _ = t * s * s * s := by rw [← h]
      _ = t * s := by rw [mul_assoc (t * s), hss, mul_one]
  constructor
  · intro ht
    let M : Subgroup G :=
      { carrier := {t | t ∈ H ∨ t * s ∈ H}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (H.mul_mem ha hb)
          · exact Or.inr (by rw [mul_assoc]; exact H.mul_mem ha hb)
          · exact Or.inr (by rw [mul_assoc, hsH b hb, ← mul_assoc]; exact H.mul_mem ha hb)
          · refine Or.inl ?_
            have : a * b = a * s * (b * s) := by
              rw [mul_assoc a s, ← mul_assoc s b s, key b hb, mul_assoc b s s, hss, mul_one]
            rw [this]
            exact H.mul_mem ha hb
        one_mem' := Or.inl H.one_mem
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rcases ha with ha | ha
          · exact Or.inl (H.inv_mem ha)
          · refine Or.inr ?_
            have : a⁻¹ * s = (a * s)⁻¹ := by rw [← key a ha, mul_inv_rev, hsinv]
            rw [this]
            exact H.inv_mem ha }
    have hle : H ⊔ Subgroup.zpowers s ≤ M :=
      sup_le (fun h hh => Or.inl hh)
        (Subgroup.zpowers_le.mpr (Or.inr (by rw [hss]; exact H.one_mem)))
    exact hle ht
  · rintro (ht | ht)
    · exact Subgroup.mem_sup_left ht
    · have : t = t * s * s := by rw [mul_assoc, hss, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))

theorem mem_zpowers_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) {t : G} :
    t ∈ Subgroup.zpowers z ↔ t = 1 ∨ t = z := by
  have h := mem_sup_zpowers_iff (H := ⊥) hz
    (fun h hh => by rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]) (t := t)
  rw [bot_sup_eq, Subgroup.mem_bot, Subgroup.mem_bot] at h
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz)
  rw [h, mul_eq_one_iff_eq_inv, hzinv]

theorem sup_zpowers_involution [Finite G] {H : Subgroup G} (hHc : IsMulCommutative H)
    (hH2 : ∀ h ∈ H, h ^ 2 = 1) {s : G} (hs : s ∉ H) (hs2 : s ^ 2 = 1)
    (hsH : ∀ h ∈ H, h * s = s * h) :
    IsMulCommutative (H ⊔ Subgroup.zpowers s : Subgroup G) ∧
      (∀ t ∈ H ⊔ Subgroup.zpowers s, t ^ 2 = 1) ∧
      Nat.card (H ⊔ Subgroup.zpowers s : Subgroup G) = Nat.card H * 2 := by
  obtain ⟨hc, hcard⟩ := sup_zpowers_card (p := 2) hHc hs hs2 hsH
  refine ⟨hc, fun t ht => ?_, hcard⟩
  rcases (mem_sup_zpowers_iff hs2 hsH).mp ht with ht | ht
  · exact hH2 t ht
  · obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, h * s = t :=
      ⟨t * s, ht, by rw [mul_assoc, ← sq, hs2, mul_one]⟩
    have h1 := hH2 h hh
    have h2 := hsH h hh
    calc (h * s) ^ 2 = h * (s * h) * s := by rw [sq]; simp only [mul_assoc]
      _ = h * (h * s) * s := by rw [← h2]
      _ = h ^ 2 * s ^ 2 := by rw [sq, sq]; simp only [mul_assoc]
      _ = 1 := by rw [h1, hs2, one_mul]

theorem elemEight_of_involutions [Finite G] {z₁ z₂ z₃ : G} (h₁ : z₁ ^ 2 = 1) (h₂ : z₂ ^ 2 = 1)
    (h₃ : z₃ ^ 2 = 1) (h₁₂ : Commute z₁ z₂) (h₁₃ : Commute z₁ z₃) (h₂₃ : Commute z₂ z₃)
    (hz₁ : z₁ ≠ 1) (hz₂ : z₂ ∉ Subgroup.zpowers z₁)
    (hz₃ : z₃ ∉ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) :
    IsMulCommutative
        (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₃ : Subgroup G) ∧
      (∀ t ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₃, t ^ 2 = 1) ∧
      Nat.card
        (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₃ : Subgroup G) = 8 := by
  have hsq₁ : ∀ t ∈ Subgroup.zpowers z₁, t ^ 2 = 1 := by
    intro t ht
    rcases (mem_zpowers_of_sq_eq_one h₁).mp ht with rfl | rfl
    · exact one_pow 2
    · exact h₁
  have hcard₁ : Nat.card (Subgroup.zpowers z₁) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h₁ hz₁]
  have hcomm₂ : ∀ h ∈ Subgroup.zpowers z₁, h * z₂ = z₂ * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (h₁₂.zpow_left k).eq
  obtain ⟨hc₂, hsq₂, hcard₂⟩ :=
    sup_zpowers_involution (isMulCommutative_zpowers z₁) hsq₁ hz₂ h₂ hcomm₂
  have hcomm₃ : ∀ h ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, h * z₃ = z₃ * h := by
    intro h hh
    have hle : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤ Subgroup.centralizer {z₃} :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h₁₃.eq))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h₂₃.eq))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  obtain ⟨hc₃, hsq₃, hcard₃⟩ := sup_zpowers_involution hc₂ hsq₂ hz₃ h₃ hcomm₃
  exact ⟨hc₃, hsq₃, by rw [hcard₃, hcard₂, hcard₁]⟩

theorem ne_of_twisted {w y c : G} (hc : c ≠ 1) (h : w * y = c * (y * w)) : y * w ≠ w * y := by
  intro hyw
  apply hc
  have h' : c * (y * w) = 1 * (y * w) := by rw [one_mul, ← h, hyw]
  exact mul_right_cancel h'

theorem not_mem_of_twisted {H : Subgroup G} {w y c : G} (hc : c ≠ 1) (h : w * y = c * (y * w))
    (hH : H ≤ Subgroup.centralizer {y}) : w ∉ H := fun hw =>
  ne_of_twisted hc h (Subgroup.mem_centralizer_singleton_iff.mp (hH hw)).symm

theorem mul_eq_of_twisted {x y x' c : G} (h : x * y = c * (y * x)) (h1 : Commute x' y) :
    x * x' * y = c * (y * (x * x')) := by
  calc x * x' * y = x * (x' * y) := mul_assoc _ _ _
    _ = x * (y * x') := by rw [h1.eq]
    _ = x * y * x' := (mul_assoc _ _ _).symm
    _ = c * (y * (x * x')) := by rw [h]; simp only [mul_assoc]

theorem mul_mul_eq_of_twisted {x y x' y' c c' : G} (h : x * y = c * (y * x))
    (h' : x' * y' = c' * (y' * x')) (h1 : Commute x' y) (h2 : Commute x y')
    (h3 : Commute c' (y * x)) : x * x' * (y * y') = c * c' * (y * y' * (x * x')) := by
  calc x * x' * (y * y') = x * (x' * y) * y' := by simp only [mul_assoc]
    _ = x * (y * x') * y' := by rw [h1.eq]
    _ = (x * y) * (x' * y') := by simp only [mul_assoc]
    _ = c * (y * x) * (c' * (y' * x')) := by rw [h, h']
    _ = c * (y * x * c') * (y' * x') := by simp only [mul_assoc]
    _ = c * (c' * (y * x)) * (y' * x') := by rw [h3.eq]
    _ = c * c' * (y * (x * y') * x') := by simp only [mul_assoc]
    _ = c * c' * (y * (y' * x) * x') := by rw [h2.eq]
    _ = c * c' * (y * y' * (x * x')) := by simp only [mul_assoc]

structure IsQuaternionTriple (P : Subgroup G) (a b z : G) : Prop where
  a_mem : a ∈ P
  b_mem : b ∈ P
  z_mem : z ∈ P
  z_ne_one : z ≠ 1
  z_sq : z ^ 2 = 1
  a_sq : a ^ 2 = z
  b_sq : b ^ 2 = z
  ab : a * b = z * (b * a)
  ba : b * a = z * (a * b)
  central : ∀ q ∈ P, Commute q z

theorem exists_isQuaternionTriple {P : Subgroup G} (e : P ≃* QuaternionGroup 2) :
    ∃ a b z : G, IsQuaternionTriple P a b z := by
  refine ⟨e.symm (QuaternionGroup.a 1), e.symm (QuaternionGroup.xa 0),
    e.symm (QuaternionGroup.a 2), ⟨(e.symm _).2, (e.symm _).2, (e.symm _).2, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · intro h
    have h' : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact absurd h' (by decide)
  · rw [← Subgroup.coe_pow, ← map_pow,
      show (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow,
      show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 by decide]
  · rw [← Subgroup.coe_pow, ← map_pow,
      show (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 by decide]
  · simp only [← Subgroup.coe_mul, ← map_mul]
    rw [show (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) by decide]
  · simp only [← Subgroup.coe_mul, ← map_mul]
    rw [show (QuaternionGroup.xa 0 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) by decide]
  · intro q hq
    have hc : ∀ q' : QuaternionGroup 2, q' * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q' := by
      decide
    have h := congrArg (fun q' => ((e.symm q' : P) : G)) (hc (e ⟨q, hq⟩))
    simp only [map_mul, Subgroup.coe_mul, MulEquiv.symm_apply_apply] at h
    exact h

theorem IsQuaternionTriple.mul_ne {P : Subgroup G} {a b z : G}
    (hQ : IsQuaternionTriple P a b z) : a * b ≠ b * a :=
  ne_of_twisted hQ.z_ne_one hQ.ba

structure SmallFixedAction (r : ℕ) (Y S : Subgroup G) : Prop where
  comm : IsMulCommutative Y
  pow_eq_one : ∀ y ∈ Y, y ^ r = 1
  le_normalizer : S ≤ Subgroup.normalizer (Y : Set G)
  faithful : S ⊓ Subgroup.centralizer (Y : Set G) = ⊥
  card_le : ∀ t ∈ S, t ≠ 1 → Nat.card (Y ⊓ Subgroup.centralizer {t} : Subgroup G) ≤ r ^ 2

namespace SmallFixedAction

theorem inf_centralizer_eq_bot {r : ℕ} {Y S : Subgroup G} (h : SmallFixedAction r Y S)
    {H : Subgroup G} (hH : H ≤ S) : H ⊓ Subgroup.centralizer (Y : Set G) = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right _ hH).trans h.faithful.le)

theorem commute_of_elemEight [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {F K : Subgroup G} (hFS : F ≤ S)
    (hFc : IsMulCommutative F) (hF2 : ∀ t ∈ F, t ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hKS : K ≤ S) (hKF : K ≤ Subgroup.centralizer (F : Set G)) :
    ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k :=
  commute_of_eight_action hr2 h.comm h.pow_eq_one hFc hF2 hF8 (hFS.trans h.le_normalizer)
    (h.inf_centralizer_eq_bot hFS) (fun t ht ht1 => h.card_le t (hFS ht) ht1)
    (hKS.trans h.le_normalizer) hKF (h.inf_centralizer_eq_bot hKS)

theorem false_of_elemEight [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {Y S : Subgroup G}
    (h : SmallFixedAction r Y S) {F : Subgroup G} {s : G} (hFS : F ≤ S)
    (hFc : IsMulCommutative F) (hF2 : ∀ t ∈ F, t ^ 2 = 1) (hF8 : Nat.card F = 8) (hsS : s ∈ S)
    (hs2 : s ^ 2 = 1) (hsF : s ∉ F) (hsc : s ∈ Subgroup.centralizer (F : Set G)) : False := by
  obtain ⟨u, hu, hu1, hlt⟩ := exists_large_fixed_of_eight_action_involution hr2 h.comm
    h.pow_eq_one hFc hF2 hF8 (hFS.trans h.le_normalizer) (h.inf_centralizer_eq_bot hFS)
    (fun t ht ht1 => h.card_le t (hFS ht) ht1) hs2 hsF (h.le_normalizer hsS) hsc
  exact absurd (h.card_le u (sup_le hFS (Subgroup.zpowers_le.mpr hsS) hu) hu1) (not_le.mpr hlt)

theorem false_of_elemEight_noncomm [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {z₁ z₂ z₃ : G} (h₁ : z₁ ^ 2 = 1)
    (h₂ : z₂ ^ 2 = 1) (h₃ : z₃ ^ 2 = 1) (h₁₂ : Commute z₁ z₂) (h₁₃ : Commute z₁ z₃)
    (h₂₃ : Commute z₂ z₃) (hz₁ : z₁ ≠ 1) (hz₂ : z₂ ∉ Subgroup.zpowers z₁)
    (hz₃ : z₃ ∉ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) (hz₁S : z₁ ∈ S) (hz₂S : z₂ ∈ S)
    (hz₃S : z₃ ∈ S) {u v : G} (huS : u ∈ S) (hvS : v ∈ S)
    (hu : Commute u z₁ ∧ Commute u z₂ ∧ Commute u z₃)
    (hv : Commute v z₁ ∧ Commute v z₂ ∧ Commute v z₃) (huv : u * v ≠ v * u) : False := by
  obtain ⟨hFc, hF2, hF8⟩ := elemEight_of_involutions h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hz₁ hz₂ hz₃
  set F := Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₃ with hF
  have hFS : F ≤ S := sup_le (sup_le (Subgroup.zpowers_le.mpr hz₁S)
    (Subgroup.zpowers_le.mpr hz₂S)) (Subgroup.zpowers_le.mpr hz₃S)
  have hmem : ∀ w : G, Commute w z₁ → Commute w z₂ → Commute w z₃ →
      w ∈ Subgroup.centralizer (F : Set G) := by
    intro w hw₁ hw₂ hw₃
    have hle : F ≤ Subgroup.centralizer {w} :=
      sup_le (sup_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hw₁.eq.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hw₂.eq.symm)))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hw₃.eq.symm))
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ht)
  exact huv (h.commute_of_elemEight hr2 hFS hFc hF2 hF8
    (inf_le_left : S ⊓ Subgroup.centralizer (F : Set G) ≤ S) inf_le_right u
    (Subgroup.mem_inf.mpr ⟨huS, hmem u hu.1 hu.2.1 hu.2.2⟩) v
    (Subgroup.mem_inf.mpr ⟨hvS, hmem v hv.1 hv.2.1 hv.2.2⟩))

theorem false_of_two_kleinFour [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P P' : Subgroup G} (hP : IsKleinFour P)
    (hP' : IsKleinFour P') (hPS : P ≤ S) (hP'S : P' ≤ S)
    (hPP' : P ≤ Subgroup.centralizer (P' : Set G)) {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hxC : x ∉ Subgroup.centralizer (P : Set G))
    (hxP' : x ∈ Subgroup.centralizer (P' : Set G)) : False := by
  have hdisj : ∀ e ∈ P, e ∈ P' → e = 1 := by
    intro e he he'
    by_contra he1
    exact hxC (mem_centralizer_of_kleinFour hP hx3 hxN he he1
      (Subgroup.mem_centralizer_iff.mp hxP' e he').symm)
  obtain ⟨s, hsP', hs1⟩ : ∃ s ∈ P', s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : P' = ⊥ := eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr (hcon g hg)
    have h4 := hP'.card_four
    rw [hbot, Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  have hs2 : s ^ 2 = 1 := kleinFour_sq hP' hsP'
  have hzs : Subgroup.zpowers s < P' := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hsP') fun heq => ?_
    have h4 := hP'.card_four
    rw [← heq, Nat.card_zpowers, orderOf_eq_prime hs2 hs1] at h4
    exact absurd h4 (by norm_num)
  obtain ⟨s', hs'P', hs'⟩ := IsConcreteLE.exists_of_lt hzs
  have hsP : s ∉ P := fun hs => hs1 (hdisj s hs hsP')
  have hsPc : ∀ p ∈ P, p * s = s * p := fun p hp => (commute_of_le_centralizer hPP' hp hsP').eq
  obtain ⟨hFc, hF2, hF8⟩ := sup_zpowers_involution
    (@IsKleinFour.isMulCommutative P _ hP) (fun p hp => kleinFour_sq hP hp) hsP hs2 hsPc
  have hF8' : Nat.card (P ⊔ Subgroup.zpowers s : Subgroup G) = 8 := by
    rw [hF8, hP.card_four]
  refine h.false_of_elemEight hr2 (sup_le hPS (Subgroup.zpowers_le.mpr (hP'S hsP'))) hFc hF2
    hF8' (hP'S hs'P') (kleinFour_sq hP' hs'P') ?_ ?_
  · intro hmem
    rcases (mem_sup_zpowers_iff hs2 hsPc).mp hmem with h1 | h1
    · exact hs' (by rw [hdisj s' h1 hs'P']; exact Subgroup.one_mem _)
    · apply hs'
      rw [eq_inv_of_mul_eq_one_left (hdisj _ h1 (P'.mul_mem hs'P' hsP'))]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers s)
  · have hle : P ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer {s'} :=
      sup_le (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_le_centralizer hPP' hp hs'P').eq)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (kleinFour_mul_comm hP' hsP' hs'P')))
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ht)

theorem false_of_kleinFour_quaternion [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P Q : Subgroup G} (hP : IsKleinFour P)
    {a b z : G} (hQ : IsQuaternionTriple Q a b z) (hPS : P ≤ S) (hQS : Q ≤ S)
    (hPQ : P ≤ Subgroup.centralizer (Q : Set G)) {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hxC : x ∉ Subgroup.centralizer (P : Set G))
    (hxQ : x ∈ Subgroup.centralizer (Q : Set G)) : False := by
  have hzP : z ∉ P := fun hz => hxC (mem_centralizer_of_kleinFour hP hx3 hxN hz hQ.z_ne_one
    (Subgroup.mem_centralizer_iff.mp hxQ z hQ.z_mem).symm)
  have hzc : ∀ p ∈ P, p * z = z * p := fun p hp => (commute_of_le_centralizer hPQ hp hQ.z_mem).eq
  obtain ⟨hFc, hF2, hF8⟩ := sup_zpowers_involution
    (@IsKleinFour.isMulCommutative P _ hP) (fun p hp => kleinFour_sq hP hp) hzP hQ.z_sq hzc
  have hF8' : Nat.card (P ⊔ Subgroup.zpowers z : Subgroup G) = 8 := by
    rw [hF8, hP.card_four]
  have hzQ : z ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => (hQ.central q hq).eq
  have hQF : Q ≤ Subgroup.centralizer ((P ⊔ Subgroup.zpowers z : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (sup_le hPQ (Subgroup.zpowers_le.mpr hzQ))
  exact hQ.mul_ne (h.commute_of_elemEight hr2
    (sup_le hPS (Subgroup.zpowers_le.mpr (hQS hQ.z_mem))) hFc hF2 hF8' hQS hQF a hQ.a_mem b
    hQ.b_mem)

theorem false_of_quaternion_eq [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P₁ P₂ P₃ : Subgroup G}
    {a₁ b₁ a₂ b₂ a₃ b₃ z z₃ : G} (hQ₁ : IsQuaternionTriple P₁ a₁ b₁ z)
    (hQ₂ : IsQuaternionTriple P₂ a₂ b₂ z) (hQ₃ : IsQuaternionTriple P₃ a₃ b₃ z₃)
    (hS₁ : P₁ ≤ S) (hS₂ : P₂ ≤ S) (hS₃ : P₃ ≤ S)
    (h₁₂ : P₁ ≤ Subgroup.centralizer (P₂ : Set G)) (h₁₃ : P₁ ≤ Subgroup.centralizer (P₃ : Set G))
    (h₂₃ : P₂ ≤ Subgroup.centralizer (P₃ : Set G)) : False := by
  have c12 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₂ → Commute p q := commute_of_le_centralizer h₁₂
  have c13 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₁₃
  have c23 : ∀ {p q : G}, p ∈ P₂ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₂₃
  have hzz : z * z = 1 := by rw [← sq]; exact hQ₁.z_sq
  have hw₁2 : (a₁ * a₂) ^ 2 = 1 := by
    rw [(c12 hQ₁.a_mem hQ₂.a_mem).mul_pow, hQ₁.a_sq, hQ₂.a_sq, ← sq, hQ₁.z_sq]
  have hw₂2 : (b₁ * b₂) ^ 2 = 1 := by
    rw [(c12 hQ₁.b_mem hQ₂.b_mem).mul_pow, hQ₁.b_sq, hQ₂.b_sq, ← sq, hQ₁.z_sq]
  have hzw₁ : Commute z (a₁ * a₂) :=
    (hQ₁.central a₁ hQ₁.a_mem).symm.mul_right (hQ₂.central a₂ hQ₂.a_mem).symm
  have hzw₂ : Commute z (b₁ * b₂) :=
    (hQ₁.central b₁ hQ₁.b_mem).symm.mul_right (hQ₂.central b₂ hQ₂.b_mem).symm
  have hw₁w₂ : Commute (a₁ * a₂) (b₁ * b₂) := by
    have := mul_mul_eq_of_twisted hQ₁.ab hQ₂.ab (c12 hQ₁.b_mem hQ₂.a_mem).symm
      (c12 hQ₁.a_mem hQ₂.b_mem) (hQ₁.central _ (P₁.mul_mem hQ₁.b_mem hQ₁.a_mem)).symm
    rw [hzz, one_mul] at this
    exact this
  have hw₁ : a₁ * a₂ ∉ Subgroup.zpowers z :=
    not_mem_of_twisted hQ₁.z_ne_one (mul_eq_of_twisted hQ₁.ab (c12 hQ₁.b_mem hQ₂.a_mem).symm)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (hQ₁.central b₁ hQ₁.b_mem).eq.symm))
  have hw₂ : b₁ * b₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers (a₁ * a₂) :=
    not_mem_of_twisted hQ₁.z_ne_one (mul_eq_of_twisted hQ₁.ba (c12 hQ₁.a_mem hQ₂.b_mem).symm)
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (hQ₁.central a₁ hQ₁.a_mem).eq.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          ((Commute.refl a₁).mul_right (c12 hQ₁.a_mem hQ₂.a_mem)).eq.symm)))
  exact h.false_of_elemEight_noncomm hr2 hQ₁.z_sq hw₁2 hw₂2 hzw₁ hzw₂ hw₁w₂ hQ₁.z_ne_one hw₁
    hw₂ (hS₁ hQ₁.z_mem) (S.mul_mem (hS₁ hQ₁.a_mem) (hS₂ hQ₂.a_mem))
    (S.mul_mem (hS₁ hQ₁.b_mem) (hS₂ hQ₂.b_mem)) (hS₃ hQ₃.a_mem) (hS₃ hQ₃.b_mem)
    ⟨(c13 hQ₁.z_mem hQ₃.a_mem).symm,
      (c13 hQ₁.a_mem hQ₃.a_mem).symm.mul_right (c23 hQ₂.a_mem hQ₃.a_mem).symm,
      (c13 hQ₁.b_mem hQ₃.a_mem).symm.mul_right (c23 hQ₂.b_mem hQ₃.a_mem).symm⟩
    ⟨(c13 hQ₁.z_mem hQ₃.b_mem).symm,
      (c13 hQ₁.a_mem hQ₃.b_mem).symm.mul_right (c23 hQ₂.a_mem hQ₃.b_mem).symm,
      (c13 hQ₁.b_mem hQ₃.b_mem).symm.mul_right (c23 hQ₂.b_mem hQ₃.b_mem).symm⟩
    hQ₃.mul_ne

theorem false_of_quaternion_mul_eq [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P₁ P₂ P₃ : Subgroup G}
    {a₁ b₁ z₁ a₂ b₂ z₂ a₃ b₃ z₃ : G} (hQ₁ : IsQuaternionTriple P₁ a₁ b₁ z₁)
    (hQ₂ : IsQuaternionTriple P₂ a₂ b₂ z₂) (hQ₃ : IsQuaternionTriple P₃ a₃ b₃ z₃)
    (hz₃ : z₃ = z₁ * z₂) (hne : z₁ ≠ z₂) (hS₁ : P₁ ≤ S) (hS₂ : P₂ ≤ S) (hS₃ : P₃ ≤ S)
    (h₁₂ : P₁ ≤ Subgroup.centralizer (P₂ : Set G)) (h₁₃ : P₁ ≤ Subgroup.centralizer (P₃ : Set G))
    (h₂₃ : P₂ ≤ Subgroup.centralizer (P₃ : Set G)) : False := by
  have c12 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₂ → Commute p q := commute_of_le_centralizer h₁₂
  have c13 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₁₃
  have c23 : ∀ {p q : G}, p ∈ P₂ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₂₃
  have hz₁₂ : Commute z₁ z₂ := c12 hQ₁.z_mem hQ₂.z_mem
  have hz₁z₁ : z₁ * z₁ = 1 := by rw [← sq]; exact hQ₁.z_sq
  have hz₂z₂ : z₂ * z₂ = 1 := by rw [← sq]; exact hQ₂.z_sq
  have hrel : z₁ * (z₂ * z₃) = 1 := by
    rw [hz₃, ← mul_assoc z₂ z₁ z₂, ← hz₁₂.eq, mul_assoc z₁ z₂ z₂, hz₂z₂, mul_one, hz₁z₁]
  have ha₁a : Commute a₁ (a₂ * a₃) :=
    (c12 hQ₁.a_mem hQ₂.a_mem).mul_right (c13 hQ₁.a_mem hQ₃.a_mem)
  have hab₁ : Commute (a₂ * a₃) b₁ :=
    (c12 hQ₁.b_mem hQ₂.a_mem).symm.mul_left (c13 hQ₁.b_mem hQ₃.a_mem).symm
  have ha₁b : Commute a₁ (b₂ * b₃) :=
    (c12 hQ₁.a_mem hQ₂.b_mem).mul_right (c13 hQ₁.a_mem hQ₃.b_mem)
  have hw2 : (a₁ * (a₂ * a₃)) ^ 2 = 1 := by
    rw [ha₁a.mul_pow, (c23 hQ₂.a_mem hQ₃.a_mem).mul_pow, hQ₁.a_sq, hQ₂.a_sq, hQ₃.a_sq, hrel]
  have hz₁w : Commute z₁ (a₁ * (a₂ * a₃)) :=
    (hQ₁.central a₁ hQ₁.a_mem).symm.mul_right
      ((c12 hQ₁.z_mem hQ₂.a_mem).mul_right (c13 hQ₁.z_mem hQ₃.a_mem))
  have hz₂w : Commute z₂ (a₁ * (a₂ * a₃)) :=
    (c12 hQ₁.a_mem hQ₂.z_mem).symm.mul_right
      ((hQ₂.central a₂ hQ₂.a_mem).symm.mul_right (c23 hQ₂.z_mem hQ₃.a_mem))
  have hz₂ : z₂ ∉ Subgroup.zpowers z₁ := by
    rw [mem_zpowers_of_sq_eq_one hQ₁.z_sq]
    rintro (h1 | h1)
    · exact hQ₂.z_ne_one h1
    · exact hne h1.symm
  have hw : a₁ * (a₂ * a₃) ∉ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ :=
    not_mem_of_twisted hQ₁.z_ne_one (mul_eq_of_twisted hQ₁.ab hab₁)
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (hQ₁.central b₁ hQ₁.b_mem).eq.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (c12 hQ₁.b_mem hQ₂.z_mem).eq.symm)))
  have hinner := mul_mul_eq_of_twisted hQ₂.ab hQ₃.ab (c23 hQ₂.b_mem hQ₃.a_mem).symm
    (c23 hQ₂.a_mem hQ₃.b_mem)
    ((c23 hQ₂.b_mem hQ₃.z_mem).symm.mul_right (c23 hQ₂.a_mem hQ₃.z_mem).symm)
  have houter := mul_mul_eq_of_twisted hQ₁.ab hinner hab₁ ha₁b
    ((c12 (P₁.mul_mem hQ₁.b_mem hQ₁.a_mem) hQ₂.z_mem).symm.mul_left
      (c13 (P₁.mul_mem hQ₁.b_mem hQ₁.a_mem) hQ₃.z_mem).symm)
  rw [hrel, one_mul] at houter
  have hvb : b₁ * (b₂ * b₃) * a₁ = z₁ * (a₁ * (b₁ * (b₂ * b₃))) :=
    mul_eq_of_twisted hQ₁.ba ha₁b.symm
  exact h.false_of_elemEight_noncomm hr2 hQ₁.z_sq hQ₂.z_sq hw2 hz₁₂ hz₁w hz₂w hQ₁.z_ne_one hz₂
    hw (hS₁ hQ₁.z_mem) (hS₂ hQ₂.z_mem)
    (S.mul_mem (hS₁ hQ₁.a_mem) (S.mul_mem (hS₂ hQ₂.a_mem) (hS₃ hQ₃.a_mem))) (hS₁ hQ₁.a_mem)
    (S.mul_mem (hS₁ hQ₁.b_mem) (S.mul_mem (hS₂ hQ₂.b_mem) (hS₃ hQ₃.b_mem)))
    ⟨hQ₁.central a₁ hQ₁.a_mem, c12 hQ₁.a_mem hQ₂.z_mem, (Commute.refl a₁).mul_right ha₁a⟩
    ⟨(hQ₁.central b₁ hQ₁.b_mem).mul_left
        ((c12 hQ₁.z_mem hQ₂.b_mem).symm.mul_left (c13 hQ₁.z_mem hQ₃.b_mem).symm),
      (c12 hQ₁.b_mem hQ₂.z_mem).mul_left
        ((hQ₂.central b₂ hQ₂.b_mem).mul_left (c23 hQ₂.z_mem hQ₃.b_mem).symm),
      houter.symm⟩
    (ne_of_twisted hQ₁.z_ne_one hvb)

theorem false_of_quaternion_independent [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P₁ P₂ P₃ : Subgroup G}
    {a₁ b₁ z₁ a₂ b₂ z₂ a₃ b₃ z₃ : G} (hQ₁ : IsQuaternionTriple P₁ a₁ b₁ z₁)
    (hQ₂ : IsQuaternionTriple P₂ a₂ b₂ z₂) (hQ₃ : IsQuaternionTriple P₃ a₃ b₃ z₃)
    (e₁₂ : z₁ ≠ z₂) (e₁₃ : z₁ ≠ z₃) (e₂₃ : z₂ ≠ z₃) (e : z₃ ≠ z₁ * z₂) (hS₁ : P₁ ≤ S)
    (hS₂ : P₂ ≤ S) (hS₃ : P₃ ≤ S) (h₁₂ : P₁ ≤ Subgroup.centralizer (P₂ : Set G))
    (h₁₃ : P₁ ≤ Subgroup.centralizer (P₃ : Set G))
    (h₂₃ : P₂ ≤ Subgroup.centralizer (P₃ : Set G)) : False := by
  have c12 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₂ → Commute p q := commute_of_le_centralizer h₁₂
  have c13 : ∀ {p q : G}, p ∈ P₁ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₁₃
  have c23 : ∀ {p q : G}, p ∈ P₂ → q ∈ P₃ → Commute p q := commute_of_le_centralizer h₂₃
  have hz₁₂ : Commute z₁ z₂ := c12 hQ₁.z_mem hQ₂.z_mem
  have hz₂ : z₂ ∉ Subgroup.zpowers z₁ := by
    rw [mem_zpowers_of_sq_eq_one hQ₁.z_sq]
    rintro (h1 | h1)
    · exact hQ₂.z_ne_one h1
    · exact e₁₂ h1.symm
  have hcomm : ∀ t ∈ Subgroup.zpowers z₁, t * z₂ = z₂ * t := by
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hz₁₂.zpow_left k).eq
  have hz₂inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hQ₂.z_sq)
  have hz₃ : z₃ ∉ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := by
    rw [mem_sup_zpowers_iff hQ₂.z_sq hcomm, mem_zpowers_of_sq_eq_one hQ₁.z_sq,
      mem_zpowers_of_sq_eq_one hQ₁.z_sq]
    rintro ((h1 | h1) | (h1 | h1))
    · exact hQ₃.z_ne_one h1
    · exact e₁₃ h1.symm
    · exact e₂₃ (by rw [eq_inv_of_mul_eq_one_left h1, hz₂inv])
    · exact e (by rw [eq_mul_inv_of_mul_eq h1, hz₂inv])
  exact h.false_of_elemEight_noncomm hr2 hQ₁.z_sq hQ₂.z_sq hQ₃.z_sq hz₁₂
    (c13 hQ₁.z_mem hQ₃.z_mem) (c23 hQ₂.z_mem hQ₃.z_mem) hQ₁.z_ne_one hz₂ hz₃ (hS₁ hQ₁.z_mem)
    (hS₂ hQ₂.z_mem) (hS₃ hQ₃.z_mem) (hS₁ hQ₁.a_mem) (hS₁ hQ₁.b_mem)
    ⟨hQ₁.central a₁ hQ₁.a_mem, c12 hQ₁.a_mem hQ₂.z_mem, c13 hQ₁.a_mem hQ₃.z_mem⟩
    ⟨hQ₁.central b₁ hQ₁.b_mem, c12 hQ₁.b_mem hQ₂.z_mem, c13 hQ₁.b_mem hQ₃.z_mem⟩ hQ₁.mul_ne

theorem false_of_three_quaternion [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {Y S : Subgroup G} (h : SmallFixedAction r Y S) {P₁ P₂ P₃ : Subgroup G}
    {a₁ b₁ z₁ a₂ b₂ z₂ a₃ b₃ z₃ : G} (hQ₁ : IsQuaternionTriple P₁ a₁ b₁ z₁)
    (hQ₂ : IsQuaternionTriple P₂ a₂ b₂ z₂) (hQ₃ : IsQuaternionTriple P₃ a₃ b₃ z₃)
    (hS₁ : P₁ ≤ S) (hS₂ : P₂ ≤ S) (hS₃ : P₃ ≤ S) (h₁₂ : P₁ ≤ Subgroup.centralizer (P₂ : Set G))
    (h₁₃ : P₁ ≤ Subgroup.centralizer (P₃ : Set G))
    (h₂₃ : P₂ ≤ Subgroup.centralizer (P₃ : Set G)) : False := by
  have h₂₁ := Subgroup.le_centralizer_iff.mp h₁₂
  have h₃₁ := Subgroup.le_centralizer_iff.mp h₁₃
  have h₃₂ := Subgroup.le_centralizer_iff.mp h₂₃
  by_cases e₁₂ : z₁ = z₂
  · subst e₁₂
    exact h.false_of_quaternion_eq hr2 hQ₁ hQ₂ hQ₃ hS₁ hS₂ hS₃ h₁₂ h₁₃ h₂₃
  by_cases e₁₃ : z₁ = z₃
  · subst e₁₃
    exact h.false_of_quaternion_eq hr2 hQ₁ hQ₃ hQ₂ hS₁ hS₃ hS₂ h₁₃ h₁₂ h₃₂
  by_cases e₂₃ : z₂ = z₃
  · subst e₂₃
    exact h.false_of_quaternion_eq hr2 hQ₂ hQ₃ hQ₁ hS₂ hS₃ hS₁ h₂₃ h₂₁ h₃₁
  by_cases e : z₃ = z₁ * z₂
  · exact h.false_of_quaternion_mul_eq hr2 hQ₁ hQ₂ hQ₃ e e₁₂ hS₁ hS₂ hS₃ h₁₂ h₁₃ h₂₃
  exact h.false_of_quaternion_independent hr2 hQ₁ hQ₂ hQ₃ e₁₂ e₁₃ e₂₃ e hS₁ hS₂ hS₃ h₁₂ h₁₃ h₂₃

theorem false_of_pieces [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {Y S : Subgroup G}
    (h : SmallFixedAction r Y S) (P : Fin 3 → Subgroup G) (hPS : ∀ i, P i ≤ S)
    (hP : ∀ i, IsKleinFour (P i) ∨ Nonempty (P i ≃* QuaternionGroup 2))
    (hPc : ∀ i j, i ≠ j → P i ≤ Subgroup.centralizer (P j : Set G)) (x : Fin 3 → G)
    (hx3 : ∀ i, x i ^ 3 = 1) (hxN : ∀ i, x i ∈ Subgroup.normalizer (P i : Set G))
    (hxC : ∀ i, x i ∉ Subgroup.centralizer (P i : Set G))
    (hxP : ∀ i j, i ≠ j → x i ∈ Subgroup.centralizer (P j : Set G)) : False := by
  have hK4 : ∀ i j, i ≠ j → IsKleinFour (P i) → False := by
    intro i j hij hi
    rcases hP j with hj | hj
    · exact h.false_of_two_kleinFour hr2 hi hj (hPS i) (hPS j) (hPc i j hij) (hx3 i) (hxN i)
        (hxC i) (hxP i j hij)
    · obtain ⟨a, b, z, hQ⟩ := exists_isQuaternionTriple hj.some
      exact h.false_of_kleinFour_quaternion hr2 hi hQ (hPS i) (hPS j) (hPc i j hij) (hx3 i)
        (hxN i) (hxC i) (hxP i j hij)
  have hQ8 : ∀ i, Nonempty (P i ≃* QuaternionGroup 2) := by
    intro i
    rcases hP i with hi | hi
    · exact (hK4 i (i + 1) (by fin_cases i <;> decide) hi).elim
    · exact hi
  obtain ⟨a₀, b₀, z₀, hQ₀⟩ := exists_isQuaternionTriple (hQ8 0).some
  obtain ⟨a₁, b₁, z₁, hQ₁⟩ := exists_isQuaternionTriple (hQ8 1).some
  obtain ⟨a₂, b₂, z₂, hQ₂⟩ := exists_isQuaternionTriple (hQ8 2).some
  exact h.false_of_three_quaternion hr2 hQ₀ hQ₁ hQ₂ (hPS 0) (hPS 1) (hPS 2)
    (hPc 0 1 (by decide)) (hPc 0 2 (by decide)) (hPc 1 2 (by decide))

end SmallFixedAction

end CFSG.RankThree.PartTwo.Source
