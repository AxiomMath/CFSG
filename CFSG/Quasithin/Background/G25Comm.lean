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

namespace CFSG.Quasithin

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_mem_iSup {ι κ : Type*} (N J : Subgroup G)
    (hN : ∀ x ∈ J, ∀ z ∈ N, x * z * x⁻¹ ∈ N) (A : ι → Subgroup G) (B : κ → Subgroup G)
    (hA : ∀ i, A i ≤ J) (hB : ∀ j, B j ≤ J) (h : ∀ i j, ∀ a ∈ A i, ∀ b ∈ B j, ⁅a, b⁆ ∈ N) :
    ∀ a ∈ ⨆ i, A i, ∀ b ∈ ⨆ j, B j, ⁅a, b⁆ ∈ N := by
  have hAJ : (⨆ i, A i) ≤ J := iSup_le hA
  have hBJ : (⨆ j, B j) ≤ J := iSup_le hB
  have h1 : ∀ j, ∀ b ∈ B j, ∀ a ∈ ⨆ i, A i, ⁅a, b⁆ ∈ N := by
    intro j b hb a ha
    rw [Subgroup.iSup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
      exact h i j y hy b hb
    | one => simp [N.one_mem]
    | mul y z hy hz ihy ihz =>
      have hyJ : y ∈ J := hAJ (by rw [Subgroup.iSup_eq_closure]; exact hy)
      have e : ⁅y * z, b⁆ = (y * ⁅z, b⁆ * y⁻¹) * ⁅y, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hN y hyJ _ ihz) ihy
    | inv y hy ih =>
      have hyJ : y ∈ J := hAJ (by rw [Subgroup.iSup_eq_closure]; exact hy)
      have e : ⁅y⁻¹, b⁆ = y⁻¹ * ⁅y, b⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hyJ) _ (N.inv_mem ih)
  intro a ha b hb
  rw [Subgroup.iSup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
    exact h1 j y hy a ha
  | one => simp [N.one_mem]
  | mul y z hy hz ihy ihz =>
    have hyJ : y ∈ J := hBJ (by rw [Subgroup.iSup_eq_closure]; exact hy)
    have e : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ihy (hN y hyJ _ ihz)
  | inv y hy ih =>
    have hyJ : y ∈ J := hBJ (by rw [Subgroup.iSup_eq_closure]; exact hy)
    have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hN y⁻¹ (inv_mem hyJ) _ (N.inv_mem ih)

theorem mul_self_mem_iSup {ι : Type*} (N J : Subgroup G)
    (hN : ∀ x ∈ J, ∀ z ∈ N, x * z * x⁻¹ ∈ N) (A : ι → Subgroup G) (hA : ∀ i, A i ≤ J)
    (habel : ∀ a ∈ ⨆ i, A i, ∀ b ∈ ⨆ i, A i, ⁅a, b⁆ ∈ N) (hsq : ∀ i, ∀ a ∈ A i, a * a ∈ N) :
    ∀ a ∈ ⨆ i, A i, a * a ∈ N := by
  have hAJ : (⨆ i, A i) ≤ J := iSup_le hA
  intro a ha
  rw [Subgroup.iSup_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
    exact hsq i y hy
  | one => simp [N.one_mem]
  | mul y z hy hz ihy ihz =>
    have hyJ : y ∈ ⨆ i, A i := by rw [Subgroup.iSup_eq_closure]; exact hy
    have hzJ : z ∈ ⨆ i, A i := by rw [Subgroup.iSup_eq_closure]; exact hz
    have e : (y * z) * (y * z) = (y * ⁅z, y⁆ * y⁻¹) * (y * y) * (z * z) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (hN y (hAJ hyJ) _ (habel z hzJ y hyJ)) ihy) ihz
  | inv y hy ih =>
    have : y⁻¹ * y⁻¹ = (y * y)⁻¹ := (mul_inv_rev y y).symm
    rw [this]
    exact N.inv_mem ih

theorem iSup_fin_three (f : Fin 3 → Subgroup G) : ⨆ k, f k = f 0 ⊔ f 1 ⊔ f 2 := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    fin_cases k
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup f 0) (le_iSup f 1)) (le_iSup f 2)

structure TripleGrp (I S : Subgroup G) (Uk : Fin 3 → Subgroup G) : Prop where
  I_eq : I = Uk 0 ⊔ Uk 1 ⊔ Uk 2
  S_norm : ∀ x ∈ I, ∀ y ∈ S, x * y * x⁻¹ ∈ S
  S_normU : ∀ (k : Fin 3), ∀ y ∈ S, ∀ x ∈ Uk k, y * x * y⁻¹ ∈ Uk k
  comm_U : ∀ (k : Fin 3), ∀ x ∈ Uk k, ∀ y ∈ Uk k, x * y * x⁻¹ * y⁻¹ ∈ Uk 0 ⊓ Uk 1 ⊓ Uk 2
  sq_U : ∀ (k : Fin 3), ∀ x ∈ Uk k, x * x ∈ Uk 0 ⊓ Uk 1 ⊓ Uk 2
  S₂_le_S : Uk 0 ⊓ Uk 1 ⊓ Uk 2 ≤ S
  S₂_norm : ∀ x ∈ I, ∀ y ∈ Uk 0 ⊓ Uk 1 ⊓ Uk 2, x * y * x⁻¹ ∈ Uk 0 ⊓ Uk 1 ⊓ Uk 2
  S_eq : S = (Uk 0 ⊓ S) ⊔ (Uk 1 ⊓ S) ⊔ (Uk 2 ⊓ S)

namespace TripleGrp

abbrev S₂ (Uk : Fin 3 → Subgroup G) : Subgroup G := Uk 0 ⊓ Uk 1 ⊓ Uk 2

abbrev W (S : Subgroup G) (Uk : Fin 3 → Subgroup G) (k : Fin 3) : Subgroup G := Uk k ⊓ S

abbrev S₃ (S : Subgroup G) (Uk : Fin 3 → Subgroup G) : Subgroup G :=
  (W S Uk 0 ⊓ W S Uk 1) ⊔ (W S Uk 0 ⊓ W S Uk 2) ⊔ (W S Uk 1 ⊓ W S Uk 2)

variable {I S : Subgroup G} {Uk : Fin 3 → Subgroup G}

theorem S₂_le_Uk (k : Fin 3) : S₂ Uk ≤ Uk k := by
  fin_cases k
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

theorem mem_S₂_of_forall {x : G} (hx : ∀ k, x ∈ Uk k) : x ∈ S₂ Uk := ⟨⟨hx 0, hx 1⟩, hx 2⟩

theorem fin_three_cases (i j k m : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    m = i ∨ m = j ∨ m = k := by
  revert i j k m
  decide

theorem inf_inf_le_S₂ {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Uk i ⊓ Uk j ⊓ Uk k ≤ S₂ Uk := by
  intro x hx
  refine mem_S₂_of_forall fun m => ?_
  rcases fin_three_cases i j k m hij hik hjk with rfl | rfl | rfl
  · exact hx.1.1
  · exact hx.1.2
  · exact hx.2

variable (h : TripleGrp I S Uk)

include h

theorem Uk_le_I (k : Fin 3) : Uk k ≤ I := by
  rw [h.I_eq]
  fin_cases k
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem S_le_I : S ≤ I := by
  rw [h.S_eq]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact inf_le_left.trans (h.Uk_le_I 0)
  · exact inf_le_left.trans (h.Uk_le_I 1)
  · exact inf_le_left.trans (h.Uk_le_I 2)

theorem S₂_le_W (k : Fin 3) : S₂ Uk ≤ W S Uk k := le_inf (S₂_le_Uk k) h.S₂_le_S

theorem comm_Uk_S (k : Fin 3) {x s : G} (hx : x ∈ Uk k) (hs : s ∈ S) :
    x * s * x⁻¹ * s⁻¹ ∈ W S Uk k := by
  refine ⟨?_, ?_⟩
  · have h1 : s * x⁻¹ * s⁻¹ ∈ Uk k := h.S_normU k s hs x⁻¹ ((Uk k).inv_mem hx)
    have := (Uk k).mul_mem hx h1
    simpa [mul_assoc] using this
  · exact S.mul_mem (h.S_norm x (h.Uk_le_I k hx) s hs) (S.inv_mem hs)

theorem W_norm (k : Fin 3) {s w : G} (hs : s ∈ S) (hw : w ∈ W S Uk k) :
    s * w * s⁻¹ ∈ W S Uk k := by
  have h1 := h.comm_Uk_S k hw.1 hs
  have h2 : s * w * s⁻¹ = (w * s * w⁻¹ * s⁻¹)⁻¹ * w := by group
  rw [h2]
  exact (W S Uk k).mul_mem ((W S Uk k).inv_mem h1) hw

theorem comm_W_W (i j : Fin 3) {a b : G} (ha : a ∈ W S Uk i) (hb : b ∈ W S Uk j) :
    ⁅a, b⁆ ∈ W S Uk i ⊓ W S Uk j := by
  refine ⟨h.comm_Uk_S i ha.1 hb.2, ?_⟩
  have h1 := h.comm_Uk_S j hb.1 ha.2
  have : ⁅a, b⁆ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact (W S Uk j).inv_mem h1

theorem comm_Wij_W {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) {a b : G}
    (ha : a ∈ W S Uk i ⊓ W S Uk j) (hb : b ∈ W S Uk k) : ⁅a, b⁆ ∈ S₂ Uk := by
  by_cases hki : k = i
  · subst hki
    exact h.comm_U k a ha.1.1 b hb.1
  by_cases hkj : k = j
  · subst hkj
    exact h.comm_U k a ha.2.1 b hb.1
  have h1 := h.comm_W_W i k ha.1 hb
  have h2 := h.comm_W_W j k ha.2 hb
  exact inf_inf_le_S₂ hij (Ne.symm hki) (Ne.symm hkj) ⟨⟨h1.1.1, h2.1.1⟩, h1.2.1⟩

theorem S₂_le_S₃ : S₂ Uk ≤ S₃ S Uk := fun _ hx =>
  Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨h.S₂_le_W 0 hx, h.S₂_le_W 1 hx⟩)

omit h in
theorem S₃_le_S : S₃ S Uk ≤ S :=
  sup_le (sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right))
    (inf_le_left.trans inf_le_right)

omit h in
theorem Wij_le_S₃ {i j : Fin 3} (hij : i ≠ j) : W S Uk i ⊓ W S Uk j ≤ S₃ S Uk := by
  revert hij
  fin_cases i <;> fin_cases j <;> intro hij
  · exact absurd rfl hij
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact (inf_comm _ _).le.trans (le_sup_left.trans le_sup_left)
  · exact absurd rfl hij
  · exact le_sup_right
  · exact (inf_comm _ _).le.trans (le_sup_right.trans le_sup_left)
  · exact (inf_comm _ _).le.trans le_sup_right
  · exact absurd rfl hij

theorem comm_S₃_S {a b : G} (ha : a ∈ S₃ S Uk) (hb : b ∈ S) : ⁅a, b⁆ ∈ S₂ Uk := by
  let A : Fin 3 → Subgroup G :=
    ![W S Uk 0 ⊓ W S Uk 1, W S Uk 0 ⊓ W S Uk 2, W S Uk 1 ⊓ W S Uk 2]
  let B : Fin 3 → Subgroup G := fun k => W S Uk k
  have hA : (⨆ i, A i) = S₃ S Uk := by rw [iSup_fin_three]; rfl
  have hB : (⨆ k, B k) = S := by rw [iSup_fin_three]; exact h.S_eq.symm
  refine comm_mem_iSup (S₂ Uk) S (fun x hx z hz => h.S₂_norm x (h.S_le_I hx) z hz) A B ?_ ?_ ?_
    a (hA ▸ ha) b (hB ▸ hb)
  · intro i
    fin_cases i
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_left.trans inf_le_right
  · intro k
    exact inf_le_right
  · intro i j a ha b hb
    fin_cases i
    · exact h.comm_Wij_W (i := 0) (j := 1) (by decide) j ha hb
    · exact h.comm_Wij_W (i := 0) (j := 2) (by decide) j ha hb
    · exact h.comm_Wij_W (i := 1) (j := 2) (by decide) j ha hb

theorem S₃_norm_S {s y : G} (hs : s ∈ S) (hy : y ∈ S₃ S Uk) : s * y * s⁻¹ ∈ S₃ S Uk := by
  have h1 : ⁅y, s⁆ ∈ S₂ Uk := h.comm_S₃_S hy hs
  have h2 : s * y * s⁻¹ = (y * s * y⁻¹ * s⁻¹)⁻¹ * y := by group
  rw [h2]
  exact (S₃ S Uk).mul_mem ((S₃ S Uk).inv_mem (h.S₂_le_S₃ h1)) hy

theorem S_abel {a b : G} (ha : a ∈ S) (hb : b ∈ S) : ⁅a, b⁆ ∈ S₃ S Uk := by
  let B : Fin 3 → Subgroup G := fun k => W S Uk k
  have hB : (⨆ k, B k) = S := by rw [iSup_fin_three]; exact h.S_eq.symm
  refine comm_mem_iSup (S₃ S Uk) S (fun x hx z hz => h.S₃_norm_S hx hz) B B (fun k => inf_le_right)
    (fun k => inf_le_right) ?_ a (hB ▸ ha) b (hB ▸ hb)
  intro i j a ha b hb
  by_cases hij : i = j
  · subst hij
    exact h.S₂_le_S₃ (h.comm_U i a ha.1 b hb.1)
  · exact Wij_le_S₃ hij (h.comm_W_W i j ha hb)

theorem S_sq {a : G} (ha : a ∈ S) : a * a ∈ S₃ S Uk := by
  let B : Fin 3 → Subgroup G := fun k => W S Uk k
  have hB : (⨆ k, B k) = S := by rw [iSup_fin_three]; exact h.S_eq.symm
  refine mul_self_mem_iSup (S₃ S Uk) S (fun x hx z hz => h.S₃_norm_S hx hz) B
    (fun k => inf_le_right) (fun a ha b hb => h.S_abel (hB ▸ ha) (hB ▸ hb)) ?_ a (hB ▸ ha)
  intro i a ha
  exact h.S₂_le_S₃ (h.sq_U i a ha.1)

theorem S₃_sq {a : G} (ha : a ∈ S₃ S Uk) : a * a ∈ S₂ Uk := by
  let A : Fin 3 → Subgroup G :=
    ![W S Uk 0 ⊓ W S Uk 1, W S Uk 0 ⊓ W S Uk 2, W S Uk 1 ⊓ W S Uk 2]
  have hA : (⨆ i, A i) = S₃ S Uk := by rw [iSup_fin_three]; rfl
  have hAS : ∀ i, A i ≤ S := by
    intro i
    fin_cases i
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_left.trans inf_le_right
  refine mul_self_mem_iSup (S₂ Uk) S (fun x hx z hz => h.S₂_norm x (h.S_le_I hx) z hz) A hAS
    (fun a ha b hb => h.comm_S₃_S (hA ▸ ha) (S₃_le_S (hA ▸ hb))) ?_ a (hA ▸ ha)
  intro i a ha
  fin_cases i
  · exact h.sq_U 0 a ha.1.1
  · exact h.sq_U 0 a ha.1.1
  · exact h.sq_U 1 a ha.1.1

omit h in
theorem le_normalizer_of_forall_conj {X K : Subgroup G} (hK : ∀ x ∈ X, ∀ w ∈ K, x * w * x⁻¹ ∈ K) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => hK x hx w hw, fun hw => ?_⟩
  simpa [mul_assoc] using hK x⁻¹ (X.inv_mem hx) _ hw

theorem S_le_normalizer_Wij {i j : Fin 3} :
    S ≤ Subgroup.normalizer ((W S Uk i ⊓ W S Uk j : Subgroup G) : Set G) :=
  le_normalizer_of_forall_conj fun _ hs _ hw => ⟨h.W_norm i hs hw.1, h.W_norm j hs hw.2⟩

theorem S_le_normalizer_S₃ : S ≤ Subgroup.normalizer ((S₃ S Uk : Subgroup G) : Set G) :=
  le_normalizer_of_forall_conj fun _ hs _ hw => h.S₃_norm_S hs hw

theorem mem_W₀_sup_S₃ {x : G} (hx : x ∈ W S Uk 0 ⊔ S₃ S Uk) :
    ∃ w ∈ W S Uk 0, ∃ z ∈ W S Uk 1 ⊓ W S Uk 2, w * z = x := by
  have hle : W S Uk 0 ⊔ S₃ S Uk ≤ W S Uk 0 ⊔ (W S Uk 1 ⊓ W S Uk 2) := by
    refine sup_le le_sup_left (sup_le (sup_le ?_ ?_) le_sup_right)
    · exact inf_le_left.trans le_sup_left
    · exact inf_le_left.trans le_sup_left
  have hnorm : W S Uk 0 ≤ Subgroup.normalizer ((W S Uk 1 ⊓ W S Uk 2 : Subgroup G) : Set G) :=
    (inf_le_right : W S Uk 0 ≤ S).trans h.S_le_normalizer_Wij
  have := hle hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at this
  exact this

theorem mem_W₁_sup_S₃ {x : G} (hx : x ∈ W S Uk 1 ⊔ S₃ S Uk) :
    ∃ w ∈ W S Uk 1, ∃ y ∈ W S Uk 0 ⊓ W S Uk 2, w * y = x := by
  have hle : W S Uk 1 ⊔ S₃ S Uk ≤ W S Uk 1 ⊔ (W S Uk 0 ⊓ W S Uk 2) := by
    refine sup_le le_sup_left (sup_le (sup_le ?_ le_sup_right) ?_)
    · exact inf_le_right.trans le_sup_left
    · exact inf_le_left.trans le_sup_left
  have hnorm : W S Uk 1 ≤ Subgroup.normalizer ((W S Uk 0 ⊓ W S Uk 2 : Subgroup G) : Set G) :=
    (inf_le_right : W S Uk 1 ≤ S).trans h.S_le_normalizer_Wij
  have := hle hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at this
  exact this

theorem inter_W_S₃ {x : G} (hx0 : x ∈ W S Uk 0 ⊔ S₃ S Uk) (hx1 : x ∈ W S Uk 1 ⊔ S₃ S Uk) :
    x ∈ S₃ S Uk := by
  obtain ⟨w₀, hw₀, z, hz, rfl⟩ := h.mem_W₀_sup_S₃ hx0
  obtain ⟨w₁, hw₁, y, hy, he⟩ := h.mem_W₁_sup_S₃ hx1
  have hzS : z ∈ S := hz.1.2
  have hy' : z * y * z⁻¹ ∈ W S Uk 0 ⊓ W S Uk 2 := h.S_le_normalizer_Wij hzS |> fun hn =>
    (Subgroup.mem_normalizer_iff.1 hn y).1 hy
  set y' := z * y * z⁻¹ with hy'def
  set t := w₀ * y'⁻¹ with ht
  have htW1 : t ∈ W S Uk 1 := by
    have : t = w₁ * z⁻¹ := by
      rw [ht, hy'def]
      have : w₀ = w₁ * y * z⁻¹ := by
        rw [he]
        group
      rw [this]
      group
    rw [this]
    exact (W S Uk 1).mul_mem hw₁ ((W S Uk 1).inv_mem hz.1)
  have htW0 : t ∈ W S Uk 0 := (W S Uk 0).mul_mem hw₀ ((W S Uk 0).inv_mem hy'.1)
  have htX : t ∈ S₃ S Uk := Wij_le_S₃ (by decide : (0 : Fin 3) ≠ 1) ⟨htW0, htW1⟩
  have hy'S : y' ∈ S₃ S Uk := Wij_le_S₃ (by decide : (0 : Fin 3) ≠ 2) hy'
  have hzS₃ : z ∈ S₃ S Uk := Wij_le_S₃ (by decide : (1 : Fin 3) ≠ 2) hz
  have e : w₀ * z = t * y' * z := by
    rw [ht]
    group
  rw [e]
  exact (S₃ S Uk).mul_mem ((S₃ S Uk).mul_mem htX hy'S) hzS₃

theorem U_inf_normalizer_le {a c : Fin 3} (hac : a ≠ c) :
    Uk a ⊓ Subgroup.normalizer ((W S Uk c : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((S₃ S Uk : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj fun x hx y hy => ?_
  have hpair : ∀ p q : Fin 3, p ≠ q → ∀ y ∈ W S Uk p ⊓ W S Uk q, x * y * x⁻¹ ∈ S₃ S Uk := by
    intro p q hpq y hy
    have hyS₃ : y ∈ S₃ S Uk := Wij_le_S₃ hpq hy
    have hmul : ∀ z ∈ S₂ Uk, x * y * x⁻¹ = z * y → x * y * x⁻¹ ∈ S₃ S Uk := by
      intro z hz he
      rw [he]
      exact (S₃ S Uk).mul_mem (h.S₂_le_S₃ hz) hyS₃
    by_cases hp : p = a
    · subst hp
      exact hmul _ (h.comm_U p x hx.1 y hy.1.1) (by group)
    by_cases hq : q = a
    · subst hq
      exact hmul _ (h.comm_U q x hx.1 y hy.2.1) (by group)
    have hcy : y ∈ W S Uk c := by
      rcases fin_three_cases a p q c (Ne.symm hp) (Ne.symm hq) hpq with hca | hcp | hcq
      · exact absurd hca.symm hac
      · rw [hcp]; exact hy.1
      · rw [hcq]; exact hy.2
    have hxy : x * y * x⁻¹ ∈ W S Uk c := (Subgroup.mem_normalizer_iff.1 hx.2 y).1 hcy
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ W S Uk a ⊓ W S Uk c :=
      ⟨h.comm_Uk_S a hx.1 hcy.2, (W S Uk c).mul_mem hxy ((W S Uk c).inv_mem hcy)⟩
    have := (S₃ S Uk).mul_mem (Wij_le_S₃ hac hcomm) hyS₃
    simpa [mul_assoc] using this
  let C : Subgroup G := (S₃ S Uk).comap (MulAut.conj x).toMonoidHom
  have hC : S₃ S Uk ≤ C := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      exact hpair 0 1 (by decide) y hy
    · intro y hy
      exact hpair 0 2 (by decide) y hy
    · intro y hy
      exact hpair 1 2 (by decide) y hy
  exact hC hy

theorem I_le_normalizer_S₃
    (hdec : ∀ (a b c : Fin 3), a ≠ b → a ≠ c → b ≠ c → ∀ u ∈ Uk a,
      ∃ u₁ ∈ Uk a ⊓ Subgroup.normalizer ((W S Uk c : Subgroup G) : Set G),
        ∃ u₂ ∈ Uk a ⊓ Subgroup.normalizer ((W S Uk b : Subgroup G) : Set G),
          ∃ s ∈ W S Uk a, u = u₁ * u₂ * s) :
    I ≤ Subgroup.normalizer ((S₃ S Uk : Subgroup G) : Set G) := by
  have hU : ∀ a, Uk a ≤ Subgroup.normalizer ((S₃ S Uk : Subgroup G) : Set G) := by
    intro a u hu
    obtain ⟨b, c, hab, hac, hbc⟩ : ∃ b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      fin_cases a
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨u₁, h₁, u₂, h₂, s, hs, rfl⟩ := hdec a b c hab hac hbc u hu
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.U_inf_normalizer_le hac h₁)
      (h.U_inf_normalizer_le hab h₂)) (h.S_le_normalizer_S₃ hs.2)
  rw [h.I_eq]
  exact sup_le (sup_le (hU 0) (hU 1)) (hU 2)

end TripleGrp

end CFSG.Quasithin
