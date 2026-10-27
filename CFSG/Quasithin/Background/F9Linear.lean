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

namespace CFSG.Quasithin.F9Lin

variable {Γ : Type*} [Group Γ]

@[expose] def commSub (x : Γ) (S : Subgroup Γ) : Subgroup Γ :=
  Subgroup.closure {c | ∃ e ∈ S, c = x * e * x⁻¹ * e⁻¹}

@[expose] def fixSub (x : Γ) (S : Subgroup Γ) : Subgroup Γ :=
  S ⊓ Subgroup.centralizer ({x} : Set Γ)

theorem mem_fixSub {x c : Γ} {S : Subgroup Γ} : c ∈ fixSub x S ↔ c ∈ S ∧ x * c * x⁻¹ = c := by
  unfold fixSub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    have := h x (Set.mem_singleton x)
    rw [this]; group
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    calc z * c = (z * c * z⁻¹) * z := by group
      _ = c * z := by rw [h]

section Commutative

variable {S : Subgroup Γ} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x : Γ}
  (hx : x ∈ Subgroup.normalizer (S : Set Γ))

include hS hx in
theorem mem_commSub {c : Γ} : c ∈ commSub x S ↔ ∃ e ∈ S, c = x * e * x⁻¹ * e⁻¹ := by
  have hxe : ∀ e ∈ S, x * e * x⁻¹ ∈ S := fun e he => (Subgroup.mem_normalizer_iff.mp hx e).mp he
  constructor
  · intro hc
    induction hc using Subgroup.closure_induction with
    | mem c hc => exact hc
    | one => exact ⟨1, S.one_mem, by group⟩
    | mul c d _ _ hc hd =>
      obtain ⟨e₁, he₁, rfl⟩ := hc
      obtain ⟨e₂, he₂, rfl⟩ := hd
      refine ⟨e₁ * e₂, S.mul_mem he₁ he₂, ?_⟩
      have h1 : (x * e₂ * x⁻¹) * e₁⁻¹ = e₁⁻¹ * (x * e₂ * x⁻¹) := hS _ (hxe e₂ he₂) _ (S.inv_mem he₁)
      have h2 : e₂⁻¹ * e₁⁻¹ = e₁⁻¹ * e₂⁻¹ := hS _ (S.inv_mem he₂) _ (S.inv_mem he₁)
      calc x * e₁ * x⁻¹ * e₁⁻¹ * (x * e₂ * x⁻¹ * e₂⁻¹)
          = x * e₁ * x⁻¹ * (e₁⁻¹ * (x * e₂ * x⁻¹)) * e₂⁻¹ := by group
        _ = x * e₁ * x⁻¹ * ((x * e₂ * x⁻¹) * e₁⁻¹) * e₂⁻¹ := by rw [h1]
        _ = (x * e₁ * x⁻¹) * (x * e₂ * x⁻¹) * (e₁⁻¹ * e₂⁻¹) := by group
        _ = (x * e₁ * x⁻¹) * (x * e₂ * x⁻¹) * (e₂⁻¹ * e₁⁻¹) := by rw [h2]
        _ = x * (e₁ * e₂) * x⁻¹ * (e₁ * e₂)⁻¹ := by group
    | inv c _ hc =>
      obtain ⟨e, he, rfl⟩ := hc
      refine ⟨e⁻¹, S.inv_mem he, ?_⟩
      have h1 : (x * e * x⁻¹)⁻¹ * e = e * (x * e * x⁻¹)⁻¹ := hS _ (S.inv_mem (hxe e he)) _ he
      calc (x * e * x⁻¹ * e⁻¹)⁻¹ = e * (x * e * x⁻¹)⁻¹ := by group
        _ = (x * e * x⁻¹)⁻¹ * e := h1.symm
        _ = x * e⁻¹ * x⁻¹ * e⁻¹⁻¹ := by group
  · rintro ⟨e, he, rfl⟩
    exact Subgroup.subset_closure ⟨e, he, rfl⟩

include hS hx in
theorem commSub_le : commSub x S ≤ S := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := (mem_commSub hS hx).mp hc
  exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp hx e).mp he |> fun h => h) (S.inv_mem he)

@[expose] def commHom : ↥S →* ↥S where
  toFun e := ⟨x * e * x⁻¹ * e⁻¹, S.mul_mem ((Subgroup.mem_normalizer_iff.mp hx e).mp e.2)
    (S.inv_mem e.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' e₁ e₂ := by
    apply Subtype.ext
    have hxe : ∀ e ∈ S, x * e * x⁻¹ ∈ S := fun e he =>
      (Subgroup.mem_normalizer_iff.mp hx e).mp he
    have h1 : (x * (e₂ : Γ) * x⁻¹) * (e₁ : Γ)⁻¹ = (e₁ : Γ)⁻¹ * (x * (e₂ : Γ) * x⁻¹) :=
      hS _ (hxe _ e₂.2) _ (S.inv_mem e₁.2)
    have h2 : (e₂ : Γ)⁻¹ * (e₁ : Γ)⁻¹ = (e₁ : Γ)⁻¹ * (e₂ : Γ)⁻¹ :=
      hS _ (S.inv_mem e₂.2) _ (S.inv_mem e₁.2)
    show x * ((e₁ : Γ) * e₂) * x⁻¹ * ((e₁ : Γ) * e₂)⁻¹ =
      (x * (e₁ : Γ) * x⁻¹ * (e₁ : Γ)⁻¹) * (x * (e₂ : Γ) * x⁻¹ * (e₂ : Γ)⁻¹)
    calc x * ((e₁ : Γ) * e₂) * x⁻¹ * ((e₁ : Γ) * e₂)⁻¹
        = (x * (e₁ : Γ) * x⁻¹) * (x * (e₂ : Γ) * x⁻¹) * ((e₂ : Γ)⁻¹ * (e₁ : Γ)⁻¹) := by group
      _ = (x * (e₁ : Γ) * x⁻¹) * (x * (e₂ : Γ) * x⁻¹) * ((e₁ : Γ)⁻¹ * (e₂ : Γ)⁻¹) := by rw [h2]
      _ = x * (e₁ : Γ) * x⁻¹ * ((x * (e₂ : Γ) * x⁻¹) * (e₁ : Γ)⁻¹) * (e₂ : Γ)⁻¹ := by group
      _ = x * (e₁ : Γ) * x⁻¹ * ((e₁ : Γ)⁻¹ * (x * (e₂ : Γ) * x⁻¹)) * (e₂ : Γ)⁻¹ := by rw [h1]
      _ = (x * (e₁ : Γ) * x⁻¹ * (e₁ : Γ)⁻¹) * (x * (e₂ : Γ) * x⁻¹ * (e₂ : Γ)⁻¹) := by group

theorem commHom_apply (e : ↥S) : ((commHom hS hx e : ↥S) : Γ) = x * e * x⁻¹ * (e : Γ)⁻¹ := rfl

include hS hx in
theorem commSub_eq_map_range : commSub x S = (commHom hS hx).range.map S.subtype := by
  ext c
  rw [mem_commSub hS hx, Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨commHom hS hx ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, e.2, rfl⟩

include hS hx in
theorem fixSub_eq_map_ker : fixSub x S = (commHom hS hx).ker.map S.subtype := by
  ext c
  rw [mem_fixSub, Subgroup.mem_map]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨⟨c, hc⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show x * c * x⁻¹ * c⁻¹ = 1
    rw [h]; group
  · rintro ⟨e, he, rfl⟩
    rw [MonoidHom.mem_ker] at he
    have h1 : x * (e : Γ) * x⁻¹ * (e : Γ)⁻¹ = 1 := congrArg Subtype.val he
    refine ⟨e.2, ?_⟩
    calc x * (e : Γ) * x⁻¹ = (x * (e : Γ) * x⁻¹ * (e : Γ)⁻¹) * e := by group
      _ = e := by rw [h1]; group

end Commutative

section Abstract

variable {E : Type*} [CommGroup E] [Finite E]

omit [Finite E] in
theorem card_map_eq_of_inf_ker (f : E →* E) (P : Subgroup E) (h : P ⊓ f.ker = ⊥) :
    Nat.card (P.map f) = Nat.card P := by
  have hinj : Function.Injective (f.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : f (a : E) = 1 := ha
    have h2 : (a : E) ∈ P ⊓ f.ker := ⟨a.2, h1⟩
    rw [h] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hr : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem map_range_eq (f g : E →* E) (hB : g.range ⊓ f.ker = ⊥)
    (hC : Nat.card f.range = Nat.card g.range) : g.range.map f = f.range := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_range f g.range) ?_
  rw [card_map_eq_of_inf_ker f g.range hB, hC]

theorem two_involutions (f g : E →* E) (hf : ∀ e, f (f e) = 1) (hg : ∀ e, g (g e) = 1)
    (hA : f.range ⊓ g.ker = ⊥) (hB : g.range ⊓ f.ker = ⊥)
    (hC : Nat.card f.range = Nat.card g.range) :
    f.range ⊓ g.range = ⊥ ∧ f.ker ⊓ (f.range ⊔ g.range) = f.range ∧
      (f.range ⊔ g.range).map f = f.range ∧
      (f.range ⊔ g.range) ⊔ (f.ker ⊓ g.ker) = ⊤ ∧ (f.range ⊔ g.range) ⊓ (f.ker ⊓ g.ker) = ⊥ := by
  have hPf : f.range ≤ f.ker := by
    rintro _ ⟨e, rfl⟩
    exact hf e
  have hPg : g.range ≤ g.ker := by
    rintro _ ⟨e, rfl⟩
    exact hg e
  have h1 : f.range ⊓ g.range = ⊥ := le_bot_iff.mp (hA ▸ inf_le_inf_left _ hPg)
  have h2 : ∀ (f g : E →* E), f.range ≤ f.ker → g.range ⊓ f.ker = ⊥ →
      f.ker ⊓ (f.range ⊔ g.range) = f.range := by
    intro f g hPf hB
    refine le_antisymm ?_ (le_inf hPf le_sup_left)
    rintro z ⟨hzK, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hz
    have h1 : f a = 1 := hPf ha
    have h2 : f (a * b) = 1 := hzK
    rw [map_mul, h1, one_mul] at h2
    have : b ∈ g.range ⊓ f.ker := ⟨hb, h2⟩
    rw [hB] at this
    rw [Subgroup.mem_bot.mp this, mul_one]
    exact ha
  have h3 : ∀ (f g : E →* E), f.range ≤ f.ker → g.range ⊓ f.ker = ⊥ →
      Nat.card f.range = Nat.card g.range → (f.range ⊔ g.range).map f = f.range := by
    intro f g hPf hB hC
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hPf, map_range_eq f g hB hC, bot_sup_eq]
  have e2 := h2 f g hPf hB
  have e2' := h2 g f hPg hA
  rw [sup_comm] at e2'
  refine ⟨h1, e2, h3 f g hPf hB hC, ?_, ?_⟩
  ·
    rw [eq_top_iff]
    intro e _
    have hfe : f e ∈ g.range.map f := by
      rw [map_range_eq f g hB hC]; exact ⟨e, rfl⟩
    have hge : g e ∈ f.range.map g := by
      rw [map_range_eq g f hA hC.symm]; exact ⟨e, rfl⟩
    obtain ⟨b, hb, hbe⟩ := hfe
    obtain ⟨a, ha, hae⟩ := hge
    have hfa : f a = 1 := hPf ha
    have hgb : g b = 1 := hPg hb
    have hw : a * b ∈ f.range ⊔ g.range := Subgroup.mul_mem_sup ha hb
    have hC' : e * (a * b)⁻¹ ∈ f.ker ⊓ g.ker := by
      refine ⟨?_, ?_⟩
      · show f (e * (a * b)⁻¹) = 1
        rw [map_mul, map_inv, map_mul, hfa, one_mul, hbe]; simp
      · show g (e * (a * b)⁻¹) = 1
        rw [map_mul, map_inv, map_mul, hgb, mul_one, hae]; simp
    have := Subgroup.mul_mem_sup hw hC'
    have e' : a * b * (e * (a * b)⁻¹) = e := by rw [mul_left_comm, mul_inv_cancel, mul_one]
    rwa [e'] at this
  ·
    rw [eq_bot_iff]
    rintro z ⟨hzW, hzf, hzg⟩
    have h4 : z ∈ f.range := by rw [← e2]; exact ⟨hzf, hzW⟩
    have h5 : z ∈ g.range := by rw [← e2']; exact ⟨hzg, hzW⟩
    have : z ∈ f.range ⊓ g.range := ⟨h4, h5⟩
    rw [h1] at this
    exact this

end Abstract

section Decomposition

variable [Finite Γ]

omit [Finite Γ] in
theorem commHom_commHom {S : Subgroup Γ} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS2 : ∀ a ∈ S, a * a = 1) {x : Γ} (hx : x ∈ Subgroup.normalizer (S : Set Γ))
    (hxx : ∀ e ∈ S, x * x * e * (x * x)⁻¹ = e) (e : ↥S) :
    commHom hS hx (commHom hS hx e) = 1 := by
  apply Subtype.ext
  have ha : x * (e : Γ) * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hx e).mp e.2
  set a : Γ := x * (e : Γ) * x⁻¹ with ha_def
  have h1 : x * a * x⁻¹ = (e : Γ) := by
    have := hxx e e.2
    calc x * a * x⁻¹ = x * x * (e : Γ) * (x * x)⁻¹ := by rw [ha_def]; group
      _ = e := this
  have h2 : (e : Γ) * a⁻¹ = a⁻¹ * (e : Γ) := hS _ e.2 _ (S.inv_mem ha)
  have hc : x * (a * (e : Γ)⁻¹) * x⁻¹ = (e : Γ) * a⁻¹ := by
    calc x * (a * (e : Γ)⁻¹) * x⁻¹ = (x * a * x⁻¹) * (x * (e : Γ)⁻¹ * x⁻¹) := by group
      _ = (e : Γ) * a⁻¹ := by rw [h1, ha_def]; group
  show x * (a * (e : Γ)⁻¹) * x⁻¹ * (a * (e : Γ)⁻¹)⁻¹ = 1
  rw [hc]
  have h5 : a * a = 1 := hS2 _ ha
  calc (e : Γ) * a⁻¹ * (a * (e : Γ)⁻¹)⁻¹ = (e : Γ) * a⁻¹ * ((e : Γ) * a⁻¹) := by group
    _ = (e : Γ) * (a⁻¹ * (e : Γ)) * a⁻¹ := by group
    _ = (e : Γ) * ((e : Γ) * a⁻¹) * a⁻¹ := by rw [← h2]
    _ = ((e : Γ) * (e : Γ)) * (a * a)⁻¹ := by group
    _ = 1 := by rw [hS2 _ e.2, h5]; simp

theorem two_involutions_sub {S : Subgroup Γ} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS2 : ∀ a ∈ S, a * a = 1) {x y : Γ}
    (hx : x ∈ Subgroup.normalizer (S : Set Γ)) (hy : y ∈ Subgroup.normalizer (S : Set Γ))
    (hxx : ∀ e ∈ S, x * x * e * (x * x)⁻¹ = e) (hyy : ∀ e ∈ S, y * y * e * (y * y)⁻¹ = e)
    (hA : commSub x S ⊓ fixSub y S = ⊥) (hB : commSub y S ⊓ fixSub x S = ⊥)
    (hC : Nat.card (commSub x S) = Nat.card (commSub y S)) :
    commSub x S ⊓ commSub y S = ⊥ ∧ fixSub x S ⊓ (commSub x S ⊔ commSub y S) = commSub x S ∧
      commSub x (commSub x S ⊔ commSub y S) = commSub x S ∧
      (commSub x S ⊔ commSub y S) ⊔ (fixSub x S ⊓ fixSub y S) = S ∧
      (commSub x S ⊔ commSub y S) ⊓ (fixSub x S ⊓ fixSub y S) = ⊥ := by
  let _ : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := fun a b => Subtype.ext (hS _ a.2 _ b.2) }
  have hinj := S.subtype_injective
  have hsx := commSub_eq_map_range hS hx
  have hsy := commSub_eq_map_range hS hy
  have hkx := fixSub_eq_map_ker hS hx
  have hky := fixSub_eq_map_ker hS hy
  have hA' : (commHom hS hx).range ⊓ (commHom hS hy).ker = ⊥ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_inf_eq _ _ _ hinj, ← hsx, ← hky, hA, Subgroup.map_bot]
  have hB' : (commHom hS hy).range ⊓ (commHom hS hx).ker = ⊥ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_inf_eq _ _ _ hinj, ← hsy, ← hkx, hB, Subgroup.map_bot]
  have hC' : Nat.card (commHom hS hx).range = Nat.card (commHom hS hy).range := by
    rw [hsx, hsy, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj] at hC
    exact hC
  obtain ⟨c1, c2, c3, c4, c5⟩ := two_involutions (commHom hS hx) (commHom hS hy)
    (commHom_commHom hS hS2 hx hxx) (commHom_commHom hS hS2 hy hyy) hA' hB' hC'
  have hW : commSub x S ⊔ commSub y S =
      ((commHom hS hx).range ⊔ (commHom hS hy).range).map S.subtype := by
    rw [Subgroup.map_sup, hsx, hsy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsx, hsy, ← Subgroup.map_inf_eq _ _ _ hinj, c1, Subgroup.map_bot]
  · rw [hW, hkx, hsx, ← Subgroup.map_inf_eq _ _ _ hinj, c2]
  · have hWS : commSub x S ⊔ commSub y S ≤ S := sup_le (commSub_le hS hx) (commSub_le hS hy)
    refine le_antisymm (Subgroup.closure_mono fun c ⟨e, he, hc⟩ => ⟨e, hWS he, hc⟩) ?_
    intro c hc
    obtain ⟨e, he, rfl⟩ := (mem_commSub hS hx).mp hc
    have h1 : commHom hS hx ⟨e, he⟩ ∈ ((commHom hS hx).range ⊔ (commHom hS hy).range).map
        (commHom hS hx) := by
      rw [c3]; exact ⟨⟨e, he⟩, rfl⟩
    obtain ⟨w, hw, hwe⟩ := h1
    have hwW : (w : Γ) ∈ commSub x S ⊔ commSub y S := by
      rw [hW]; exact Subgroup.mem_map_of_mem S.subtype hw
    have h2 : x * (e : Γ) * x⁻¹ * (e : Γ)⁻¹ = x * (w : Γ) * x⁻¹ * (w : Γ)⁻¹ :=
      (congrArg Subtype.val hwe).symm
    rw [h2]
    exact Subgroup.subset_closure ⟨w, hwW, rfl⟩
  · rw [hW, hkx, hky, ← Subgroup.map_inf_eq _ _ _ hinj, ← Subgroup.map_sup, c4, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [hW, hkx, hky, ← Subgroup.map_inf_eq _ _ _ hinj, ← Subgroup.map_inf_eq _ _ _ hinj, c5,
      Subgroup.map_bot]

end Decomposition

end CFSG.Quasithin.F9Lin
