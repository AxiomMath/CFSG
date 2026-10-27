module

public import CFSG.Quasithin.Vol2.Ch10SecV1SA

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]

structure SumTwo (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)) (V W₀ W₁ : Subgroup H) where
  c₀ : NatCoord φ W₀
  c₁ : NatCoord φ W₁
  le₀ : W₀ ≤ V
  le₁ : W₁ ≤ V
  sup : W₀ ⊔ W₁ = V
  inf : W₀ ⊓ W₁ = ⊥
  comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x

namespace SumTwo

variable {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {V W₀ W₁ : Subgroup H}

theorem decomp (S : SumTwo φ V W₀ W₁) {v : H} (hv : v ∈ V) :
    ∃ a ∈ W₀, ∃ b ∈ W₁, a * b = v := by
  have hN : W₁ ≤ Subgroup.normalizer (W₀ : Set H) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rwa [S.comm b (S.le₁ hb) x (S.le₀ hx), mul_inv_cancel_right]
    · intro hx
      have hxV : x ∈ V := by
        have e : x = b⁻¹ * (b * x * b⁻¹) * b := by group
        rw [e]
        exact V.mul_mem (V.mul_mem (V.inv_mem (S.le₁ hb)) (S.le₀ hx)) (S.le₁ hb)
      rwa [S.comm b (S.le₁ hb) x hxV, mul_inv_cancel_right] at hx
  have hv' : v ∈ ((W₀ ⊔ W₁ : Subgroup H) : Set H) := by
    rw [S.sup]
    exact hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W₀ W₁ hN] at hv'
  obtain ⟨a, ha, b, hb, hab⟩ := hv'
  exact ⟨a, ha, b, hb, hab⟩

theorem eq_one_of_mem (S : SumTwo φ V W₀ W₁) {x : H} (h₀ : x ∈ W₀) (h₁ : x ∈ W₁) : x = 1 := by
  have : x ∈ W₀ ⊓ W₁ := ⟨h₀, h₁⟩
  rwa [S.inf, Subgroup.mem_bot] at this

theorem card_eq (S : SumTwo φ V W₀ W₁) : Nat.card W₀ = Nat.card W₁ :=
  (Nat.card_congr S.c₀.θ.toEquiv).trans (Nat.card_congr S.c₁.θ.toEquiv).symm

@[expose] def gr (S : SumTwo φ V W₀ W₁) (a : K) : ↥W₀ →* ↥W₁ where
  toFun w := S.c₁.θ.symm (Multiplicative.ofAdd (a • Multiplicative.toAdd (S.c₀.θ w)))
  map_one' := by simp
  map_mul' w w' := by simp [toAdd_mul, smul_add, ofAdd_add]

theorem gr_apply (S : SumTwo φ V W₀ W₁) (a : K) (w : ↥W₀) :
    S.c₁.θ (S.gr a w) = Multiplicative.ofAdd (a • Multiplicative.toAdd (S.c₀.θ w)) := by
  simp [gr]

@[expose] def grHom (S : SumTwo φ V W₀ W₁) (a : K) : ↥W₀ →* H where
  toFun w := (w : H) * (S.gr a w : H)
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul, Subgroup.coe_mul]
    have hc := S.comm _ (S.le₁ (S.gr a w).2) _ (S.le₀ w'.2)
    calc (w : H) * w' * ((S.gr a w : H) * S.gr a w') = w * ((w' : H) * S.gr a w) * S.gr a w' := by
          group
      _ = w * ((S.gr a w : H) * w') * S.gr a w' := by rw [hc]
      _ = (w : H) * S.gr a w * (w' * S.gr a w') := by group

@[expose] def graph (S : SumTwo φ V W₀ W₁) (a : K) : Subgroup H := (S.grHom a).range

theorem grHom_injective (S : SumTwo φ V W₀ W₁) (a : K) : Function.Injective (S.grHom a) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : (w : H) = (S.gr a w : H)⁻¹ := eq_inv_of_mul_eq_one_left hw
  have h1 : (w : H) ∈ W₁ := h ▸ W₁.inv_mem (S.gr a w).2
  exact Subtype.ext (S.eq_one_of_mem w.2 h1)

theorem card_graph (S : SumTwo φ V W₀ W₁) (a : K) : Nat.card (S.graph a) = Nat.card W₀ :=
  (Nat.card_congr (MonoidHom.ofInjective (S.grHom_injective a)).toEquiv).symm

theorem graph_le (S : SumTwo φ V W₀ W₁) (a : K) : S.graph a ≤ V := by
  rintro _ ⟨w, rfl⟩
  exact V.mul_mem (S.le₀ w.2) (S.le₁ (S.gr a w).2)

theorem eq_gr_of_mem (S : SumTwo φ V W₀ W₁) {a : K} (w : ↥W₀) {b : H} (hb : b ∈ W₁)
    (h : (w : H) * b ∈ S.graph a) : b = S.gr a w := by
  obtain ⟨w', hw'⟩ := h
  have e : (w' : H) * S.gr a w' = w * b := hw'
  have e1 : (w : H)⁻¹ * w' = b * (S.gr a w' : H)⁻¹ := by
    calc (w : H)⁻¹ * w' = (w : H)⁻¹ * (w' * S.gr a w') * (S.gr a w' : H)⁻¹ := by group
      _ = b * (S.gr a w' : H)⁻¹ := by rw [e]; group
  have h1 : (w : H)⁻¹ * w' = 1 :=
    S.eq_one_of_mem (W₀.mul_mem (W₀.inv_mem w.2) w'.2) (e1 ▸ W₁.mul_mem hb (W₁.inv_mem
      (S.gr a w').2))
  have hww : w' = w := Subtype.ext (by
    have := congrArg (fun x => (w : H) * x) h1
    simpa using this)
  subst hww
  have : (w' : H) * S.gr a w' = w' * b := e
  exact (mul_left_cancel this).symm

end SumTwo

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
