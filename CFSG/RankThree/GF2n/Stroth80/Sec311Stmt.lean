module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth311aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B →
    hc.CN t = ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t), conjSubgroup h (LB M Q B) ⊓ hc.CN t

theorem exists_centLB (hc : Ctx M Q Z B) (t : G) :
    ∃ T : Subgroup G, ∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q := by
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  refine ⟨{ carrier := {x | x ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(LB M Q B).mul_mem hx hy, fun r hr => ?_⟩
    have e : ⁅r, x * y⁆ = ⁅r, x⁆ * (x * ⁅r, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem (hx' r hr) (hQn x (hc.LB_le_M hx) _ (hy' r hr))
  · refine ⟨(LB M Q B).one_mem, fun r _ => ?_⟩
    simp [commutatorElement_def]
  · rintro x ⟨hx, hx'⟩
    refine ⟨(LB M Q B).inv_mem hx, fun r hr => ?_⟩
    have e : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hQn x⁻¹ (M.inv_mem (hc.LB_le_M hx)) _ (Q.inv_mem (hx' r hr))
    simpa using this

@[expose] def Stroth311bCardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B → ¬ SLNat hc t →
    ∀ T : Subgroup G, (∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q) →
      Nat.card T ≤ Nat.card Q * Nat.card Z

@[expose] def Stroth311bCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B → ¬ SLNat hc t →
    ∀ T : Subgroup G, (∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q) →
      ⁅hc.CN t, hc.CN t⁆ ≤ T

end CFSG.RankThree.GF2n.Stroth80
