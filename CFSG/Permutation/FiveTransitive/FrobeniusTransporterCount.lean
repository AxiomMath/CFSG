module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.FrobeniusTransporterCount

open MulAction
open scoped BigOperators

variable {G T : Type*} [Group G] [MulAction G T]

@[expose] def admissible (f : T → T) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    SubMulAction G T where
  carrier := {x | ∃ g : G, g • x = f x}
  smul_mem' a x hx := by
    obtain ⟨g, hg⟩ := hx
    refine ⟨a * g * a⁻¹, ?_⟩
    simp only [mul_smul, inv_smul_smul, hg, hf]

private noncomputable def transporterFixedEquiv
    (f : T → T) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    (Σ g : G, {x : T // g • x = f x}) ≃
      (Σ g : G, fixedBy (admissible f hf) g) := by
  classical
  let E := admissible f hf
  let c (x : E) : G := Classical.choose x.property
  have hc (x : E) : c x • x.val = f x.val := Classical.choose_spec x.property
  refine
    { toFun := fun p => ⟨(c ⟨p.2.val, p.1, p.2.property⟩)⁻¹ * p.1,
        ⟨⟨p.2.val, p.1, p.2.property⟩, ?_⟩⟩
      invFun := fun p => ⟨c p.2.val * p.1, ⟨p.2.val.val, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    change ((c ⟨p.2.val, p.1, p.2.property⟩)⁻¹ * p.1) • p.2.val = p.2.val
    rw [mul_smul]
    exact (congrArg (fun x => (c ⟨p.2.val,p.1,p.2.property⟩)⁻¹ • x)
      (p.2.property.trans (hc ⟨p.2.val,p.1,p.2.property⟩).symm)).trans
        (inv_smul_smul _ _)
  · have hp : p.1 • p.2.val.val = p.2.val.val := congrArg Subtype.val p.2.property
    rw [mul_smul, hp, hc]
  · intro p
    apply Sigma.ext
    · simp only [mul_inv_cancel_left]
    · apply (Subtype.heq_iff_coe_eq (by intro x; simp only [mul_inv_cancel_left])).mpr
      rfl
  · intro p
    have he : (⟨p.2.val.val, c p.2.val * p.1, by
        have hp : p.1 • p.2.val.val = p.2.val.val := congrArg Subtype.val p.2.property
        rw [mul_smul, hp, hc]⟩ : E) = p.2.val := rfl
    apply Sigma.ext
    · simp only [he, inv_mul_cancel_left]
    · apply (Subtype.heq_iff_coe_eq (by intro x; simp only [he, inv_mul_cancel_left])).mpr
      rfl

theorem sum_card_transporter_eq
    [Fintype G] [Fintype T]
    (f : T → T) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    (∑ g : G, Nat.card {x : T // g • x = f x}) =
      Nat.card G * Nat.card (orbitRel.Quotient G (admissible f hf)) := by
  classical
  let _ : Fintype (admissible f hf) := Fintype.ofFinite _
  have he := Fintype.card_congr (transporterFixedEquiv f hf)
  simp only [Fintype.card_sigma] at he
  simp only [Nat.card_eq_fintype_card]
  rw [he, sum_card_fixedBy_eq_card_orbits_mul_card_group, Nat.mul_comm]

theorem sum_card_transporter_eq_card_group
    [Fintype G] [Fintype T] [Nonempty T] [IsPretransitive G T]
    (f : T → T) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    (∑ g : G, Nat.card {x : T // g • x = f x}) = Nat.card G := by
  classical
  let E := admissible f hf
  have hmem (x : T) : x ∈ E := IsPretransitive.exists_smul_eq x (f x)
  let _ : Nonempty E := ⟨⟨Classical.choice inferInstance, hmem _⟩⟩
  let _ : IsPretransitive G E := ⟨fun x y => by
    obtain ⟨g,hg⟩ := IsPretransitive.exists_smul_eq (M := G) x.val y.val
    exact ⟨g, Subtype.ext hg⟩⟩
  let _ : Unique (orbitRel.Quotient G E) := Classical.choice
    ((pretransitive_iff_unique_quotient_of_nonempty G E).mp inferInstance)
  rw [sum_card_transporter_eq f hf]
  change Nat.card G * Nat.card (orbitRel.Quotient G E) = Nat.card G
  simp

end FiveTransitive.FrobeniusTransporterCount

end CFSG
