module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.KGC31

section Coset

variable {G : Type*} [Group G]

theorem card_conj_eq {K : Subgroup G} (b r : G) (hr : r ∈ K) (P : G → Prop) :
    Nat.card {g : K // P g ∧ (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} =
      Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)} := by
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨r⁻¹ * g, K.mul_mem (K.inv_mem hr) g.1.2⟩, ?_, ?_⟩
      invFun := fun c => ⟨⟨r * c, K.mul_mem hr c.1.2⟩, c.2.2, ?_⟩
      left_inv := fun g => by ext; simp
      right_inv := fun c => by ext; simp }
  · have h := g.2.2
    calc r⁻¹ * (g : G) * b = r⁻¹ * ((g : G) * b * (g : G)⁻¹) * g := by group
      _ = r⁻¹ * (r * b * r⁻¹) * g := by rw [h]
      _ = b * (r⁻¹ * g) := by group
  · simpa using g.2.1
  · have h := c.2.1
    calc r * (c : G) * b * (r * c)⁻¹ = r * ((c : G) * b) * (c : G)⁻¹ * r⁻¹ := by group
      _ = r * (b * c) * (c : G)⁻¹ * r⁻¹ := by rw [h]
      _ = r * b * r⁻¹ := by group

theorem card_eq_sum_coset {K : Subgroup G} [Finite K] (b : G) (rs : List G) (P : G → Prop)
    (hP : ∀ g ∈ K, P g → ∃ r ∈ rs, g * b * g⁻¹ = r * b * r⁻¹) (hrs : ∀ r ∈ rs, r ∈ K)
    (hd : rs.Pairwise fun r r' => r * b * r⁻¹ ≠ r' * b * r'⁻¹) :
    Nat.card {g : K // P g} =
      (rs.map fun r => Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)}).sum := by
  classical
  have key : ∀ l : List G, (∀ r ∈ l, r ∈ K) →
      l.Pairwise (fun r r' => r * b * r⁻¹ ≠ r' * b * r'⁻¹) →
      Nat.card {g : K // P g ∧ ∃ r ∈ l, (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} =
        (l.map fun r => Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)}).sum := by
    intro l
    induction l with
    | nil =>
      intro _ _
      have : IsEmpty {g : K // P g ∧ ∃ r ∈ ([] : List G), (g : G) * b * (g : G)⁻¹ =
          r * b * r⁻¹} := ⟨fun ⟨_, _, _, hr, _⟩ => by simp at hr⟩
      simp
    | cons r l ih =>
      intro hl hpw
      rw [List.pairwise_cons] at hpw
      have hr : r ∈ K := hl r (by simp)
      have hdis : Disjoint (fun g : K => P g ∧ (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹)
          (fun g : K => P g ∧ ∃ r' ∈ l, (g : G) * b * (g : G)⁻¹ = r' * b * r'⁻¹) := by
        intro f hf1 hf2 g hg
        obtain ⟨-, r', hr', e⟩ := hf2 g hg
        exact hpw.1 r' hr' ((hf1 g hg).2.symm.trans e)
      have h1 : Nat.card {g : K // P g ∧ ∃ r' ∈ r :: l, (g : G) * b * (g : G)⁻¹ =
            r' * b * r'⁻¹} =
          Nat.card {g : K // P g ∧ (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} +
            Nat.card {g : K // P g ∧ ∃ r' ∈ l, (g : G) * b * (g : G)⁻¹ = r' * b * r'⁻¹} := by
        rw [← Nat.card_sum, ← Nat.card_congr (subtypeOrEquiv _ _ hdis)]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
        simp only [List.mem_cons, exists_eq_or_imp]
        tauto
      rw [List.map_cons, List.sum_cons, h1, card_conj_eq b r hr P,
        ih (fun r' h' => hl r' (by simp [h'])) hpw.2]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)).trans (key rs hrs hd)
  exact ⟨fun h => ⟨h, hP g g.2 h⟩, fun h => h.1⟩

end Coset

end CFSG.Quasithin.KGC31

end
