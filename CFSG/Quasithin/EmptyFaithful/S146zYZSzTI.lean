module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.S146zY.SzNoFive

theorem card_add_one_le_index_of_ti {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hTI : ∀ g : G, g ∉ P → ∀ x ∈ P, g⁻¹ * x * g ∈ P → x = 1) (hP : P ≠ ⊤) :
    Nat.card P + 1 ≤ P.index := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ P := by
    by_contra h
    exact hP ((Subgroup.eq_top_iff' P).2 fun x => by_contra fun hx => h ⟨x, hx⟩)
  let f : Option P → G ⧸ P := fun o =>
    o.elim (QuotientGroup.mk 1) (fun u => QuotientGroup.mk ((u : G) * g))
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with _ | u <;> rcases b with _ | u'
    · rfl
    · exfalso
      have hab' : (QuotientGroup.mk (1 : G) : G ⧸ P) = QuotientGroup.mk ((u' : G) * g) := hab
      have h1 : (1 : G)⁻¹ * ((u' : G) * g) ∈ P := QuotientGroup.eq.1 hab'
      rw [inv_one, one_mul] at h1
      exact hg ((Subgroup.mul_mem_cancel_left P u'.2).1 h1)
    · exfalso
      have hab' : (QuotientGroup.mk ((u : G) * g) : G ⧸ P) = QuotientGroup.mk (1 : G) := hab
      have h1 : ((u : G) * g)⁻¹ * 1 ∈ P := QuotientGroup.eq.1 hab'
      rw [mul_one] at h1
      have h2 : (u : G) * g ∈ P := by simpa using P.inv_mem h1
      exact hg ((Subgroup.mul_mem_cancel_left P u.2).1 h2)
    · have hab' : (QuotientGroup.mk ((u : G) * g) : G ⧸ P) = QuotientGroup.mk ((u' : G) * g) := hab
      have h1 : ((u : G) * g)⁻¹ * ((u' : G) * g) ∈ P := QuotientGroup.eq.1 hab'
      have hx : (u : G)⁻¹ * u' ∈ P := P.mul_mem (P.inv_mem u.2) u'.2
      have h2 : g⁻¹ * ((u : G)⁻¹ * u') * g ∈ P := by
        have : ((u : G) * g)⁻¹ * ((u' : G) * g) = g⁻¹ * ((u : G)⁻¹ * u') * g := by group
        rwa [this] at h1
      have h3 := hTI g hg _ hx h2
      rw [inv_mul_eq_one] at h3
      exact congrArg some (Subtype.ext h3)
  have h := Nat.card_le_card_of_injective f hf
  have hopt : Nat.card (Option P) = Nat.card P + 1 := by
    have := Fintype.ofFinite P
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  rwa [hopt, ← Subgroup.index] at h

end CFSG.Quasithin.S146zY.SzNoFive
