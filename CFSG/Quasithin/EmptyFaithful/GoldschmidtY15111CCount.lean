module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Cop

public section

namespace CFSG.Quasithin

namespace Y15111

variable {J : Type} [Group J]

theorem card_sup_mul_card_inf {A B : Subgroup J} (h : A ≤ Subgroup.normalizer (B : Set J)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_eq h] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_inf_le_of_mulEquiv {S : Type*} [Group S] [Finite S] {B V : Subgroup J}
    (e : ↥B ≃* S) (hV : ∀ v ∈ V, v * v = 1) {k : ℕ}
    (hS : Nat.card {s : S // s * s = 1} ≤ k) : Nat.card ↥(V ⊓ B) ≤ k := by
  refine le_trans ?_ hS
  have key : ∀ v : ↥(V ⊓ B), e ⟨v, (Subgroup.mem_inf.mp v.2).2⟩ *
      e ⟨v, (Subgroup.mem_inf.mp v.2).2⟩ = 1 := by
    intro v
    rw [← map_mul]
    have h1 : (⟨v, (Subgroup.mem_inf.mp v.2).2⟩ : ↥B) * ⟨v, (Subgroup.mem_inf.mp v.2).2⟩ = 1 :=
      Subtype.ext (hV v (Subgroup.mem_inf.mp v.2).1)
    rw [h1, map_one]
  refine Nat.card_le_card_of_injective
    (fun v => (⟨e ⟨v, (Subgroup.mem_inf.mp v.2).2⟩, key v⟩ : {s : S // s * s = 1})) ?_
  intro v w h
  have := e.injective (congrArg Subtype.val h)
  exact Subtype.ext (Subtype.mk.inj this)

def conjEndSet (S : Set J) (c : J) (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) : Function.End ↥S :=
  fun s => ⟨c * s * c⁻¹, hS s s.2⟩

theorem exists_fixed_of_card_mod_three {S : Set J} [Finite S] {c : J}
    (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hc3 : c ^ 3 = 1) (hmod : Nat.card S % 3 ≠ 0) :
    ∃ s ∈ S, c * s * c⁻¹ = s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype S := Fintype.ofFinite S
  have hc3' : c * c * c = 1 := by rw [← hc3, pow_succ, pow_succ, pow_one]
  let f : Function.End ↥S := conjEndSet S c hS
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext w
    apply Subtype.ext
    show c * (c * (c * (w : J) * c⁻¹) * c⁻¹) * c⁻¹ = w
    have : c * (c * (c * (w : J) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * w * (c * c * c)⁻¹ := by
      group
    rw [this, hc3']
    simp
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have key' : Nat.card S ≡ Nat.card (Function.fixedPoints f) [MOD 3] := by
    convert key using 2
    · exact Nat.card_eq_fintype_card
    · rw [Nat.card_eq_fintype_card]
      congr
      funext a
      exact Subsingleton.elim _ _
  by_contra hne
  push Not at hne
  have h0 : Nat.card (Function.fixedPoints f) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨s, hs⟩ => ?_⟩
    exact hne s s.2 (congrArg Subtype.val hs)
  rw [h0] at key'
  exact hmod (by simpa [Nat.ModEq] using key')

end Y15111

end CFSG.Quasithin
