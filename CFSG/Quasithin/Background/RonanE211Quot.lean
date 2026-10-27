module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.Quasithin.RonanE211

theorem commutator_mem_of_index_two {Q : Type} [Group Q] (Λ J₀ : Subgroup Q) [Λ.Normal]
    (hJc : J₀ ≤ Subgroup.center Q) {q : Q} (hq : ∀ x : Q, x ∈ Λ ⊔ J₀ ∨ q⁻¹ * x ∈ Λ ⊔ J₀) :
    ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ Λ := by
  have hcent : ∀ j : Q, j ∈ J₀ → ∀ g : Q ⧸ Λ, (j : Q ⧸ Λ) * g = g * (j : Q ⧸ Λ) := by
    intro j hj g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← Subgroup.mem_center_iff.mp (hJc hj) z]
  have hform : ∀ g : Q ⧸ Λ, (∃ j : Q, j ∈ J₀ ∧ g = (j : Q ⧸ Λ)) ∨
      (∃ j : Q, j ∈ J₀ ∧ g = (q : Q ⧸ Λ) * (j : Q ⧸ Λ)) := by
    intro g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    rcases hq z with h | h
    · obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h
      refine Or.inl ⟨j, hj, ?_⟩
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
    · obtain ⟨l, hl, j, hj, hlj⟩ := Subgroup.mem_sup_of_normal_left.mp h
      refine Or.inr ⟨j, hj, ?_⟩
      have hz : z = q * (l * j) := by
        rw [hlj, mul_inv_cancel_left]
      rw [hz, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  have hcomm' : ∀ a b : Q ⧸ Λ, a * b = b * a := by
    intro a b
    rcases hform a with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;>
      rcases hform b with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact hcent j hj _
    · exact hcent j hj _
    · exact (hcent k hk _).symm
    · have hJq : Commute (j : Q ⧸ Λ) (q : Q ⧸ Λ) := hcent j hj _
      have hJk : Commute (j : Q ⧸ Λ) (k : Q ⧸ Λ) := hcent j hj _
      have hqK : Commute (q : Q ⧸ Λ) (k : Q ⧸ Λ) := (hcent k hk _).symm
      exact Commute.mul_left (Commute.mul_right (Commute.refl _) hqK)
        (Commute.mul_right hJq hJk)
  intro x y
  refine (QuotientGroup.eq_one_iff _).mp ?_
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm' (x : Q ⧸ Λ) (y : Q ⧸ Λ)]
  simp

theorem sq_mem_of_gen {Q : Type} [Group Q] (Λ : Subgroup Q) [Λ.Normal]
    (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ Λ)
    (hgen : Subgroup.closure {x : Q | x * x = 1} = ⊤) : ∀ y : Q, y * y ∈ Λ := by
  let K : Subgroup Q :=
    { carrier := {y : Q | y * y ∈ Λ}
      one_mem' := by
        show (1 : Q) * 1 ∈ Λ
        rw [mul_one]
        exact Λ.one_mem
      mul_mem' := by
        intro a b ha hb
        have ha' : a * a ∈ Λ := ha
        have hb' : b * b ∈ Λ := hb
        have hconj : b * (a * a) * b⁻¹ ∈ Λ := ‹Λ.Normal›.conj_mem (a * a) ha' b
        have hid : a * b * (a * b) =
            (a * b * a⁻¹ * b⁻¹) * (b * (a * a) * b⁻¹) * (b * b) := by
          simp only [mul_assoc, inv_mul_cancel_left]
        show a * b * (a * b) ∈ Λ
        rw [hid]
        exact Λ.mul_mem (Λ.mul_mem (hcomm a b) hconj) hb'
      inv_mem' := by
        intro a ha
        have ha' : a * a ∈ Λ := ha
        show a⁻¹ * a⁻¹ ∈ Λ
        rw [← mul_inv_rev]
        exact Λ.inv_mem ha' }
  have hS : {x : Q | x * x = 1} ⊆ (K : Set Q) := by
    intro x hx
    have hx' : x * x = 1 := hx
    show x * x ∈ Λ
    rw [hx']
    exact Λ.one_mem
  have hK : (⊤ : Subgroup Q) ≤ K := by
    rw [← hgen]
    exact (Subgroup.closure_le K).mpr hS
  intro y
  exact hK (Subgroup.mem_top y)

end CFSG.Quasithin.RonanE211
