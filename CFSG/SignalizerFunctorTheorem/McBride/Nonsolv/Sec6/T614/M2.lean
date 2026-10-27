module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M1

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem isFunctor_kOf
    (h : Counterexample p A θ) (S : Setting614 p A θ E) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    IsFunctor p B (fun b => kOf (θ b)) := by
  have hBA : B ≤ A := hB.1
  refine ⟨fun a ha ha1 => (kOf_le _).trans (h.isFunctor.le_centralizer a (hBA ha) ha1),
    fun a ha ha1 => (h.isFunctor.coprime a (hBA ha) ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le _)),
    fun a ha ha1 => le_normalizer_kOf_of_le_normalizer
      (hBA.trans (h.isFunctor.normalized a (hBA ha) ha1)),
    fun a ha ha1 b hb hb1 => ?_⟩
  show kOf (θ a) ⊓ Subgroup.centralizer {b} ≤ kOf (θ b)
  have hline : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ Subgroup.zpowers x, y ≠ 1 →
      Subgroup.zpowers x = Subgroup.zpowers y := fun x hx hx1 y hy hy1 =>
    h.line_eq_zpowers (h.zpowers_mem_E1 (hBA hx) hx1) hy hy1
  by_cases hba : b ∈ Subgroup.zpowers a
  · have heq := h.isFunctor.eq_of_zpowers_eq (hBA ha) ha1 (hBA hb) hb1 (hline a ha ha1 b hba hb1)
    rw [heq]
    exact inf_le_left
  · have hab : a ∉ Subgroup.zpowers b := fun hab => hba (by
      rw [← hline b hb hb1 a hab ha1]
      exact Subgroup.mem_zpowers b)
    have h1 := h.kOf_apply_inf_centralizer_eq S hB hEB ha hb ha1 hb1 hba
    have h2 := h.kOf_apply_inf_centralizer_eq S hB hEB hb ha hb1 ha1 hab
    rw [h1, sup_comm, ← h2]
    exact inf_le_left

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
