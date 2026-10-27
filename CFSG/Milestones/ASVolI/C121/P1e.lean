module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Milestones.ASVolI.C1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem burnsideC121_sl2_irreducible {F : Type} [Field F] (A : Subgroup (Multiplicative (Fin 2 → F)))
    (hA : ∀ (g : SL(2, F)) (x : Multiplicative (Fin 2 → F)), x ∈ A →
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x)) ∈ A)
    (hne : A ≠ ⊥) : A = ⊤ := by
  have hsub : ∀ (g : SL(2, F)) (x : Multiplicative (Fin 2 → F)), x ∈ A →
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x) -
        Multiplicative.toAdd x) ∈ A := by
    intro g x hx
    rw [ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv]
    exact A.mul_mem (hA g x hx) (A.inv_mem hx)
  have hline1 : ∀ x ∈ A, Multiplicative.toAdd x 1 ≠ 0 → ∀ t : F,
      Multiplicative.ofAdd ![t, 0] ∈ A := by
    intro x hx h1 t
    have := hsub (CFSG.Quasithin.SL2Model.e12 (t / Multiplicative.toAdd x 1)) x hx
    convert this using 2
    rw [CFSG.Quasithin.SL2Model.e12_coe]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail, div_mul_cancel₀ _ h1]
  have hline0 : ∀ x ∈ A, Multiplicative.toAdd x 0 ≠ 0 → ∀ t : F,
      Multiplicative.ofAdd ![0, t] ∈ A := by
    intro x hx h0 t
    have := hsub (CFSG.Quasithin.SL2Model.e21 (t / Multiplicative.toAdd x 0)) x hx
    convert this using 2
    rw [CFSG.Quasithin.SL2Model.e21_coe]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail, div_mul_cancel₀ _ h0]
  obtain ⟨x, hxA, hx1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hne
  have hboth : (∀ t : F, Multiplicative.ofAdd ![t, 0] ∈ A) ∧
      (∀ t : F, Multiplicative.ofAdd ![0, t] ∈ A) := by
    by_cases h1 : Multiplicative.toAdd (x : Multiplicative (Fin 2 → F)) 1 ≠ 0
    · have hl1 := hline1 x hxA h1
      refine ⟨hl1, ?_⟩
      intro t
      by_cases ht : t = 0
      · subst ht
        have : Multiplicative.ofAdd ![(0 : F), 0] = 1 := by
          apply Multiplicative.toAdd.injective
          funext i
          fin_cases i <;> rfl
        rw [this]
        exact A.one_mem
      · exact hline0 _ (hl1 t) (by simpa using ht) t
    · push_neg at h1
      have h0 : Multiplicative.toAdd (x : Multiplicative (Fin 2 → F)) 0 ≠ 0 := by
        intro h0
        apply hx1
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have hl0 := hline0 x hxA h0
      refine ⟨?_, hl0⟩
      intro t
      by_cases ht : t = 0
      · subst ht
        have : Multiplicative.ofAdd ![(0 : F), 0] = 1 := by
          apply Multiplicative.toAdd.injective
          funext i
          fin_cases i <;> rfl
        rw [this]
        exact A.one_mem
      · exact hline1 _ (hl0 t) (by simpa using ht) t
  rw [eq_top_iff]
  intro y _
  have hy : y = Multiplicative.ofAdd ![Multiplicative.toAdd y 0, 0] *
      Multiplicative.ofAdd ![0, Multiplicative.toAdd y 1] := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  rw [hy]
  exact A.mul_mem (hboth.1 _) (hboth.2 _)

end CFSG.ASVolI
