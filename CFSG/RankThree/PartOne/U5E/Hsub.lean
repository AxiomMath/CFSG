module

public import CFSG.RankThree.PartOne.U5K.Kf.Comb

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG.RankThree.PartOne.U5K.Kf

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem card_VM : Nat.card (VM p) = p ^ 5 := by
  have : Nat.card (Fin 5 → ZMod p) = p ^ 5 := by
    rw [Nat.card_fun, Nat.card_zmod]
    simp
  exact this

theorem diffHom_surjective {i j : Fin 5} (hij : i ≠ j) :
    Function.Surjective (diffHom (p := p) i j) := by
  intro c
  refine ⟨Multiplicative.ofAdd (fun k => if k = i then Multiplicative.toAdd c else 0), ?_⟩
  apply Multiplicative.toAdd.injective
  simp [diffHom, hij.symm]

theorem card_Hsub {i j : Fin 5} (hij : i ≠ j) : Nat.card (Hsub p i j) = p ^ 4 := by
  have h1 := Subgroup.card_ker_mul_card_range (diffHom (p := p) i j)
  have h2 : Nat.card (diffHom (p := p) i j).range = p := by
    rw [MonoidHom.range_eq_top.2 (diffHom_surjective hij), Subgroup.card_top]
    simp
  rw [h2, card_VM] at h1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h3 : Nat.card (Hsub p i j) * p = p ^ 4 * p := by
    unfold Hsub
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hp h3

theorem Hsub_comm (i j : Fin 5) : Hsub p i j = Hsub p j i := by
  ext a
  rw [mem_Hsub, mem_Hsub]
  exact eq_comm

end CFSG.RankThree.PartOne.U5E
