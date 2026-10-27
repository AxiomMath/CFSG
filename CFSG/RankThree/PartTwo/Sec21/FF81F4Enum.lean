module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4EnumDefs
public import CFSG.RankThree.PartOne.SEITZX.F4Two
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.RankThree.PartTwo.Sec4.Item434F42

theorem card_two_cases {K : Type} [Field K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  obtain ⟨a, b, hab, h⟩ := Nat.card_eq_two_iff.1 hK
  have hz : (0 : K) ∈ ({a, b} : Set K) := by rw [h]; trivial
  have ho : (1 : K) ∈ ({a, b} : Set K) := by rw [h]; trivial
  have hc : c ∈ ({a, b} : Set K) := by rw [h]; trivial
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ho hc
  rcases hc with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases ho with h1 | h1 <;> aesop

section Letters

open CFSG.RankThree.PartOne.SEITZX (letterOfCode yElement_one_eq)

variable (K : Type) [Field K] [CharP K 2]

noncomputable def gL (l : ℕ) : adjointGroup ReeTag.F4.tag K := (letterOfCode l).elt K

theorem letterGB_size : letterGB.size = 8 := by simp [letterGB]

variable {K}

theorem gL_bits : ∀ l < letterGB.size, HasBits K (gL K l) letterGB[l]! := by
  intro l hl
  rw [letterGB_size] at hl
  have : letterGB[l]! = (letterOfCode l).bits := by
    have h1 : l < letterGB.size := by rw [letterGB_size]; exact hl
    rw [getElem!_pos letterGB l h1]
    simp [letterGB, hl]
  rw [this]
  exact Letter.hasBits _

theorem gL_gen (hK : Nat.card K = 2) :
    Subgroup.closure (gL K '' {k | k < letterGB.size}) = ⊤ := by
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · rcases card_two_cases hK c with rfl | rfl
    · rw [xElement_zero]; exact Subgroup.one_mem _
    · have hi : i.val < 4 := i.2
      have hlt : i.val < letterGB.size := by rw [letterGB_size]; omega
      have hidx : (idx ⟨i.val, hi⟩ : Fin ReeTag.F4.tag.rank) = i := Fin.ext rfl
      refine Subgroup.subset_closure ⟨i.val, hlt, ?_⟩
      simp only [gL, letterOfCode, hi, dite_true, Letter.elt, hidx]
  · rcases card_two_cases hK c with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact Subgroup.one_mem _
    · have hi : i.val < 4 := i.2
      have hidx : (idx ⟨i.val, hi⟩ : Fin ReeTag.F4.tag.rank) = i := Fin.ext rfl
      rw [yElement_one_eq]
      have hx : xElement (τ := ReeTag.F4.tag) (K := K) i 1 ∈
          Subgroup.closure (gL K '' {k | k < letterGB.size}) := by
        have hlt : i.val < letterGB.size := by rw [letterGB_size]; omega
        refine Subgroup.subset_closure ⟨i.val, hlt, ?_⟩
        simp only [gL, letterOfCode, hi, dite_true, Letter.elt, hidx]
      have hn : weylElement ReeTag.F4.tag K i ∈
          Subgroup.closure (gL K '' {k | k < letterGB.size}) := by
        have hlt : i.val + 4 < letterGB.size := by rw [letterGB_size]; omega
        refine Subgroup.subset_closure ⟨i.val + 4, hlt, ?_⟩
        have h4 : ¬ (i.val + 4 < 4) := by omega
        simp only [gL, letterOfCode, h4, dite_false, Letter.elt]
        have h5 : (idx (⟨(i.val + 4 - 4) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)) = i :=
          Fin.ext (by show (i.val + 4 - 4) % 4 = i.val; omega)
        rw [h5]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn) hx

end Letters

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
