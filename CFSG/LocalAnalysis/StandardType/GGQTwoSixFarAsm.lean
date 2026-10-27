module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixFar
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixCharts
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixAlign
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGens
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPoint

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {H : Subgroup G}

theorem qTwoSix_far [Finite G] (hK : Nat.card K = 4)
    (B : QTwoCanonBlocks K 5 6 H) (hodd : Odd (Nat.card (Subgroup.center ↥H))) :
    ∀ x ∈ B.blk ({0, 1, 2} : Finset (Fin 6)), ∀ y ∈ B.blk ({3, 4, 5} : Finset (Fin 6)),
      x * y = y * x := by
  obtain ⟨φ₀, h₀⟩ := qTwoSix_fourChart_exists hK B 0 (by norm_num)
  obtain ⟨φ₁', h₁'⟩ := qTwoSix_fourChart_exists hK B 1 (by norm_num)
  obtain ⟨φ₂', h₂'⟩ := qTwoSix_fourChart_exists hK B 2 (by norm_num)
  obtain ⟨φ₁, h₁, a₀₁⟩ := qTwoSix_align hK B (s := 0) (by norm_num) h₀ h₁'
  obtain ⟨φ₂, h₂, a₁₂⟩ := qTwoSix_align hK B (s := 1) (by norm_num) h₁ h₂'
  obtain ⟨g, hrel, hH, hb012, hb345, hb0123, hb1234, hb2345⟩ :=
    qTwoSix_gens hK B h₀ h₁ h₂ a₀₁ a₁₂
  let g' : Fin 18 → ↥H := fun i => ⟨g i, hH i⟩
  have hsub : ∀ w, (H.subtype (evalG g' w) : G) = evalG g w := by
    intro w
    simp only [evalG, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    rintro ⟨i, b⟩ _
    cases b <;> simp [g']
  have hrel' : ∀ w ∈ relsP, evalG g' w = 1 := fun w hw =>
    H.subtype_injective (by rw [hsub, hrel w hw, map_one])
  have hYH : Subgroup.closure (Set.range g) ≤ H :=
    (Subgroup.closure_le H).mpr (by rintro _ ⟨i, rfl⟩; exact hH i)
  have hHY : H ≤ Subgroup.closure (Set.range g) :=
    qTwoSix_hub_gen B _ (fun x hx => hb0123 x hx) (fun x hx => hb1234 x hx)
      (fun x hx => hb2345 x hx)
  have hgen : Subgroup.closure (Set.range g') = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    rw [← Set.range_comp]
    exact le_antisymm ((Subgroup.closure_le H).mpr (by rintro _ ⟨i, rfl⟩; exact hH i)) hHY
  have hcomm := qTwoSixPoint_commute hK g' hrel' hgen (qTwoSix_hub_perfect hK B) hodd
  have key : ∀ a ∈ ([10, 11] : List (Fin 18)), ∀ b ∈ ([16, 17] : List (Fin 18)),
      g a * g b = g b * g a := fun a ha b hb => congrArg Subtype.val (hcomm a ha b hb)
  intro x hx y hy
  have hx' := hb012 x hx
  have hy' := hb345 y hy
  have h1 : ∀ a ∈ ({g 10, g 11} : Set G), Subgroup.closure ({g 16, g 17} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := by
    intro a ha
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have ha' : a = g 10 ∨ a = g 11 := by simpa using ha
    have hb' : b = g 16 ∨ b = g 17 := by simpa using hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
      first | exact (key 10 (by simp) 16 (by simp)).symm | exact (key 10 (by simp) 17 (by simp)).symm |
        exact (key 11 (by simp) 16 (by simp)).symm | exact (key 11 (by simp) 17 (by simp)).symm
  have h2 : Subgroup.closure ({g 10, g 11} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({g 16, g 17} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    have := h1 a ha hz
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have := Subgroup.mem_centralizer_iff.mp (h2 hx') y hy'
  exact this.symm

end CFSG.StandardType.QTwo.SixPoint

end
