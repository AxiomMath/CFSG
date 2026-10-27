module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Hyp154
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_centralizer_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) {w : G}
    (hw : w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L)
    (hw1 : w ≠ 1) : centralizer ({w} : Set G) ≤ D.M := by
  have hV := h.hyp151.isElemAbelian
  have hwV : w ∈ V := c23_wSub_sup_v1Sub_le D h.hyp151.hyp125 hV hw
  have hw2 : ∃ n : ℕ, w ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 w hwV⟩
  exact (centralizer_le_of_uniqueMax D.maxLocal hw1 hw2 (h.unique₁ w hw hw1)).1

theorem c23a_cent_union (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) {x : G}
    (hx : x ∈ D.M) {w : G}
    (hw : w ∈ (wSub V₀ V h.hyp151.isElemAbelian L : Set G) ∪
      (conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x : Set G)) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) ≤ D.M := by
  rcases hw with hw | hw
  · exact c23a_centralizer_le D h (Subgroup.mem_sup_left hw) hw1
  · have hw' : x * w * x⁻¹ ∈ wSub V₀ V h.hyp151.isElemAbelian L := mem_conjSubgroup_iff.1 hw
    have hw1' : x * w * x⁻¹ ≠ 1 := fun h1 => hw1 (by simpa using h1)
    have h1 := c23a_centralizer_le D h (Subgroup.mem_sup_left hw') hw1'
    intro y hy
    have hy' : x * y * x⁻¹ ∈ centralizer ({x * w * x⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      have := hy w rfl
      rw [hz]
      calc x * w * x⁻¹ * (x * y * x⁻¹) = x * (w * y) * x⁻¹ := by group
        _ = x * (y * w) * x⁻¹ := by rw [this]
        _ = x * y * x⁻¹ * (x * w * x⁻¹) := by group
    have h2 : x * y * x⁻¹ ∈ D.M := h1 hy'
    have h3 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [h3]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) h2) hx

theorem c23a_inf_blocks_eq_bot {M V W W' : Subgroup G} (hP : C23APair M V W W')
    {A X : Subgroup G} (hA : ¬ A ≤ M) (hX : ∀ x ∈ X, ∀ a ∈ A, a * x = x * a) :
    X ⊓ W = ⊥ ∧ X ⊓ W' = ⊥ := by
  have key : ∀ B : Subgroup G, (∀ w ∈ B, w ≠ 1 → centralizer ({w} : Set G) ≤ M) →
      X ⊓ B = ⊥ := by
    intro B hB
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    by_contra hw1
    obtain ⟨hwX, hwB⟩ := Subgroup.mem_inf.1 hw
    refine hA fun a ha => hB w hwB hw1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (hX w hwX a ha).symm
  exact ⟨key W fun w hw hw1 => hP.cent w (Or.inl hw) hw1,
    key W' fun w hw hw1 => hP.cent w (Or.inr hw) hw1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
