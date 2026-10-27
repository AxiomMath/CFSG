module

public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions.QZ

theorem O4PairData.mul_not_mem {Y : Type} [Group Y] {Θ : Set Y} (h : O4PairData Y Θ)
    {x y : Y} (hx : x ∈ Θ) (hy : y ∈ Θ) : x * y ∉ Θ := by
  obtain ⟨e, he⟩ := h
  intro hxy
  have hxe : e x ∈ class65 := by rw [← he]; exact ⟨x, hx, rfl⟩
  have hye : e y ∈ class65 := by rw [← he]; exact ⟨y, hy, rfl⟩
  have hxye : e (x * y) ∈ class65 := by rw [← he]; exact ⟨x * y, hxy, rfl⟩
  rw [map_mul] at hxye
  exact class65_no_sq hxe hye hxye

end CFSG.OddTranspositions.QZ
