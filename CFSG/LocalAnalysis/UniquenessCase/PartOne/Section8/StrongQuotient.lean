module

public import CFSG.Open.GLBDefs
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open

theorem isStronglyPEmbedded_of_glbStronglyEmbedded {H : Type*} [Group H] {p : ℕ}
    {Y : Subgroup H} (h : GLBStronglyEmbedded p Y) : IsStronglyPEmbedded p Y := by
  obtain ⟨hne, hdvd, hint⟩ := h
  refine ⟨hne, hdvd, fun g hg => ?_⟩
  have hg' : g⁻¹ ∉ Y := fun hmem => hg (by simpa using Y.inv_mem hmem)
  simpa [GLBConj] using hint g⁻¹ hg'

end CFSG.RankThree.PartOne

