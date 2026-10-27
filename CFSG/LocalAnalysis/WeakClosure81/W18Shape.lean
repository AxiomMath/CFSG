module

public import CFSG.LocalAnalysis.WeakClosure81.W18Four
public import CFSG.LocalAnalysis.WeakClosure81.W18Solv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem exists_shape512 (h172 : W3Thm172Weak G) (h5_12 : Asch5_12) (c : MinCex183 D V₀ V H i)
    (h1 : ¬ Concl181 D V₀ V H) :
    IsSolvable ↥(relPPrimeCore 3 H) ∧ relPPrimeCore 3 H ≤ H ⊓ D.M ∧ Shape512 H := by
  obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := c.hyps_5_13 h1
  obtain ⟨-, hcase⟩ := h5_12 G H D.T hK hT hTlt h3 hno hne
  rcases hcase with hsolv | ⟨hsolv, hle, hshape⟩
  · exact absurd hsolv (c.not_isSolvable h172)
  · exact ⟨hsolv, hle.trans (c.lGen_one_le_inf h1), hshape⟩

theorem exists_component182 (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) :
    ∃ L : Subgroup G, IsComponentModN (OInf H) H L ∧ L ⊔ D.T = H ∧ Shape54 H D.T L := by
  obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := c.hyps_5_11 h2
  rcases h5_4 G H D.T hK hT hTlt hno with h | ⟨p, hpp, hp2, hrk, hrk'⟩ | ⟨-, hsolv | hL⟩
  · exact absurd h hne
  · rcases hp p hpp hp2 with h3 | h1
    · exact absurd (lt_of_lt_of_le hrk
        (CFSG.SectionRank.pRank_mono hpp.one_lt (perfectCore_le H))) (not_lt.mpr h3)
    · exact absurd hrk' (not_lt.mpr h1)
  · exact absurd hsolv (c.not_isSolvable h172)
  · exact hL

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
