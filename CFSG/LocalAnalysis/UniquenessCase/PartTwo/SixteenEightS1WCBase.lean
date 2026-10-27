module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.k_eq_one_of_three_mem (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig) :
    D.k = 1 :=
  Data.k_eq_one_of_three_mem D h.std.hSg (h.std.h1219 V₀ V h.setting.hyp16.hyp125) h3

theorem S16gRowCtx.isStronglyPEmbedded_three (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
  h.std.hSg.sig1_sp 3 ((h.std.h1219 V₀ V h.setting.hyp16.hyp125) ▸ h3)

theorem S16gRowCtx.false_of_permuting_three (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hbig : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y) : False := by
  have hk := h.k_eq_one_of_three_mem h3
  have hm' : MBarGT D.M V₀ V (D.k + 1) := by rw [hk]; exact hm
  have hP11 : F11.InP11 D Y :=
    inP11_of_strongly Nat.prime_three (by norm_num) (h.isStronglyPEmbedded_three h3) hYM hY3
      hYexp hYnc hperm
  have hPStar : InPStar D V₀ Y := by
    rcases hbig with hne | hbig
    · exact (inPStar_iff_of_ne_bot hne Y).2 hP11
    · exact ⟨hP11, fun _ => ⟨3, Nat.prime_three, hY3, Or.inl (by norm_num; exact hbig)⟩⟩
  exact twelve_twelve D h.std.h63 h.std.h126 h.std.h1211 h.std.h111 h.std.h6161ii
    h.setting.hyp16.hyp125 hm' Y hPStar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
