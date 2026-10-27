module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

theorem ggK1C_core_valid {p nf r : ℕ} {K : Type} [Field K] {x : ↥(StatedSp r K)}
    {m : List ℕ} (h2r : 2 ≤ r) (hm : GGK1CMultOf p nf (ggMultOrd p nf) r K x m) :
    GGMultValidCl ⟨.C, r, nf⟩ p (ggMultDatumC p nf (ggMultOrd p nf) m) := by
  have hd : ggMultOrd p nf ≠ 0 := by
    rcases hm.blocks_eq with ⟨h1, -⟩ | ⟨h2, -⟩
    · rw [h1]; exact one_ne_zero
    · rw [h2]; exact two_ne_zero
  refine ⟨.C r, false, nf, by simp [ggKacTypeClOfLabel, h2r], ?_⟩
  exact (mem_ggMultTableCl_C hd).mpr ⟨m, hm.length_eq, hm.sum_eq, rfl⟩

end CFSG.StandardType

end
