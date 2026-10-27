module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.H13.AS91Sec8Uniq

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem rank_hyp (h531 : Stmt5_3_1u) (hJ : HypJ4 G z) (hloc : CosetGeomLocal c.G1 c.G2 c.G3)
    {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) :
    ∀ b : G ⧸ c.G1, CInc c.G1 c.G3 b (basePt c.G3) → c.Delta.Adj c.x0 b →
      ∃ j ∈ c.G1 ⊓ c.G3, j • y = b := by
  intro b hb hadj
  obtain ⟨t, ht, htx, -⟩ := hloc.swap hy hyx
  have hyP : y ∈ c.ptsP := by
    refine ⟨t, ?_, ?_⟩
    · rw [← htx, ← mul_one t, mk_mul_eq_smul]
      simp
    · rw [QuotientGroup.eq]
      simpa using ht
  exact h531 G z hJ c y ⟨hyP, CosetGeomLocal.adj hy hyx⟩ b ⟨hb, hadj⟩

end Loc49

end CFSG.Quasithin.H13.AS91
