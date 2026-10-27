module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOneInput
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem s21_9TorusN_of (D : Data G) (Ch : Choice2011 G) (hC : uc22pwCartanSU3) :
    S21_9TorusN D Ch := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro _ _ L hL hLN n hX s hs hsn r hr hrs
  have hn : n ≠ 0 := by
    have := (CFSG.Blueprint.LieModel.admissible hX.2).2.1
    omega
  have h2n : 2 < n := by
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hsn
    obtain ⟨j, rfl⟩ := hs
    rcases j with _ | j
    · norm_num at hrs
      exact absurd hrs hr.ne_one
    · omega
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hTL : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN)
  have hT : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hS : IsSylowOf 2 (D.T ⊓ L) L := uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨x, hxL, hxo, hxN⟩ :=
    uc22ine229_exists_mem_normalizer_of_concl hTL hS hn hs hsn hr hrs
      (fun U hψ e m' hm' hnem => by
        obtain ⟨E, h1, h2, h3, h4, h5⟩ :=
          hC (Bar2 L) hX.1 n h2n hX U ↥D.T hT _ hψ e m' hm' hnem
        exact ⟨E, h1, ⟨h2, h3, h4⟩, h5⟩)
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hxo], Subgroup.zpowers_le.2 hxL,
    Subgroup.zpowers_le.2 hxN⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
