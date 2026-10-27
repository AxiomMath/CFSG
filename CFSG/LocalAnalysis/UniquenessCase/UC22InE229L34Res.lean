module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Res
import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem l34GFResidue_of_torus (hT : uc22pwTorusSU3) (hgr : GriessAllModelsStatement)
    (k : Sec7Core4 G)
    (h846 : ∀ Y ∈ calC k.M, ∀ n : ℕ, IsSU3 (Bar2 Y) n →
      ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n + 1 → IsStronglyPEmbedded r k.M) :
    L34GFResidue k := by
  intro hG3 hRee _ hp3 h4 Y hY X hXY q hq hq5 hXc _ hYt hH B₁ hB₁M hB₁ hB₁c hB₁X hB₁Y _ _ _ _ hF
  rcases hYt with hthin | ⟨n, hn, hqn⟩
  · exact uc22ine229_l34_false_of_pRank_le_one hG3 hRee k hp3 h4 hY hXY hq hq5 hXc
      (hthin q hq (by omega)) (hthin 3 Nat.prime_three (by norm_num)) hH hF
  · exact uc22ine229_l34_false_of_isSU3 hT hgr hG3 hRee k hp3 hY hn
      (fun r hr hr3 hrn => h846 Y hY n hn r hr hr3 hrn) hXY hq hq5 hXc hqn hH hF hB₁M hB₁ hB₁c
      hB₁X hB₁Y

theorem l34GFResidueAt_of_torus (hT : uc22pwTorusSU3) (hgr : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) : L34GFResidueAt hS hU S :=
  fun hp hsp => l34GFResidue_of_torus hT hgr _ h846

end CFSG.LocalAnalysis.UniquenessCase.UC22
