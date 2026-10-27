module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwOmPlus_rankLE_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ}
    (hK : Nat.card K = 2 ^ n) (hr : 3 ≤ r) (hev : Even r) (hmr : m = r + 1)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGElemAbelianRankLE (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) 3 r := by
  intro E hE
  have hm : Odd m := by
    obtain ⟨j, hj⟩ := hev
    refine ⟨j, ?_⟩
    omega
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3
  have h := IOneMore.card_le_plus_odd (K := K) (m := m) (p := 3) hm Nat.prime_three
    (by norm_num) hpq E hE
  have hm1 : m - 1 = r := by omega
  rwa [hm1] at h

end CFSG.StandardType

end
