module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3One
public import CFSG.LocalAnalysis.WeakClosure81.W183K3I1
public import CFSG.LocalAnalysis.WeakClosure81.W183K3L34

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

theorem br3MasterOne_holds : Br3MasterOne := by
  unfold Br3MasterOne
  intro rows V _ _ _ Y T L Γ VA 𝒢 Zs m i₀ δ hB hL hshape hne hall
  classical
  by_cases hrk : ∀ D ∈ Γ, 3 ≤ mRank D
  · exact br3_false_of_one rows hB hL hshape.symm hrk hne
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite (LGL 2 V) :=
      Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
        (fun e f h => LinearEquiv.ext (congrFun h))
    rw [not_forall] at hrk
    obtain ⟨D, hrk'⟩ := hrk
    rw [not_imp, not_le] at hrk'
    obtain ⟨hD, hrlt⟩ := hrk'
    have hrank2 : mRank D = 2 := by
      have := hall D hD
      omega
    have hel : IsElemAbelian 2 D := hB.h131.isElemAb D hD
    have hcard : Nat.card ↥D = 4 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥D)).mp hel.isPGroup
      have hlog : mRank D = k := by
        rw [mRank, hk, Nat.log_pow (by norm_num : 1 < 2)]
      have hk2 : k = 2 := by omega
      rw [hk, hk2]
      norm_num
    have hr : mRank D ≤ m - i₀ - 1 := by
      have := hB.hmi
      omega
    obtain ⟨τ, hτT, hτd⟩ := hL.dynkin
    have hτY : τ ∈ Y := hB.sylow.le hτT
    rcases hshape with hs | hs
    · exact br3_false_of_A6 rows hB.h131 hL.core hs ⟨τ, hτY, hτd⟩ hD hr hcard
    · exact br3_false_of_L34 rows hB.h131 hB.vfix hL.core hs hD hr hcard

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
