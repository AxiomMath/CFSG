module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

theorem ggCommonJSpSplit_label_sp {K : Type} [Field K] [Finite K] [CharP K 2] {f r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hr : 3 ≤ r) {J : Subgroup (StatedSp r K)}
    (hiso : Nonempty (↥J ≃* StatedSp (r - 1) K)) :
    GGHasLabel ⟨.C, r - 1, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨e⟩ := hiso
  have hn : 1 ≤ r - 1 := by omega
  haveI : NeZero (r - 1) := ⟨by omega⟩
  have hZsp : Subgroup.center (StatedSp (r - 1) K) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := K) (n := r - 1) hn
  have hZ : Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ Subgroup.center (StatedSp (r - 1) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rw [hZsp, Subgroup.mem_bot] at hez
    rw [Subgroup.mem_bot]
    exact e.injective (hez.trans (map_one e).symm)
  change ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
    Nat.card K' = 2 ^ f ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
      LargeEvenProj (LargeEvenSpGroup K' (r - 1)))
  refine ⟨K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (e.trans (TableBSymp.spProjEquivSp (K := K) (m := r - 1)).symm)

end CFSG.StandardType

end
