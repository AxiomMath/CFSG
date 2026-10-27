module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.Vol2.Ch11SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_normalizer_ne_bot_vi (h : Hyp11 G T L I n) {i : ℕ} (hi : 1 ≤ i) {U : Subgroup G}
    (hU : IsVi T L I n i U) : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
  have hp : IsPGroup 2 ↥U := (isPGroup_fsuV h).to_le (IsVi.le_fsuV hU)
  have hle : U ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
  intro hb
  rw [hb] at hle
  exact IsVi.ne_bot h hU hi (le_bot_iff.mp hle)

omit [Finite G] in
theorem autOn_perfect {K V : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hKK : ⁅K, K⁆ = K) : ⁅autOn K V, autOn K V⁆ = autOn K V :=
  CFSG.Quasithin.AutOn.autOn_perfect hKV hKK

end CFSG.Quasithin.Vol2.Ch11.SecA
