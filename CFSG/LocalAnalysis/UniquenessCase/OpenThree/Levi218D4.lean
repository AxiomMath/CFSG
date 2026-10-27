module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3D4
import CFSG.RankThree.PartOne.KF.ClsExcD4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RankBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint.Chevalley (TwistTag ModGL)
open CFSG.LieType.Chevalley (graphFixedRootGroup graphFixedPosUnipotent)


set_option linter.unusedVariables false in
theorem levi218_3D4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : Is3D4 Y n) (hn : ¬ IsPowTwo n)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ n - 1)
    (hrk : ¬ p ∣ 2 ^ (2 * n) + 2 ^ n + 1 → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) :
    Levi218 n (2 ^ (3 * n) - 1) U p := by
  obtain ⟨hn1, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  have : Finite (ModGL TwistTag.D4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have hpd : p ∣ 2 ^ (6 * n) - 1 := by
    by_cases hp3 : p ∣ 2 ^ (2 * n) + 2 ^ n + 1
    · have hq : p ∣ 2 ^ (3 * n) - 1 := by
        rw [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by rw [← pow_mul, mul_comm],
          CFSG.RankThree.PartOne.KFU.cube_sub_one _ Nat.one_le_two_pow]
        exact dvd_mul_of_dvd_right (by simpa only [pow_mul, mul_comm 2 n] using hp3) _
      have h6 : 2 ^ (6 * n) = (2 ^ (3 * n)) ^ 2 := by rw [← pow_mul]; congr 1; ring
      rw [h6]
      exact hq.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ (3 * n)) 2)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.dvd_two_pow_six_mul_sub_one_of_is3D4 hY hp hp2 (hrk hp3)
  have hLevi : Levi218 n (2 ^ (3 * n) - 1)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) p := by
    refine ⟨_, _, uc22s218_d4_fieldBorelData_model σ hn1 hσ3 hK hσ,
      fun {s r} hs hsn hr hrs => ?_⟩
    obtain ⟨x, hx, hxo, S, hSC, hSt, hpS⟩ :=
      uc22s218_d4_exists_levi_torus σ hσ3 hn1 hK hk hpd hs hsn hr hrs
    refine ⟨x, hx, hxo, S, 3 * n, hSC, by omega, Or.inl hSt, Or.inl ⟨?_, hpS⟩⟩
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact uc22s218_d4_pRank_le_two hY hp hp2
  exact Levi218.of_sylow hp (hLevi.map hp e.symm) hU

end CFSG.LocalAnalysis.UniquenessCase.UC22
