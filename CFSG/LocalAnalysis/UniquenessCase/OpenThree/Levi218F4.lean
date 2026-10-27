module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3F4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LieType.Ree.ReeTag (F4)


theorem levi218_2F4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : LieModel Y .twistedF4 0 2 n)
    (hn : ¬ IsPowTwo n) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ n - 1) (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) :
    Levi218 n (2 ^ n - 1) U p := by
  obtain ⟨a, ha, rfl, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_f4_exists_model hY
  have : Finite (CFSG.Blueprint.Chevalley.ModGL F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have hrk' : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(F4.reeGamma K a)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact hrk
  have hpd := uc22s218_f4_dvd_add_one_or_sq_add_one hK hp hp2 hpq hrk'
  have hLevi : Levi218 (2 * a + 1) (2 ^ (2 * a + 1) - 1)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) p := by
    refine ⟨_, _, uc22s218_f4_fieldBorelData_model ha hK, fun {s r} hs hsn hr hrs => ?_⟩
    obtain ⟨x, hx, hxo, S, hSC, hSt, hpS⟩ :=
      uc22s218_f4_exists_levi_torus ha hK hpd hs hsn hr hrs
    refine ⟨x, hx, hxo, S, 2 * a + 1, hSC, by omega, hSt, Or.inl ⟨?_, hpS⟩⟩
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact uc22s218_f4_pRank_le_two hY hp hp2
  exact Levi218.of_sylow hp (hLevi.map hp e.symm) hU

end CFSG.LocalAnalysis.UniquenessCase.UC22
