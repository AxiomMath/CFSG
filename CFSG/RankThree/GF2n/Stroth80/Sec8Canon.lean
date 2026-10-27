module

public import CFSG.RankThree.GF2n.Stroth80.Sec8CanonPts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec8Canon_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Sec8CanonStatement := by
  intro G _ _ M Q Z B hc n t hs r hr g hgM hgV
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  obtain ⟨h, hhR, hp₁, hp₂⟩ := sec8_canon_exists_h h34 hRoot hs hr hgM hgV
  have hhM : h ∈ M := hc.Rt_le_M t hhR
  have hgVeq : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    sec8_conjSubgroup_eq_of_mem_normalizer hgV
  have hVh : conjSubgroup h (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hhR)
  have hconjV : ∀ g' ∈ M, conjSubgroup g' (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t →
      conjSubgroup g' (Sec8V1 M Q Z B t r) =
        Vone Q (conjSubgroup g' B) (conjSubgroup (g' * r) B) (Vt M (LB M Q B) B Z t) := by
    intro g' hg' hV'
    rw [conjSubgroup_mul]
    exact sec8_conj_Vone (hc.conj_Q_eq hg') hV'
  have hEq : conjSubgroup g (Sec8V1 M Q Z B t r) = conjSubgroup h (Sec8V1 M Q Z B t r) := by
    rw [hconjV g hgM hgVeq, hconjV h hhM hVh]
    unfold Vone
    rw [sec8_inf_QB_eq_of_sup_eq (hc.conj_of_mem hgM) (hc.conj_of_mem hhM) hp₁,
      sec8_inf_QB_eq_of_sup_eq (hc.conj_of_mem (M.mul_mem hgM hrM))
        (hc.conj_of_mem (M.mul_mem hhM hrM)) hp₂]
  have hfix : conjSubgroup h (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r :=
    (sec8InvStatement_holds G M Q Z B hc n t hs r hr h hhR).1
  exact conjSubgroup_eq_self_iff.mp (hEq.trans hfix)

end CFSG.RankThree.GF2n.Stroth80
