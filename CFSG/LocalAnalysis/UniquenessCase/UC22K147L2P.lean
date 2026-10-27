module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PA
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PSw

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open Subgroup CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
open scoped MatrixGroups

theorem k147L2P_holds : K147L2P := by
  intro G _ _ V _ _ _ ρ _ _ hρ hirr L _ n hcase h2 hm
  obtain ⟨hn2, hL2, -⟩ := hcase
  have hn : 3 ≤ n := hn2
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 (P22fin.isL2Ev_of_isL2 hL2).1
  letI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact hF
  obtain ⟨g₀, hP⟩ := exists_isPair h2
  have hev : Even (Nat.card G) := by
    have hR : Nat.card (rootSub F) ∣ Nat.card SL(2, F) := Subgroup.card_subgroup_dvd_card _
    rw [natCard_rootSub, hF', ← Nat.card_congr e.toEquiv] at hR
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega)).trans
      (hR.trans (Subgroup.card_subgroup_dvd_card L)))
  obtain ⟨t, ht2, htd⟩ := exists_involution_of_mGV_le ρ hev hm
  have ht : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  by_cases hB : fixSub ρ (L.map (MulAut.conj g₀).toMonoidHom) = ⊥
  · exact Or.inr (hP.natOmegaPlus4_of_not_mem_normalizer ρ hρ hirr e hn hF' ht htd hB
      (hP.not_mem_normalizer_of_fixSub_eq_bot ρ hρ hirr e hn hF' ht ht1 htd hB))
  · exact Or.inl (case_fixSub_ne_bot ρ hρ hirr hP e hn hF' hL2 ht ht1 htd hB)

theorem k147L2_holds : K147L2 :=
  K147L2.of_split k147L2N_holds k147L2P_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
