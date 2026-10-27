module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0X
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0Z
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0S0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC0S1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

theorem t_p : IsPGroup 2 (Tb 0) := t_sylow.isPGroup

theorem k0_enum' : KEnum k0 := kEnum_of_chk t_desc k0_chk k0_enum
theorem k1_enum' : KEnum k1 := kEnum_of_chk t_desc k1_chk k1_enum
theorem k2_enum' : KEnum k2 := kEnum_of_chk t_desc k2_chk k2_enum
theorem k3_enum' : KEnum k3 := kEnum_of_chk t_desc k3_chk k3_enum
theorem k4_enum' : KEnum k4 := kEnum_of_chk t_desc k4_chk k4_enum
theorem k5_enum' : KEnum k5 := kEnum_of_chk t_desc k5_chk k5_enum

theorem sx_tGenC : (closureC tGenC).subgroupOf (GB 0) = Tb 0 := by
  rw [← t_gens, closureC_map_code]
  rfl

theorem k0_top : Sx 0 k0 = Tb 0 := sx_tGenC

theorem k1_top : Sx 0 k1 = Tb 0 := sx_tGenC

theorem kList0 : KList 0 tLit ks [0, 1] := by
  refine kList_of ?_ ?_
  · intro D hD
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨k0_enum', k0_chk, _, k0_o2⟩
    · exact ⟨k1_enum', k1_chk, _, k1_o2⟩
    · exact ⟨k2_enum', k2_chk, _, k2_o2⟩
    · exact ⟨k3_enum', k3_chk, _, k3_o2⟩
    · exact ⟨k4_enum', k4_chk, _, k4_o2⟩
    · exact ⟨k5_enum', k5_chk, _, k5_o2⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact k0_top
    · exact k1_top

theorem table0 : ∀ A : Subgroup ↥(GB 0), A ≤ Tb 0 → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    (∃ H R Lh : Subgroup ↥(GB 0), FiveWit (L1b 0) (L2b 0) (Tb 0) A H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 0), SevenWit (L1b 0) (L2b 0) (Tb 0) A K Y := by
  intro A hAT _ hA4
  by_cases h1 : A ≤ Qx 0 k0
  · by_cases h2 : A ≤ Qx 0 k1
    · have hZ : XDesc (Qx 0 k0 ⊓ Qx 0 k1) zLit :=
        xdesc_inf (xdesc_Qx t_desc k0_enum' k0_chk) (xdesc_Qx t_desc k1_enum' k1_chk) z_inter
      have hAZ : A = Qx 0 k0 ⊓ Qx 0 k1 :=
        eq_of_le_of_card_ge (le_inf h1 h2) (by rw [hZ.card z_nodup, z_length]; exact hA4)
      rw [hAZ]
      exact Or.inl ⟨_, _, _, fiveWit_of_chk t_desc t0_data t_p hZ z_nodup z_five⟩
    · exact Or.inr ⟨_, _, sevenWit_of_top t_desc k1_enum' k1_chk t_p k1_top k1_o2 hAT h2⟩
  · exact Or.inr ⟨_, _, sevenWit_of_top t_desc k0_enum' k0_chk t_p k0_top k0_o2 hAT h1⟩

theorem close0 : ∀ U E : Subgroup ↥(GB 0), U ≤ E → E ≤ Tb 0 →
    Tb 0 ≤ normalizer (E : Set ↥(GB 0)) → IsElemAbelian 2 E → 4 ≤ Nat.card U →
    (∃ H R Lh : Subgroup ↥(GB 0), FiveWit (L1b 0) (L2b 0) (Tb 0) U H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 0), KillWit (L1b 0) (L2b 0) (Tb 0) U K Y := by
  intro U E hUE hET hTE hEe hU4
  have hq0 := xdesc_Qx t_desc k0_enum' k0_chk
  have hq1 := xdesc_Qx t_desc k1_enum' k1_chk
  have hE : E ≤ Qx 0 k0 ∨ E ≤ Qx 0 k1 := by
    apply SubgroupClass.subset_union.1
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Or.inl (one_mem _)
    obtain ⟨L, hL, hxL⟩ := mem_of_normal_elab t_desc close_inv hET hTE hEe hx hx1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · exact Or.inl ((hq0.mem x).2 hxL)
    · exact Or.inr ((hq1.mem x).2 hxL)
  have hUT : U ≤ Tb 0 := hUE.trans hET
  have hs0 := subs_parts (qLit_sub t_desc k0_chk) subs0_chk
  have hs1 := subs_parts (qLit_sub t_desc k1_chk) subs1_chk
  rcases hE with hE | hE
  · rcases exists_listed hq0 k0_enum'.qnd q0_length subs0_chk (hUE.trans hE) hU4 with
      rfl | ⟨k, hk, hUk⟩
    · exact close_of_stat t_desc t0_data t_p t_perm kList0 hq0 k0_enum'.qnd hUT qstat0
        qstat0_chk hs0
    · exact close_of_stat t_desc t0_data t_p t_perm kList0 hUk (hs0 k hk).2.2.1 hUT _
        (stats0_chk k hk) hs0
  · rcases exists_listed hq1 k1_enum'.qnd q1_length subs1_chk (hUE.trans hE) hU4 with
      rfl | ⟨k, hk, hUk⟩
    · exact close_of_stat t_desc t0_data t_p t_perm kList0 hq1 k1_enum'.qnd hUT qstat1
        qstat1_chk hs1
    · exact close_of_stat t_desc t0_data t_p t_perm kList0 hUk (hs1 k hk).2.2.1 hUT _
        (stats1_chk k hk) hs1

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open MF MF.M0

theorem modelFacts915_zero : ModelFacts915 0 := by
  unfold ModelFacts915
  exact
    { le_of_normal := le_of_normal_L 0 g_norm (mem_GB_of_mem 0 (by simp [bGens])) L02_eq_map
      cent := cent_L 0
      three := three_L 0
      pair := pair_of_chk 0 t_desc t_sylow pair_chk
      table := table0
      close := close0 }

end CFSG.LocalAnalysis.WeakClosure81.NGM
