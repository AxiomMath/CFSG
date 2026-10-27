module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC3T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC3K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC3S

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

theorem t_p : IsPGroup 2 (Tb 3) := t_sylow.isPGroup

theorem ks_chk : ∀ j < ks.length,
    KEnum (ks.getD j KData.dflt) ∧ KChk tLit (ks.getD j KData.dflt) = true := by
  have h : ∀ D ∈ ks, KEnum D ∧ KChk tLit D = true := by
    intro D hD
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · exact ⟨kEnum_of_chk t_desc k0_chk k0_enum, k0_chk⟩
    · exact ⟨kEnum_of_chk t_desc k1_chk k1_enum, k1_chk⟩
    · exact ⟨kEnum_of_chk t_desc k2_chk k2_enum, k2_chk⟩
    · exact ⟨kEnum_of_chk t_desc k3_chk k3_enum, k3_chk⟩
  intro j hj
  exact h _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)

theorem table3 : ∀ A : Subgroup ↥(GB 3), A ≤ Tb 3 → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    (∃ H R Lh : Subgroup ↥(GB 3), FiveWit (L1b 3) (L2b 3) (Tb 3) A H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 3), SevenWit (L1b 3) (L2b 3) (Tb 3) A K Y :=
  table_of_seeds t_desc t0_data t_p t_perm ks_chk reps_chk pairs_chk conj_chk

theorem close3 : ∀ U E : Subgroup ↥(GB 3), U ≤ E → E ≤ Tb 3 →
    Tb 3 ≤ normalizer (E : Set ↥(GB 3)) → IsElemAbelian 2 E → 4 ≤ Nat.card U →
    (∃ H R Lh : Subgroup ↥(GB 3), FiveWit (L1b 3) (L2b 3) (Tb 3) U H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 3), KillWit (L1b 3) (L2b 3) (Tb 3) U K Y :=
  close_of_z t_desc t0_data t_p z_chk close_inv z_five

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open MF MF.M3

theorem modelFacts915_three : ModelFacts915 3 := by
  unfold ModelFacts915
  exact
    { le_of_normal := le_of_normal_L 3 g_norm (mem_GB_of_mem 3 (by simp [bGens])) L02_eq_map
      cent := cent_L 3
      three := three_L 3
      pair := pair_of_chk 3 t_desc t_sylow pair_chk
      table := table3
      close := close3 }

end CFSG.LocalAnalysis.WeakClosure81.NGM
