module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC2T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC2K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC2S

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M2

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

theorem t_p : IsPGroup 2 (Tb 2) := t_sylow.isPGroup

theorem ks_chk : ∀ j < ks.length,
    KEnum (ks.getD j KData.dflt) ∧ KChk tLit (ks.getD j KData.dflt) = true := by
  have h : ∀ D ∈ ks, KEnum D ∧ KChk tLit D = true := by
    intro D hD
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl
    · exact ⟨kEnum_of_chk t_desc k0_chk k0_enum, k0_chk⟩
    · exact ⟨kEnum_of_chk t_desc k1_chk k1_enum, k1_chk⟩
    · exact ⟨kEnum_of_chk t_desc k2_chk k2_enum, k2_chk⟩
  intro j hj
  exact h _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)

theorem table2 : ∀ A : Subgroup ↥(GB 2), A ≤ Tb 2 → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    (∃ H R Lh : Subgroup ↥(GB 2), FiveWit (L1b 2) (L2b 2) (Tb 2) A H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 2), SevenWit (L1b 2) (L2b 2) (Tb 2) A K Y :=
  table_of_seeds t_desc t0_data t_p t_perm ks_chk reps_chk pairs_chk conj_chk

theorem close2 : ∀ U E : Subgroup ↥(GB 2), U ≤ E → E ≤ Tb 2 →
    Tb 2 ≤ normalizer (E : Set ↥(GB 2)) → IsElemAbelian 2 E → 4 ≤ Nat.card U →
    (∃ H R Lh : Subgroup ↥(GB 2), FiveWit (L1b 2) (L2b 2) (Tb 2) U H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 2), KillWit (L1b 2) (L2b 2) (Tb 2) U K Y :=
  close_of_z t_desc t0_data t_p z_chk close_inv z_five

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M2

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open MF MF.M2

theorem modelFacts915_two : ModelFacts915 2 := by
  unfold ModelFacts915
  exact
    { le_of_normal := le_of_normal_L 2 g_norm (mem_GB_of_mem 2 (by simp [bGens])) L02_eq_map
      cent := cent_L 2
      three := three_L 2
      pair := pair_of_chk 2 t_desc t_sylow pair_chk
      table := table2
      close := close2 }

end CFSG.LocalAnalysis.WeakClosure81.NGM
