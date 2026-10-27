module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC1T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC1K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMC1S

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M1

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

theorem t_p : IsPGroup 2 (Tb 1) := t_sylow.isPGroup

theorem ks_chk : ∀ j < ks.length,
    KEnum (ks.getD j KData.dflt) ∧ KChk tLit (ks.getD j KData.dflt) = true := by
  have h : ∀ D ∈ ks, KEnum D ∧ KChk tLit D = true := by
    intro D hD
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl
    · exact ⟨kEnum_of_chk t_desc k0_chk k0_enum, k0_chk⟩
    · exact ⟨kEnum_of_chk t_desc k1_chk k1_enum, k1_chk⟩
  intro j hj
  exact h _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)

theorem table1 : ∀ A : Subgroup ↥(GB 1), A ≤ Tb 1 → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    (∃ H R Lh : Subgroup ↥(GB 1), FiveWit (L1b 1) (L2b 1) (Tb 1) A H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 1), SevenWit (L1b 1) (L2b 1) (Tb 1) A K Y :=
  table_of_seeds t_desc t0_data t_p t_perm ks_chk reps_chk pairs_chk conj_chk

theorem close1 : ∀ U E : Subgroup ↥(GB 1), U ≤ E → E ≤ Tb 1 →
    Tb 1 ≤ normalizer (E : Set ↥(GB 1)) → IsElemAbelian 2 E → 4 ≤ Nat.card U →
    (∃ H R Lh : Subgroup ↥(GB 1), FiveWit (L1b 1) (L2b 1) (Tb 1) U H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB 1), KillWit (L1b 1) (L2b 1) (Tb 1) U K Y :=
  close_of_z t_desc t0_data t_p z_chk close_inv z_five

theorem L02_eq_map_d1sig : L02 = L01.map (MulAut.conj (d1 * sig)).toMonoidHom := by
  have hd1 : d1 ∈ fixHiP := cfixHi_iff.1 (by decide)
  rw [map_conj_mul, ← L02_eq_map]
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨x, hx, ?_⟩
    rw [commute_of_fixHiP_fixLoP hd1 (L02_le_fixLoP hx)]
    simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    rw [commute_of_fixHiP_fixLoP hd1 (L02_le_fixLoP hy)]
    simpa [mul_assoc] using hy

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M1

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open MF MF.M1

theorem modelFacts915_one : ModelFacts915 1 := by
  unfold ModelFacts915
  exact
    { le_of_normal := le_of_normal_L 1 g_norm (mem_GB_of_mem 1 (by simp [bGens])) L02_eq_map_d1sig
      cent := cent_L 1
      three := three_L 1
      pair := pair_of_chk 1 t_desc t_sylow pair_chk
      table := table1
      close := close1 }

end CFSG.LocalAnalysis.WeakClosure81.NGM
