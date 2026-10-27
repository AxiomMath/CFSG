module

public import CFSG.Quasithin.Vol2.Ch10SecD12O
public import CFSG.Quasithin.Vol2.Ch10SecD12H

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem one_lt_wParam_three (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6) (h1013 : Stmt10_1_3)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h10211 : Stmt10_2_11) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) : (1 : ℕ∞) < E3.wParam T (fsuVM T L I) := by
  have hD := data_three h37 h38 hI16 h h3
  have hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I :=
    Or.inr (genFaithful_three h37 h38 hI16 h h3)
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  by_contra hle
  push Not at hle
  obtain ⟨k, hk⟩ : ∃ k : ℕ, E3.wParam T (fsuVM T L I) = k :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top 1) hle)).symm⟩
  have hk1 : k ≤ 1 := by
    rw [hk] at hle
    exact_mod_cast hle
  obtain ⟨g, hg, hnc, hgk⟩ := exists_offender h331 h hk
  have hm := le_add_a0 hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg hnc (by omega)
  have hk1' : k = 1 := by omega
  subst hk1'
  have hw : 0 < E3.wParam T (fsuVM T L I) := by
    rw [hk]
    norm_num
  obtain ⟨g', hg', hnc', hk', X, hX, hXC, hXk⟩ :=
    exists_good hD h37 h38 h1029 h ht htn hg hnc (by omega)
  rw [hgk] at hk' hXk
  obtain ⟨hAN, hkey, hm'⟩ :=
    acts_and_le hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg' hnc' hX hXC (by omega)
  have hVM : ¬ fsuVM T L I ≤ conjSubgroup (fsuM T L) g' := by
    intro hVM
    apply hnc'
    have hVN : fsuVM T L I ≤ Subgroup.normalizer
        ((conjSubgroup (fsuVM T L I) g' : Subgroup G) : Set G) := by
      refine hVM.trans ?_
      rw [← conjSubgroup_normalizer]
      exact conjSubgroup_mono_left g' (SecA.fsuM_le_normalizer_fsuVM T L I)
    exact E3.commutator_eq_bot_iff_le_centralizer'.2
      ((E3.e3_25_centralizer_iff_normalizer (SecA.isElemAbelian_fsuVM h) (hypE322 h) hw g').2
        hVN)
  by_cases hc : fsuCVM T L I = ⊥
  · exact false_three_b h37 h38 hI16 h1013 h1029 h10210 h10211 h h3 hc ht htn hg' hnc' hk' hX
      hXC hAN hkey (by omega) hVM
  · exact false_three_a h37 h38 hI16 h1029 h h3 hc ht htn hX hAN (by omega) hVM

end CFSG.Quasithin.Vol2.Ch10.SecD
