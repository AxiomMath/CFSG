module

public import CFSG.Quasithin.Vol2.Ch10SecD12F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_offender (h331 : Stmt3_3_1) (h : Hyp10 G T L I) {k : ℕ}
    (hk : E3.wParam T (fsuVM T L I) = k) :
    ∃ g : G, g ∉ fsuM T L ∧ ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥ ∧
      mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) = k := by
  have hV := SecA.isElemAbelian_fsuVM h
  have hNV := SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h)
  obtain ⟨g, hnc, hgk⟩ := exists_isWOffenderAt hV (hypE322 h) hk
  rw [hk, hNV] at hgk
  refine ⟨g, fun hgM => hnc ?_, hnc, by exact_mod_cast hgk.symm⟩
  rw [conjSubgroup_eq_iff_mem_normalizer.2 (SecA.fsuM_le_normalizer_fsuVM T L I hgM),
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hV.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem lt_wParam {m a0 r0 j : ℕ} (hD : Data10212 T L I m a0 r0)
    (hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I) (hj : j + 2 ≤ m)
    (hja : j + a0 < m) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h : Hyp10 G T L I) : (j : ℕ∞) < E3.wParam T (fsuVM T L I) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  by_contra hle
  push Not at hle
  obtain ⟨k, hk⟩ : ∃ k : ℕ, E3.wParam T (fsuVM T L I) = k :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top j) hle)).symm⟩
  have hkj : k ≤ j := by
    rw [hk] at hle
    exact_mod_cast hle
  obtain ⟨g, hg, hnc, hgk⟩ := exists_offender h331 h hk
  have := le_add_a0 hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg hnc (by omega)
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
