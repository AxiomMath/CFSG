module

public import CFSG.Quasithin.Vol2.Ch10SecD12E

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conjSubgroup_mul_inf {Y M : Subgroup G} (g : G) {t : G} (ht : t ∈ M) :
    conjSubgroup Y (g * t) ⊓ M = conjSubgroup (conjSubgroup Y g ⊓ M) t := by
  rw [conjSubgroup_inf, conjSubgroup_conjSubgroup,
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer ht)]

theorem exists_good {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {g : G} (hg : g ∉ fsuM T L) (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥)
    (hk : mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) < m) :
    ∃ g' : G, g' ∉ fsuM T L ∧ ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g'⁆ ≠ ⊥ ∧
      mQuot (conjSubgroup (fsuVM T L I) g') (conjSubgroup (fsuVM T L I) g' ⊓ fsuM T L) =
        mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) ∧
      ∃ X : Subgroup G, (X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) ∧
        ¬ conjSubgroup X g' ⊓ fsuM T L ≤ Subgroup.centralizer (fsuUL T L I : Set G) ∧
        mQuot (conjSubgroup X g') (conjSubgroup X g' ⊓ fsuM T L) ≤
          mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) := by
  have hV := SecA.isElemAbelian_fsuVM h
  have hV2 : IsPGroup 2 (conjSubgroup (fsuVM T L I) g) :=
    isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
  obtain ⟨X, hX, hXC⟩ := exists_not_le_centralizer hD h37 h38 h1029 h ht htn hnc hk
  have hmX := mQuot_inf_le (M := fsuM T L) (conjSubgroup_mono_left g (le_V_of_eq ht hX)) hV2
  by_cases h1 : conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.centralizer (fsuUL T L I : Set G)
  ·
    have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
    have h2 : ¬ conjSubgroup X g ⊓ fsuM T L ≤
        Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
      intro h2
      apply hXC
      rw [Subgroup.le_centralizer_iff, SecA.fsuVM_eq_sup h37 h38 h ht htn]
      exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
    have hVt : conjSubgroup (fsuVM T L I) t = fsuVM T L I :=
      conjSubgroup_eq_iff_mem_normalizer.2 (SecA.fsuM_le_normalizer_fsuVM T L I htM)
    refine ⟨g * t, fun hgt => hg ?_, ?_, ?_, X, hX, ?_, ?_⟩
    · have : g = g * t * t⁻¹ := by group
      rw [this]
      exact (fsuM T L).mul_mem hgt ((fsuM T L).inv_mem htM)
    · intro hbot
      apply hnc
      have h3 : conjSubgroup ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ t = ⊥ := by
        rw [conjSubgroup_commutator, hVt, conjSubgroup_conjSubgroup]
        exact hbot
      rw [← conjSubgroup_conj_inv ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ t, h3,
        conjSubgroup_bot]
    · rw [conjSubgroup_mul_inf g htM, ← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    · intro h3
      apply h2
      rw [conjSubgroup_mul_inf g htM] at h3
      have h4 := conjSubgroup_mono_left t⁻¹ h3
      rwa [conjSubgroup_conj_inv, conjSubgroup_centralizer,
        conjugate_V1_inv h37 h38 h ht htn] at h4
    · rw [conjSubgroup_mul_inf g htM, ← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
      exact hmX
  · exact ⟨g, hg, hnc, rfl, X, hX, h1, hmX⟩

theorem le_add_a0 {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h : Hyp10 G T L I)
    (hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥)
    (hk : mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) + 2 ≤
      m) :
    m ≤ mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) + a0 := by
  obtain ⟨g', hg', hnc', -, X, hX, hXC, hXk⟩ :=
    exists_good hD h37 h38 h1029 h ht htn hg hnc (by omega)
  have := (acts_and_le hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg' hnc' hX hXC
    (by omega)).2.2
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
