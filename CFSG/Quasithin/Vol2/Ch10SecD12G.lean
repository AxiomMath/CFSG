module

public import CFSG.Quasithin.Vol2.Ch10SecD12E

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_normalizer_of_le {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0) (hr : r0 + 2 ≤ m)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {g : G} (hVg : conjSubgroup (fsuVM T L I) g ≤ fsuM T L) {X Y : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hY : Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) :
    Y ≤ conjSubgroup (fsuM T L) g ⊓
      Subgroup.normalizer ((conjSubgroup X g : Subgroup G) : Set G) := by
  have hV := SecA.isElemAbelian_fsuVM h
  set W := conjSubgroup X g with hW
  have hWV : W ≤ conjSubgroup (fsuVM T L I) g := conjSubgroup_mono_left g (le_V_of_eq ht hX)
  have hWM : W ≤ fsuM T L := hWV.trans hVg
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono hWV (isElemAbelian_conjSubgroup hV g)
  have hW2 : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hWel
  obtain ⟨K, hK, hKX⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
    rcases hX with rfl | rfl
    · exact ⟨L, Or.inl rfl, rfl⟩
    · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
  have hNY : W ⊓ Subgroup.normalizer (fsuUL T L I : Set G) ≤
      W ⊓ Subgroup.normalizer (Y : Set G) := by
    rintro x ⟨hxW, hxN⟩
    refine ⟨hxW, ?_⟩
    rcases hY with rfl | rfl
    · exact hxN
    · rcases mem_normalizer_V12_or h37 h38 h ht htn (hWM hxW) with h1 | h1
      · exact h1.2
      · exact absurd ((SecA.conjugate_eq_self_iff.mpr hxN).symm.trans h1.1)
          (V1_ne_V2 h37 h38 h ht htn)
  have hB1 : mQuot W (W ⊓ Subgroup.normalizer (Y : Set G)) ≤ 1 :=
    le_trans (mQuot_mono hNY) (mQuot_le_one_of_card_le hW2 inf_le_left
      (card_le_two_mul_card_inf_normalizer_V1 h37 h38 h hWM))
  set B := W ⊓ Subgroup.normalizer (Y : Set G) with hB
  have hBr := rank_le_X hD ht hY B (le_inf (inf_le_left.trans hWM) inf_le_right)
    (B2F.isElemAbelian_mono inf_le_left hWel)
  have hWC : mQuot W (B ⊓ Subgroup.centralizer (Y : Set G)) ≤ r0 + 1 := by
    rw [mQuot_add (inf_le_left : B ⊓ Subgroup.centralizer (Y : Set G) ≤ B)
      (inf_le_left : B ≤ W)]
    omega
  obtain ⟨c, hc, hcL⟩ : ∃ c ∈ B ⊓ Subgroup.centralizer (Y : Set G),
      c ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g := by
    by_contra hcon
    push Not at hcon
    have hle : B ⊓ Subgroup.centralizer (Y : Set G) ≤
        W ⊓ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g :=
      le_inf (inf_le_left.trans inf_le_left) hcon
    have h1 := mQuot_mono (V := W) hle
    have h2 : mQuot W (W ⊓ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g) =
        mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
      rw [hW, ← conjSubgroup_inf, mQuot_conjSubgroup, mQuot_V12 ht hX]
    have := hD.rank_quot
    omega
  have hcC := centralizer_le_conjSubgroup_inf h1029 h hK g (hKX ▸ hc.1.1) hcL
  rw [conjSubgroup_inf, conjSubgroup_normalizer ⁅fsuVM T L I, K⁆ g, ← hKX] at hcC
  intro y hy
  refine hcC ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hc.2 y hy

theorem wParam_pos {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0) (hr : r0 + 2 ≤ m)
    (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h : Hyp10 G T L I) :
    0 < E3.wParam T (fsuVM T L I) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hV := SecA.isElemAbelian_fsuVM h
  have hNV := SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h)
  by_contra hw
  push Not at hw
  have hw0 : E3.wParam T (fsuVM T L I) = ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero]
    exact le_antisymm hw zero_le
  obtain ⟨g, hnc, hgk⟩ := exists_isWOffenderAt hV (hypE322 h) hw0
  rw [hw0] at hgk
  have hk0 : mQuot (conjSubgroup (fsuVM T L I) g)
      (conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G)) = 0 := by
    exact_mod_cast hgk.symm
  have hVg : conjSubgroup (fsuVM T L I) g ≤ fsuM T L := by
    rw [← hNV]
    have := (mQuot_eq_zero_iff (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g)
      inf_le_left).1 hk0
    rw [← this]
    exact inf_le_right
  have hg : g ∉ fsuM T L := by
    intro hgM
    apply hnc
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (SecA.fsuM_le_normalizer_fsuVM T L I hgM),
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hV.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hVg' : conjSubgroup (fsuVM T L I) g⁻¹ ≤ fsuM T L := by
    have hle : fsuVM T L I ≤ conjSubgroup (fsuM T L) g := by
      rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
      exact sup_le
        ((le_normalizer_of_le hD hr h37 h38 h1029 h ht htn hVg (Or.inl rfl) (Or.inl rfl)).trans
          inf_le_left)
        ((le_normalizer_of_le hD hr h37 h38 h1029 h ht htn hVg (Or.inl rfl) (Or.inr rfl)).trans
          inf_le_left)
    have := conjSubgroup_mono_left g⁻¹ hle
    rwa [conjSubgroup_conj_inv] at this
  have hcomm : ∀ X Y : Subgroup G, (X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      (Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      Y ≤ Subgroup.centralizer ((conjSubgroup X g : Subgroup G) : Set G) := by
    intro X Y hX hY
    have h1 := (le_normalizer_of_le hD hr h37 h38 h1029 h ht htn hVg hX hY).trans inf_le_right
    have h2 : conjSubgroup X g ≤ Subgroup.normalizer (Y : Set G) := by
      have h3 := (le_normalizer_of_le hD hr h37 h38 h1029 h ht htn hVg' hY hX).trans
        inf_le_right
      have h4 := conjSubgroup_mono_left g h3
      rwa [conjSubgroup_normalizer, conjSubgroup_inv_conj] at h4
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, eq_bot_iff,
      ← V_inf_conjSubgroup_eq_bot h10210 h ht htn hg hY hX]
    refine le_inf (commutator_le_left_of_le_normalizer h2) ?_
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer h1
  have hVg2 : conjSubgroup (fsuVM T L I) g =
      conjSubgroup (fsuUL T L I) g ⊔ conjSubgroup ⁅fsuVM T L I, CFSG.conjugate L t⁆ g := by
    conv_lhs => rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact Subgroup.map_sup _ _ _
  have hY : ∀ Y : Subgroup G, (Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      Y ≤ Subgroup.centralizer ((conjSubgroup (fsuVM T L I) g : Subgroup G) : Set G) := by
    intro Y hY
    rw [Subgroup.le_centralizer_iff, hVg2]
    exact sup_le (Subgroup.le_centralizer_iff.mp (hcomm _ Y (Or.inl rfl) hY))
      (Subgroup.le_centralizer_iff.mp (hcomm _ Y (Or.inr rfl) hY))
  apply hnc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (SecA.fsuVM_eq_sup h37 h38 h ht htn).le.trans
    (sup_le (hY _ (Or.inl rfl)) (hY _ (Or.inr rfl)))

end CFSG.Quasithin.Vol2.Ch10.SecD
