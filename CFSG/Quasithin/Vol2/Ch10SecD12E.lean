module

public import CFSG.Quasithin.Vol2.Ch10SecD12D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem conjugate_V1_inv (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    conjSubgroup (fsuUL T L I) t⁻¹ = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  have htM : t⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (SecA.le_fsuM T L ht)
  rcases mem_normalizer_V12_or h37 h38 h ht htn htM with h1 | h1
  · exfalso
    apply V1_ne_V2 h37 h38 h ht htn
    have h2 : conjSubgroup (fsuUL T L I) t⁻¹ = fsuUL T L I :=
      conjSubgroup_eq_iff_mem_normalizer.2 h1.1
    rw [V2_eq_conjugate ht]
    show fsuUL T L I = conjSubgroup (fsuUL T L I) t
    conv_lhs => rw [← conjSubgroup_inv_conj (fsuUL T L I) t, h2]
  · exact h1.1

omit [Finite G] in
theorem rank_le_X {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0) {t : G} (ht : t ∈ T)
    {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) (E : Subgroup G)
    (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (X : Set G)) (hEa : IsElemAbelian 2 E) :
    mQuot E (E ⊓ Subgroup.centralizer (X : Set G)) ≤ r0 := by
  rcases hX with rfl | rfl
  · exact hD.rank_le E hE hEa
  · have hV2 : conjSubgroup ⁅fsuVM T L I, CFSG.conjugate L t⁆ t⁻¹ = fsuUL T L I := by
      rw [V2_eq_conjugate ht]
      exact conjSubgroup_conj_inv _ _
    have hM : conjSubgroup (fsuM T L) t⁻¹ = fsuM T L :=
      conjSubgroup_eq_iff_mem_normalizer.2
        (Subgroup.le_normalizer ((fsuM T L).inv_mem (SecA.le_fsuM T L ht)))
    have h1 : conjSubgroup E t⁻¹ ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) := by
      have := conjSubgroup_mono_left t⁻¹ hE
      rwa [conjSubgroup_inf, hM, conjSubgroup_normalizer, hV2] at this
    have h2 := hD.rank_le _ h1 (isElemAbelian_conjSubgroup hEa t⁻¹)
    rwa [← hV2, ← conjSubgroup_centralizer, ← conjSubgroup_inf, mQuot_conjSubgroup] at h2

theorem mQuot_inf_le {X V M : Subgroup G} (hXV : X ≤ V) (hV : IsPGroup 2 V) :
    mQuot X (X ⊓ M) ≤ mQuot V (V ⊓ M) := by
  have hX : IsPGroup 2 X := hV.to_le hXV
  have h1 : (X ⊓ M).relIndex X ≤ (V ⊓ M).relIndex V := by
    rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
    exact Subgroup.relIndex_le_of_le_right hXV Subgroup.index_ne_zero_of_finite
  rw [relIndex_eq_two_pow hX, relIndex_eq_two_pow hV] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem exists_not_le_centralizer {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {g : G} (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥)
    (hk : mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) < m) :
    ∃ X : Subgroup G, (X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) ∧
      ¬ conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hV := SecA.isElemAbelian_fsuVM h
  have hV2 : IsPGroup 2 (conjSubgroup (fsuVM T L I) g) :=
    isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
  by_contra hall
  push Not at hall
  have hXM : ∀ X : Subgroup G, (X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      conjSubgroup X g ≤ fsuM T L := by
    intro X hX
    have hXV := le_V_of_eq ht hX
    obtain ⟨K, hK, hKX⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
      rcases hX with rfl | rfl
      · exact ⟨L, Or.inl rfl, rfl⟩
      · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
    have hkX : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) < m :=
      lt_of_le_of_lt (mQuot_inf_le (conjSubgroup_mono_left g hXV) hV2) hk
    obtain ⟨a, haA, haL⟩ : ∃ a ∈ conjSubgroup X g ⊓ fsuM T L,
        a ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g := by
      by_contra hcon
      push Not at hcon
      have hle : conjSubgroup X g ⊓ fsuM T L ≤
          conjSubgroup X g ⊓ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g :=
        le_inf inf_le_left hcon
      have h1 := mQuot_mono (V := conjSubgroup X g) hle
      rw [← conjSubgroup_inf, mQuot_conjSubgroup, mQuot_V12 ht hX] at h1
      have := hD.rank_quot
      omega
    have hVa : fsuVM T L I ≤ conjSubgroup (fsuM T L ⊓
        Subgroup.normalizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G)) g := by
      intro v hv
      refine centralizer_le_conjSubgroup_inf h1029 h hK g (hKX ▸ haA.1) haL ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hall X hX haA) v hv
    set E := conjSubgroup (fsuUL T L I) g⁻¹ with hE
    have hEle : E ≤ fsuM T L ⊓ Subgroup.normalizer (X : Set G) := by
      have := conjSubgroup_mono_left g⁻¹ (V1_le_V.trans hVa)
      rwa [conjSubgroup_conj_inv, ← hKX] at this
    have hEa : IsElemAbelian 2 E :=
      isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono V1_le_V hV) g⁻¹
    have hr := rank_le_X hD ht hX E hEle hEa
    have hEm : m ≤ mQuot E ⊥ := by
      rw [hE, ← conjSubgroup_bot g⁻¹, mQuot_conjSubgroup]
      exact hD.rank_quot.trans (mQuot_mono bot_le)
    have hne : E ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hr
      have := hD.r0_lt
      omega
    obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
    have hc : g⁻¹ * e * g ∈ fsuUL T L I := by
      have h1 : e ∈ conjSubgroup (fsuUL T L I) g⁻¹ := he.1
      exact mem_conjSubgroup_inv_iff.mp h1
    have hc1 : g⁻¹ * e * g ≠ 1 := fun h1 => he1' (by
      have : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      rw [this, h1]
      group)
    intro y hy
    refine (h1029 G T L I h L (Or.inl rfl)).1 _ hc hc1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' := mem_conjSubgroup_iff.mp hy
    have h2 := (Subgroup.mem_centralizer_iff.mp he.2) _ hy'
    calc y * (g⁻¹ * e * g) = g⁻¹ * ((g * y * g⁻¹) * e) * g := by group
      _ = g⁻¹ * (e * (g * y * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * e * g * y := by group
  have hVg : conjSubgroup (fsuVM T L I) g =
      conjSubgroup (fsuUL T L I) g ⊔ conjSubgroup ⁅fsuVM T L I, CFSG.conjugate L t⁆ g := by
    conv_lhs => rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact Subgroup.map_sup _ _ _
  apply hnc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff, hVg]
  refine sup_le ?_ ?_
  · have h1 := hall _ (Or.inl rfl)
    rwa [inf_eq_left.mpr (hXM _ (Or.inl rfl))] at h1
  · have h1 := hall _ (Or.inr rfl)
    rwa [inf_eq_left.mpr (hXM _ (Or.inr rfl))] at h1

end CFSG.Quasithin.Vol2.Ch10.SecD
