module

public import CFSG.Quasithin.Vol2.Ch10SecD12N
public import CFSG.Quasithin.Vol2.Ch10SecD12K
public import CFSG.Quasithin.Vol2.Ch10SecD12M

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_normalizer_other (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {X X' : Subgroup G} (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hX' : X' = fsuUL T L I ∨ X' = ⁅fsuVM T L I, CFSG.conjugate L t⁆) {x : G}
    (hxM : x ∈ fsuM T L) (hxX : x ∈ Subgroup.normalizer (X : Set G)) :
    x ∈ Subgroup.normalizer (X' : Set G) := by
  have hne := V1_ne_V2 h37 h38 h ht htn
  rcases mem_normalizer_V12_or h37 h38 h ht htn hxM with h1 | h1
  · rcases hX' with rfl | rfl
    · exact h1.1
    · exact h1.2
  · exfalso
    rcases hX with rfl | rfl
    · exact hne ((SecA.conjugate_eq_self_iff.mpr hxX).symm.trans h1.1)
    · exact hne (h1.2.symm.trans (SecA.conjugate_eq_self_iff.mpr hxX))

theorem false_three_b (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h10211 : Stmt10_2_11) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥)
    (hk : mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) = 1)
    {X : Subgroup G} (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hAC : ¬ conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.centralizer (fsuUL T L I : Set G))
    (hAN : conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.normalizer (fsuUL T L I : Set G))
    (hkey : ∀ b ∈ conjSubgroup X g ⊓ fsuM T L,
      b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g →
      fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.centralizer ((conjSubgroup X g ⊓ fsuM T L : Subgroup G) : Set G))
    (hk1 : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) = 1)
    (hVM : ¬ fsuVM T L I ≤ conjSubgroup (fsuM T L) g) : False := by
  have hD := data_three h37 h38 hI16 h h3
  have hV := SecA.isElemAbelian_fsuVM h
  have hVg := isElemAbelian_conjSubgroup hV g
  have hV12 : fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ = ⊥ := by
    rw [eq_bot_iff, ← hc]
    intro x hx
    exact ⟨V1_le_V hx.1, V1_inf_V2_le h37 h38 h ht htn hx⟩
  obtain ⟨X', hX', hXX', hXX''⟩ : ∃ X' : Subgroup G,
      (X' = fsuUL T L I ∨ X' = ⁅fsuVM T L I, CFSG.conjugate L t⁆) ∧
        fsuVM T L I = X ⊔ X' ∧ X ⊓ X' = ⊥ := by
    rcases hX with rfl | rfl
    · exact ⟨_, Or.inr rfl, SecA.fsuVM_eq_sup h37 h38 h ht htn, hV12⟩
    · exact ⟨_, Or.inl rfl, by rw [sup_comm]; exact SecA.fsuVM_eq_sup h37 h38 h ht htn,
        by rw [inf_comm]; exact hV12⟩
  set W := conjSubgroup X g with hW
  set W' := conjSubgroup X' g with hW'
  set A := W ⊓ fsuM T L with hA
  have hVW : conjSubgroup (fsuVM T L I) g = W ⊔ W' := by
    conv_lhs => rw [hXX']
    exact Subgroup.map_sup X X' _
  have hWW' : W ⊓ W' = ⊥ := by rw [hW, hW', ← conjSubgroup_inf, hXX'', conjSubgroup_bot]
  have hWV : W ≤ conjSubgroup (fsuVM T L I) g := conjSubgroup_mono_left g (le_V_of_eq ht hX)
  have hWL : ∀ b ∈ W, b ≠ 1 → b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g := by
    intro b hb hb1 hbL
    rw [hW, mem_conjSubgroup_iff] at hb
    rw [mem_conjSubgroup_iff] at hbL
    have h1 : g * b * g⁻¹ ∈ fsuCVM T L I := ⟨le_V_of_eq ht hX hb, hbL⟩
    rw [hc, Subgroup.mem_bot] at h1
    exact hb1 (by
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
  have hF1 : ∀ b ∈ A, b ≠ 1 →
      fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    fun b hb hb1 => hkey b hb (hWL b hb.1 hb1)
  have hF4 : ∀ u ∈ fsuUL T L I ⊓ Subgroup.centralizer (A : Set G), u ≠ 1 →
      W ⊓ Subgroup.centralizer ({u} : Set G) ≤ A := fun u hu hu1 x hx =>
    ⟨hx.1, (h1029 G T L I h L (Or.inl rfl)).1 u hu.1 hu1 hx.2⟩
  obtain ⟨b0, hb0A, hb01⟩ : ∃ b0 ∈ A, b0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAC
    intro x hx
    rw [hcon x hx]
    exact one_mem _
  have hA1 : A ≠ ⊥ := fun hbot => hb01 (by rw [hbot] at hb0A; exact hb0A)
  obtain ⟨K, hK, hKX⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
    rcases hX with rfl | rfl
    · exact ⟨L, Or.inl rfl, rfl⟩
    · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
  have hCb0 := centralizer_le_conjSubgroup_inf h1029 h hK g (hKX ▸ hb0A.1) (hWL b0 hb0A.1 hb01)
  rw [conjSubgroup_inf, conjSubgroup_normalizer ⁅fsuVM T L I, K⁆ g, ← hKX] at hCb0
  have hUb0 : fsuUL T L I ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer ({b0} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu.2 b0 hb0A).symm
  have hUM : fsuUL T L I ⊓ Subgroup.centralizer (A : Set G) ≤ conjSubgroup (fsuM T L) g :=
    fun u hu => (hCb0 (hUb0 hu)).1
  have hUN : fsuUL T L I ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (W : Set G) := fun u hu => (hCb0 (hUb0 hu)).2
  have hUN' : fsuUL T L I ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (W' : Set G) := by
    intro u hu
    have h1 := hUM hu
    have h2 := hUN hu
    rw [mem_conjSubgroup_iff] at h1
    rw [hW, ← conjSubgroup_normalizer, mem_conjSubgroup_iff] at h2
    rw [hW', ← conjSubgroup_normalizer, mem_conjSubgroup_iff]
    exact mem_normalizer_other h37 h38 h ht htn hX hX' h1 h2
  obtain ⟨u1, hu1U, hu11⟩ : ∃ u1 ∈ fsuUL T L I ⊓ Subgroup.centralizer (A : Set G), u1 ≠ 1 := by
    obtain ⟨v, hv, hvL, hvb⟩ := hD.fix b0 (hAN hb0A) (hVg.2 b0 (hWV hb0A.1))
    refine ⟨v, ⟨hv, hF1 b0 hb0A hb01 ⟨hv, ?_⟩⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hvb.symm
    · rintro rfl
      exact hvL (one_mem _)
  have hWU : ∀ w ∈ W, (∀ u ∈ fsuUL T L I ⊓ Subgroup.centralizer (A : Set G),
      u * w * u⁻¹ = w) → w ∈ A := by
    intro w hw hwu
    refine hF4 u1 hu1U hu11 ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hwu u1 hu1U
    calc w * u1 = u1 * w * u1⁻¹ * u1 := by rw [this]
      _ = u1 * w := by group
  obtain ⟨v0, hv0, hv0A⟩ : ∃ v0 ∈ fsuUL T L I, v0 ∉ Subgroup.centralizer (A : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hAC
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hcon v hv) a ha).symm
  obtain ⟨w0, hw0, hw0A⟩ : ∃ w0 ∈ W, w0 ∉ A := by
    by_contra hcon
    push Not at hcon
    have hAW : A = W := le_antisymm inf_le_left fun w hw => hcon w hw
    rw [hAW, mQuot_self] at hk1
    exact absurd hk1 (by norm_num)
  have hW'M := not_le_fsuM_three h37 h38 hI16 h1013 h1029 h10210 h h3 ht htn hg hnc hX' hVM
  obtain ⟨c, hcVM, hcAW'⟩ := exists_c hVg hVW hWW' hA hk hw0 hw0A hW'M
  obtain ⟨u, hu, hcu⟩ := exists_u hVg hVW hWW' hUN hUN' hWU hcVM.1 hcAW'
  have hP := isPGroup_sup_three h37 h38 h1029 h10211 h h3 hc ht htn hk hX hUM hcVM hu hcu
  exact false_of_isPGroup_sup (B2F.isElemAbelian_mono V1_le_V hV)
    (B2F.isElemAbelian_mono hWV hVg) inf_le_left hAN hUN hF1 hF4 hA1 hv0 hv0A hw0 hw0A hP

end CFSG.Quasithin.Vol2.Ch10.SecD
