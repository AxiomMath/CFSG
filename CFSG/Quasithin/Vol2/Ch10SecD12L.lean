module

public import CFSG.Quasithin.Vol2.Ch10SecD12F
public import CFSG.Quasithin.Vol2.Ch10SecD12J
public import CFSG.Quasithin.Vol2.Ch10SecD31A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_add_a0_of_not_le {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h : Hyp10 G T L I)
    (hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥) {X Y : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hY : Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hAC : ¬ conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.centralizer (Y : Set G))
    (hk : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) + 2 ≤ m) :
    m ≤ mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) + a0 := by
  rcases hY with rfl | rfl
  · exact (acts_and_le hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg hnc hX hAC hk).2.2
  · have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
    have hVt : conjSubgroup (fsuVM T L I) t = fsuVM T L I :=
      conjSubgroup_eq_iff_mem_normalizer.2 (SecA.fsuM_le_normalizer_fsuVM T L I htM)
    have hgt : g * t ∉ fsuM T L := fun hgt => hg (by
      have : g = g * t * t⁻¹ := by group
      rw [this]
      exact (fsuM T L).mul_mem hgt ((fsuM T L).inv_mem htM))
    have hnct : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) (g * t)⁆ ≠ ⊥ := by
      intro hbot
      apply hnc
      have h3 : conjSubgroup ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ t = ⊥ := by
        rw [conjSubgroup_commutator, hVt, conjSubgroup_conjSubgroup]
        exact hbot
      rw [← conjSubgroup_conj_inv ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ t, h3,
        conjSubgroup_bot]
    have hkt : mQuot (conjSubgroup X (g * t)) (conjSubgroup X (g * t) ⊓ fsuM T L) =
        mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) := by
      rw [conjSubgroup_mul_inf g htM, ← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    have hACt : ¬ conjSubgroup X (g * t) ⊓ fsuM T L ≤
        Subgroup.centralizer (fsuUL T L I : Set G) := by
      intro h3
      apply hAC
      rw [conjSubgroup_mul_inf g htM] at h3
      have h4 := conjSubgroup_mono_left t⁻¹ h3
      rwa [conjSubgroup_conj_inv, conjSubgroup_centralizer,
        conjugate_V1_inv h37 h38 h ht htn] at h4
    have := (acts_and_le hD h37 h38 h1013 h1029 h10210 h hgf ht htn hgt hnct hX hACt
      (by omega)).2.2
    omega

omit [Finite G] in
theorem exists_conj_V1 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {a b : G}
    (ha : a ∈ fsuUL T L I) (hb : b ∈ fsuUL T L I) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ l ∈ L, l * a * l⁻¹ = b := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  set a' : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨a, ha⟩, trivial⟩
  set b' : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨b, hb⟩, trivial⟩
  have hne : ∀ x : ↥(⊤ : Subgroup ↥(fsuUL T L I)), ((x : ↥(fsuUL T L I)) : G) ≠ 1 →
      Multiplicative.toAdd (D.β x) ≠ 0 := by
    intro x hx h0
    apply hx
    have h1 : D.β x = 1 := by
      have : D.β x = Multiplicative.ofAdd 0 := by rw [← h0]; rfl
      rw [this]; rfl
    have h2 := hβinj (h1.trans (map_one D.β).symm)
    rw [h2]
    rfl
  obtain ⟨γ, hγ⟩ := L3.act_trans _ _ (hne a' ha1) (hne b' hb1)
  have h1 := D.β_rho γ ⟨a, ha⟩ trivial trivial
  have h2 : D.β ⟨D.rho γ ⟨a, ha⟩, trivial⟩ = D.β b' := by
    rw [h1, hγ]
    rfl
  have h3 := hβinj h2
  obtain ⟨⟨l, hlN⟩, hl, hlρ⟩ := D.rho_mem γ
  refine ⟨l, Subgroup.mem_subgroupOf.mp hl, ?_⟩
  have h4 : ((D.rho γ ⟨a, ha⟩ : ↥(fsuUL T L I)) : G) = b := congrArg (fun x => (x.1 : G)) h3
  rw [← hlρ, A1b.conjAct_coe] at h4
  exact h4

theorem not_le_fsuM_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥) {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hVM : ¬ fsuVM T L I ≤ conjSubgroup (fsuM T L) g) : ¬ conjSubgroup X g ≤ fsuM T L := by
  intro hXM
  have hD := data_three h37 h38 hI16 h h3
  have hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I :=
    Or.inr (genFaithful_three h37 h38 hI16 h h3)
  have hA : conjSubgroup X g ⊓ fsuM T L = conjSubgroup X g := inf_eq_left.mpr hXM
  have hk0 : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) = 0 := by
    rw [hA, mQuot_self]
  have hC : ∀ Y : Subgroup G, (Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      conjSubgroup X g ≤ Subgroup.centralizer (Y : Set G) := by
    intro Y hY
    by_contra hcon
    rw [← hA] at hcon
    have := le_add_a0_of_not_le hD h37 h38 h1013 h1029 h10210 h hgf ht htn hg hnc hX hY hcon
      (by omega)
    omega
  have hXC : conjSubgroup X g ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [Subgroup.le_centralizer_iff, SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact sup_le (Subgroup.le_centralizer_iff.mp (hC _ (Or.inl rfl)))
      (Subgroup.le_centralizer_iff.mp (hC _ (Or.inr rfl)))
  obtain ⟨K, hK, hKX⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
    rcases hX with rfl | rfl
    · exact ⟨L, Or.inl rfl, rfl⟩
    · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
  have hX1 : conjSubgroup X g ≠ ⊥ := by
    intro hbot
    have h1 := congrArg (fun H => conjSubgroup H g⁻¹) hbot
    simp only [conjSubgroup_conj_inv, conjSubgroup_bot] at h1
    rcases hX with rfl | rfl
    · exact SecA.commutator_fsuVM_ne_bot h.fsu h1
    · have h2 : conjSubgroup (fsuUL T L I) t = ⊥ := by
        rw [← h1, V2_eq_conjugate ht]
        rfl
      apply SecA.commutator_fsuVM_ne_bot h.fsu
      show fsuUL T L I = ⊥
      rw [← conjSubgroup_conj_inv (fsuUL T L I) t, h2, conjSubgroup_bot]
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  apply hVM
  intro v hv
  refine centralizer_le_conjSubgroup h1029 h hK g (hKX ▸ hx) hx1' ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp (hXC hx) v hv

theorem false_three_a (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I ≠ ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hAN : conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.normalizer (fsuUL T L I : Set G))
    (hk1 : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) ≤ 1)
    (hVM : ¬ fsuVM T L I ≤ conjSubgroup (fsuM T L) g) : False := by
  have hD := data_three h37 h38 hI16 h h3
  have hV := SecA.isElemAbelian_fsuVM h
  have hV1 := cV1_ne_bot h37 h38 h hc
  have h16 := (card_V1_eq h37 h38 hI16 h h3 hV1).1
  set A := conjSubgroup X g ⊓ fsuM T L with hA
  have hXV := le_V_of_eq ht hX
  have hWel : IsElemAbelian 2 (conjSubgroup X g) :=
    B2F.isElemAbelian_mono (conjSubgroup_mono_left g hXV) (isElemAbelian_conjSubgroup hV g)
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono inf_le_left hWel
  have hX16 : Nat.card ↥(conjSubgroup X g) = 16 := by
    rw [card_conjSubgroup]
    rcases hX with rfl | rfl
    · exact h16
    · rw [V2_eq_conjugate ht]
      exact (card_conjSubgroup _ _).trans h16
  have hA8 : 8 ≤ Nat.card A := by
    have h1 := card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hWel)
      (inf_le_left : A ≤ conjSubgroup X g)
    rw [hX16] at h1
    have h2 : 2 ^ mQuot (conjSubgroup X g) A ≤ 2 := by
      calc 2 ^ mQuot (conjSubgroup X g) A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    nlinarith
  obtain ⟨K, hK, hKX⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
    rcases hX with rfl | rfl
    · exact ⟨L, Or.inl rfl, rfl⟩
    · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
  have hYM : ∀ Y : Subgroup G, (Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) →
      Y ≤ conjSubgroup (fsuM T L) g := by
    intro Y hY
    have hAY : A ≤ fsuM T L ⊓ Subgroup.normalizer (Y : Set G) := by
      intro a ha
      refine ⟨ha.2, ?_⟩
      rcases hY with rfl | rfl
      · exact hAN ha
      · rcases mem_normalizer_V12_or h37 h38 h ht htn ha.2 with h1 | h1
        · exact h1.2
        · exact absurd ((SecA.conjugate_eq_self_iff.mpr (hAN ha)).symm.trans h1.1)
            (V1_ne_V2 h37 h38 h ht htn)
    have hr := rank_le_X hD ht hY A hAY hAel
    have h1 := card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hAel)
      (inf_le_left : A ⊓ Subgroup.centralizer (Y : Set G) ≤ A)
    have hne : A ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := by
      intro hbot
      have hc1 : Nat.card ↥(A ⊓ Subgroup.centralizer (Y : Set G)) = 1 := by
        rw [hbot, Subgroup.card_bot]
      rw [hc1, mul_one] at h1
      have h2 : 2 ^ mQuot A (A ⊓ Subgroup.centralizer (Y : Set G)) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) hr
      omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
    intro y hy
    refine centralizer_le_conjSubgroup h1029 h hK g (hKX ▸ ha.1.1) ha1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ha.2 y hy
  apply hVM
  rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
  exact sup_le (hYM _ (Or.inl rfl)) (hYM _ (Or.inr rfl))

end CFSG.Quasithin.Vol2.Ch10.SecD
