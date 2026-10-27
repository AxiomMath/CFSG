module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Frame
public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

theorem exists_mem_notMem_of_card_lt {H : Type*} [Group H] [Finite H] (R : Subgroup H)
    (s : Finset H) (hs : s.card < Nat.card R) : ∃ b ∈ R, b ∉ s := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (R : Set H) ⊆ (s : Set H) := fun a ha => hcon a ha
  have h1 : Nat.card R ≤ Nat.card (s : Set H) := Nat.card_mono s.finite_toSet hsub
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
  omega

theorem card_e4Sub : Nat.card ↥e4Sub = 4 := by
  classical
  have h1 : (Finset.univ.filter InE4).card = 4 := by decide +kernel
  rw [← h1, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun σ => by
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

section Baum

variable {G : Type} [Group G] [Finite G] {Y W : Subgroup G}

structure A5BaumHyp (F : S5Frame Y W) (T : Subgroup G) : Prop where
  TY : T ≤ Y
  WT : W ≤ T
  el : IsElemAbelian 2 W
  TD : ∀ t : ↥Y, (t : G) ∈ T → InD8 (F.ρ t)
  DT : ∀ σ : Perm (Fin 5), InD8 σ → ∃ t : ↥Y, (t : G) ∈ T ∧ F.ρ t = σ
  J : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G)

namespace A5BaumHyp

variable {F : S5Frame Y W} {T : Subgroup G}

omit [Finite G] in
theorem card_range_le_four (F : S5Frame Y W) {A : Subgroup G} (hAY : A ≤ Y)
    (hA : IsElemAbelian 2 A) : Nat.card (F.ρOn hAY).range ≤ 4 := by
  have hsq : ∀ σ ∈ (F.ρOn hAY).range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, ← pow_two]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hA.2 a a.2)
    rw [this, map_one]
  have hcomm : ∀ σ ∈ (F.ρOn hAY).range, ∀ τ ∈ (F.ρOn hAY).range, σ * τ = τ * σ := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hA.1
    exact Subtype.ext (setLike_mul_comm a.2 b.2)
  refine card_le_four_of_dependent _ fun γ hγ δ hδ ε hε => ?_
  exact s5_elemAbelian_rank γ (hsq γ hγ) δ (hsq δ hδ) (hcomm γ hγ δ hδ) ε (hsq ε hε)
    (hcomm γ hγ ε hε) (hcomm δ hδ ε hε)

theorem rho_offender (h : A5BaumHyp F T) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (a : ↥Y) (ha : (a : G) ∈ A) : InE4 (F.ρ a) := by
  classical
  by_contra hne
  have hAY : A ≤ Y := hA.1.trans h.TY
  have hineq := card_le_relIndex_mul_card h.el h.WT hA
  rw [F.relIndex_eq_card_range hAY, F.card_W] at hineq
  have hR4 := card_range_le_four F hAY hA.2.1
  have haD : InD8 (F.ρ a) := h.TD a (hA.1 ha)
  have ha2 : F.ρ a * F.ρ a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := by
      apply Subtype.ext
      show (a : G) * a = 1
      rw [← pow_two]
      exact hA.2.1.2 _ ha
    rw [this, map_one]
  have hfix1 := F.card_fix_le (A := A) ha
  rw [d5_fix_card_outside _ haD ha2 hne] at hfix1
  by_cases hR : Nat.card (F.ρOn hAY).range ≤ 2
  · have : Nat.card (F.ρOn hAY).range * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ 8 :=
      calc _ ≤ 2 * 4 := Nat.mul_le_mul hR hfix1
        _ = 8 := by norm_num
    omega
  · push Not at hR
    obtain ⟨b, ⟨b', rfl⟩, hb⟩ := exists_mem_notMem_of_card_lt (F.ρOn hAY).range
      {1, F.ρ a} (lt_of_le_of_lt (Finset.card_le_two) hR)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    have hb'Y : (⟨b', hAY b'.2⟩ : ↥Y) = Subgroup.inclusion hAY b' := rfl
    have hbD : InD8 (F.ρOn hAY b') := h.TD _ (hA.1 b'.2)
    have hb2 : F.ρOn hAY b' * F.ρOn hAY b' = 1 := by
      rw [← map_mul]
      have : b' * b' = 1 := by
        apply Subtype.ext
        show (b' : G) * b' = 1
        rw [← pow_two]
        exact hA.2.1.2 _ b'.2
      rw [this, map_one]
    have hab : F.ρ a * F.ρOn hAY b' = F.ρOn hAY b' * F.ρ a := by
      have ha' : F.ρ a = F.ρOn hAY ⟨a, ha⟩ := rfl
      rw [ha', ← map_mul, ← map_mul]
      congr 1
      have := hA.2.1.1
      exact Subtype.ext (setLike_mul_comm ha b'.2)
    have hpair : PairCond (F.ρ a) (F.ρOn hAY b') :=
      ⟨haD, hbD, ha2, hb2, hab, hne, hb.1, hb.2⟩
    have hfix2 := F.card_fix_le_two (A := A) (a := a) (b := Subgroup.inclusion hAY b') ha b'.2
    have hfix2' : Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 := by
      have := d5_fix_card_pair _ _ hpair
      rw [← this]
      exact hfix2
    have : Nat.card (F.ρOn hAY).range * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ 8 :=
      calc _ ≤ 4 * 2 := Nat.mul_le_mul hR4 hfix2'
        _ = 8 := by norm_num
    omega

theorem rho_thompsonJ (h : A5BaumHyp F T) (j : ↥Y) (hj : (j : G) ∈ thompsonJ T) :
    InE4 (F.ρ j) := by
  let E' : Subgroup G := (e4Sub.comap F.ρ).map Y.subtype
  have hJ : thompsonJ T ≤ E' := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    exact ⟨⟨a, hA.1.trans h.TY ha⟩, h.rho_offender hA ⟨a, hA.1.trans h.TY ha⟩ ha, rfl⟩
  obtain ⟨j', hj', hjj'⟩ := hJ hj
  have : j' = j := Subtype.ext hjj'
  rw [← this]
  exact hj'

omit [Finite G] in
theorem exists_offender (h : A5BaumHyp F T) :
    ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set G) := by
  by_contra hcon
  push Not at hcon
  exact h.J (iSup₂_le fun A hA => hcon A hA)

theorem offender_eq (h : A5BaumHyp F T) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAW : ¬ A ≤ Subgroup.centralizer (W : Set G)) :
    (∃ a : ↥Y, (a : G) ∈ A ∧ (F.ρ a = swap 0 1 ∨ F.ρ a = swap 2 3)) ∧
      Nat.card W = (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A *
        Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := by
  classical
  have hAY : A ≤ Y := hA.1.trans h.TY
  have hineq := card_le_relIndex_mul_card h.el h.WT hA
  rw [F.relIndex_eq_card_range hAY] at hineq ⊢
  rw [F.card_W] at hineq ⊢
  have hR4 := card_range_le_four F hAY hA.2.1
  have hRE : (F.ρOn hAY).range ≤ e4Sub := by
    rintro _ ⟨a, rfl⟩
    exact h.rho_offender hA (Subgroup.inclusion hAY a) a.2
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a₀ : ↥Y, (a₀ : G) ∈ A ∧ F.ρ a₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAW
    intro a ha
    have := hcon ⟨a, hAY ha⟩ ha
    exact (F.ρ_eq_one_iff _).1 this
  by_cases hboth : (∃ a₁ : ↥Y, (a₁ : G) ∈ A ∧ F.ρ a₁ = swap 0 1) ∧
      (∃ a₂ : ↥Y, (a₂ : G) ∈ A ∧ F.ρ a₂ = swap 2 3)
  · obtain ⟨⟨a₁, ha₁A, ha₁⟩, ⟨a₂, ha₂A, ha₂⟩⟩ := hboth
    have hfix := F.card_fix_le_two (A := A) ha₁A ha₂A
    rw [ha₁, ha₂, d5_fix_card_E4] at hfix
    refine ⟨⟨a₁, ha₁A, Or.inl ha₁⟩, le_antisymm hineq ?_⟩
    calc _ ≤ 4 * 4 := Nat.mul_le_mul hR4 hfix
      _ = 16 := by norm_num
  ·
    have hR2 : Nat.card (F.ρOn hAY).range ≤ 2 := by
      have hdvd : Nat.card (F.ρOn hAY).range ∣ 4 := card_e4Sub ▸ Subgroup.card_dvd_of_le hRE
      have hne4 : Nat.card (F.ρOn hAY).range ≠ 4 := by
        intro h4
        apply hboth
        have heq : (F.ρOn hAY).range = e4Sub :=
          Subgroup.eq_of_le_of_card_ge hRE (by rw [h4, card_e4Sub])
        have h01 : swap 0 1 ∈ (F.ρOn hAY).range := by rw [heq]; exact mem_e4Sub.mpr (by decide)
        have h23 : swap 2 3 ∈ (F.ρOn hAY).range := by rw [heq]; exact mem_e4Sub.mpr (by decide)
        obtain ⟨b₁, hb₁⟩ := h01
        obtain ⟨b₂, hb₂⟩ := h23
        exact ⟨⟨Subgroup.inclusion hAY b₁, b₁.2, hb₁⟩, ⟨Subgroup.inclusion hAY b₂, b₂.2, hb₂⟩⟩
      have hle : Nat.card (F.ρOn hAY).range ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hc : Nat.card (F.ρOn hAY).range <;> simp_all
    have ha₀E : InE4 (F.ρ a₀) := h.rho_offender hA a₀ ha₀A
    have hfix := F.card_fix_le (A := A) ha₀A
    have h8 := fixCard1_le_eight _ ha₀E ha₀
    have hprod : Nat.card (F.ρOn hAY).range * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤
        16 := calc _ ≤ 2 * 8 := Nat.mul_le_mul hR2 (hfix.trans h8)
      _ = 16 := by norm_num
    have hgt : 4 < fixCard1 (F.ρ a₀) := by
      by_contra hle
      push Not at hle
      have : Nat.card (F.ρOn hAY).range *
          Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ 8 :=
        calc _ ≤ 2 * 4 := Nat.mul_le_mul hR2 (hfix.trans hle)
          _ = 8 := by norm_num
      omega
    exact ⟨⟨a₀, ha₀A, d5_transposition_of_fix _ ha₀E ha₀ hgt⟩, le_antisymm hineq hprod⟩

theorem le_thompsonJ (h : A5BaumHyp F T) : W ≤ thompsonJ T := by
  obtain ⟨A, hA, hAW⟩ := h.exists_offender
  have heq := (h.offender_eq hA hAW).2
  have hmax := isMaxElemAbelian_sup_of_eq h.el h.WT (isMaxElemAbelian_iff_corank_zero.mp hA)
    (by rw [pow_zero, mul_one]; exact heq)
  exact le_sup_right.trans (le_iSup₂_of_le _ hmax le_rfl)

omit [Finite G] in
theorem T_le_normalizer_thompsonJ (T : Subgroup G) :
    T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)

theorem rho_thompsonJ_surj (h : A5BaumHyp F T) (ε : Perm (Fin 5)) (hε : InE4 ε) :
    ∃ j : ↥Y, (j : G) ∈ thompsonJ T ∧ F.ρ j = ε := by
  obtain ⟨A, hA, hAW⟩ := h.exists_offender
  obtain ⟨a, haA, ha⟩ := (h.offender_eq hA hAW).1
  have hAJ : A ≤ thompsonJ T :=
    le_iSup₂_of_le (f := fun B (_ : IsMaxElemAbelian T B) => B) A hA le_rfl
  have haJ : (a : G) ∈ thompsonJ T := hAJ haA
  obtain ⟨t, htT, ht⟩ := h.DT (swap 0 2 * swap 1 3) (by decide)
  have hctJ : (t : G) * a * (t : G)⁻¹ ∈ thompsonJ T :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_thompsonJ T htT) _).mp haJ
  have hta : t * a * t⁻¹ = (⟨(t : G) * a * (t : G)⁻¹, Y.mul_mem (Y.mul_mem t.2 a.2)
      (Y.inv_mem t.2)⟩ : ↥Y) := rfl
  have hcon := d5_conj_swap (F.ρ t) (by rw [ht]; decide) (by rw [ht]; decide)
  have h01 : ∃ j : ↥Y, (j : G) ∈ thompsonJ T ∧ F.ρ j = swap 0 1 := by
    rcases ha with ha | ha
    · exact ⟨a, haJ, ha⟩
    · refine ⟨t * a * t⁻¹, hctJ, ?_⟩
      rw [map_mul, map_mul, map_inv, ha]
      exact hcon.2
  have h23 : ∃ j : ↥Y, (j : G) ∈ thompsonJ T ∧ F.ρ j = swap 2 3 := by
    rcases ha with ha | ha
    · refine ⟨t * a * t⁻¹, hctJ, ?_⟩
      rw [map_mul, map_mul, map_inv, ha]
      exact hcon.1
    · exact ⟨a, haJ, ha⟩
  obtain ⟨j₁, hj₁, hj₁e⟩ := h01
  obtain ⟨j₂, hj₂, hj₂e⟩ := h23
  rcases (inE4_iff ε).1 hε with rfl | rfl | rfl | rfl
  · exact ⟨1, (thompsonJ T).one_mem, map_one _⟩
  · exact ⟨j₁, hj₁, hj₁e⟩
  · exact ⟨j₂, hj₂, hj₂e⟩
  · refine ⟨j₁ * j₂, (thompsonJ T).mul_mem hj₁ hj₂, ?_⟩
    rw [map_mul, hj₁e, hj₂e]

theorem rho_baum (h : A5BaumHyp F T) (s : ↥Y) (hs : (s : G) ∈ baum T) : InE4 (F.ρ s) := by
  have hsT : (s : G) ∈ T := hs.1
  refine d5_centralizer_E4 _ (h.TD s hsT) ?_
  intro x hx hxE
  obtain ⟨u, rfl⟩ := F.c_surj x hx
  have huJ : (u : G) ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjY : j ∈ Y := (iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hj |> h.TY
    have hju : j * u * j⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (F.le hjY) u).mp u.2
    have h1 := F.equiv ⟨j, hjY⟩ u hju
    rw [hxE _ (h.rho_thompsonJ ⟨j, hjY⟩ hj)] at h1
    have h2 := congrArg Subtype.val (F.c_inj h1)
    simp only at h2
    calc j * (u : G) = j * u * j⁻¹ * j := by group
      _ = u * j := by rw [h2]
  have huE : (u : G) ∈ omegaOneCenterOf (thompsonJ T) := by
    rw [← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨h.WT u.2, huJ⟩, h.el.2 _ u.2⟩
  have hsu : (s : G) * u * (s : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (F.le s.2) u).mp u.2
  rw [← F.equiv s u hsu]
  congr 1
  apply Subtype.ext
  show (s : G) * u * (s : G)⁻¹ = u
  rw [← Subgroup.mem_centralizer_iff.mp hs.2 u huE, mul_inv_cancel_right]

theorem le_baum (h : A5BaumHyp F T) : W ≤ baum T :=
  h.le_thompsonJ.trans (B2F.thompsonJ_le_baum T)

theorem rho_baum_surj (h : A5BaumHyp F T) (ε : Perm (Fin 5)) (hε : InE4 ε) :
    ∃ s : ↥Y, (s : G) ∈ baum T ∧ F.ρ s = ε := by
  obtain ⟨j, hj, hje⟩ := h.rho_thompsonJ_surj ε hε
  exact ⟨j, B2F.thompsonJ_le_baum T hj, hje⟩

end A5BaumHyp

end Baum

end CFSG.Quasithin.H13
