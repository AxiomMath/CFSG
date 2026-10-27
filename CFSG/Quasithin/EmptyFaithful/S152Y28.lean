module

public import CFSG.Quasithin.EmptyFaithful.S152Y27
public import CFSG.Quasithin.EmptyFaithful.S152Y15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem exists_nontrivial_action_of_comm_eq (c3 : Lemma15203Concl T Mc M) :
    ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M),
      r * a * r⁻¹ ≠ a := by
  by_contra hcon
  push Not at hcon
  apply c3.ne_bot
  have hbot : ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha r hr
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have h1 := hcon r hr a ha
    calc a * r = (r * a * r⁻¹) * r := by rw [h1]
      _ = r * a := by group
  exact c3.comm_eq.trans hbot

theorem mul_self_eq_one_of_card_two {B : Type*} [Group B] {X : Subgroup B} (hX : Nat.card X = 2) :
    ∀ x ∈ X, x * x = 1 := by
  intro x hx
  have : (⟨x, hx⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
  rw [hX] at this
  have h2 : x ^ 2 = 1 := by simpa using congrArg Subtype.val this
  rwa [pow_two] at h2

theorem mul_self_eq_one_of_mem_Tb (h : Data T Mc M)
    (h4 : ¬ 4 ∣ Nat.card (autOn M (V154 T Mc M))) :
    ∀ x ∈ autOn T (V154 T Mc M), x * x = 1 := by
  have hsyl := isSylowTwoOf_Tb h
  have hcard : Nat.card (autOn T (V154 T Mc M)) ≤ 2 :=
    S152N.card_le_two_of_dvd hsyl.2.1 (Subgroup.card_dvd_of_le hsyl.1) h4
  intro x hx
  have hpos : 0 < Nat.card (autOn T (V154 T Mc M)) := Nat.card_pos
  have hpow : (⟨x, hx⟩ : autOn T (V154 T Mc M)) ^ Nat.card (autOn T (V154 T Mc M)) = 1 :=
    pow_card_eq_one'
  interval_cases hc : Nat.card (autOn T (V154 T Mc M))
  · have : x = 1 := by simpa using congrArg Subtype.val hpow
    rw [this, mul_one]
  · have h2 : x ^ 2 = 1 := by simpa using congrArg Subtype.val hpow
    rwa [pow_two] at h2

theorem isY1_Y (h : Data T Mc M) (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) {n : ℕ} (hn : Odd n)
    (hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ n = 1)
    (hquot : IsSmallQuot152 (yOf152 T Mc M ⊔ rcOf Mc M))
    (hunique : IsUniqueM (yOf152 T Mc M ⊔ T) M) : IsY1 T Mc M (yOf152 T Mc M) :=
  isY1_of_star h le_rfl (T_le_normalizer_yOf T Mc M)
    (by unfold yOf152; exact (A4.oTwoUpper_oTwoUpper _).symm) hquot hK
    (odd_orderOf_of_inf_ker_bot h h.yOf_le_M hn hK hex) hunique

theorem isSmallQuot_of_Y_three (h : Data T Mc M) (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥)
    (hcard : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3)
    (hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M),
      r * a * r⁻¹ ≠ a) :
    IsSmallQuot152 (yOf152 T Mc M ⊔ rcOf Mc M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := quot_dihedral_of_star h h.yOf_le_M
    (h.rc_le_T.trans (T_le_normalizer_yOf T Mc M)) (by norm_num) hK hcard hRe hact
  obtain ⟨d⟩ := S152N2.nonempty_d3_equiv_perm
  exact Or.inl ⟨e.trans d⟩

theorem isUniqueM_Y_of_five (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) {n : ℕ} (hn : Odd n)
    (hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ n = 1)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M),
      r * a * r⁻¹ ≠ a) : IsUniqueM (yOf152 T Mc M ⊔ T) M :=
  isUniqueM_of_five h h5 hs h.yOf_le_M
    (not_le_Mc (h.rc_le_T.trans (T_le_normalizer_yOf T Mc M))
      (odd_orderOf_of_inf_ker_bot h h.yOf_le_M hn hK hex)
      (exists_nontrivial_action h h.yOf_le_M hact))

theorem exists_Y1_iii (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205)
    (c3 : Lemma15203Concl T Mc M) (hiii : Case15203iii T Mc M) : ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨-, hRc2, -, hcard3, hcent, -⟩ := hiii
  have hK := imageOTwoQuot_inf_ker_eq_bot h hcent
  have hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ 3 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(autOn (yOf152 T Mc M) (V154 T Mc M))) (x := ⟨a, ha⟩)
    rw [hcard3] at this
    simpa using congrArg Subtype.val this
  have hact := exists_nontrivial_action_of_comm_eq c3
  exact ⟨yOf152 T Mc M, isY1_Y h hK (by decide) hex
    (isSmallQuot_of_Y_three h hK hcard3 (mul_self_eq_one_of_card_two hRc2) hact)
    (isUniqueM_Y_of_five hs h h5 hK (by decide) hex hact)⟩

theorem exists_Y1_small_three (h : Data T Mc M) (c3 : Lemma15203Concl T Mc M)
    (hi : Case15203i T Mc M) (e : ↥(mBar0 T Mc M) ≃* DihedralGroup 3)
    (h4 : ¬ 4 ∣ Nat.card (autOn M (V154 T Mc M))) : ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨hYb, hcent, -⟩ := hi
  have hshape := dihedral_shape (n := 3) (by decide) e
  have hcard3 : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3 := by
    rw [hYb]
    exact hshape.1
  have hK := imageOTwoQuot_inf_ker_eq_bot h hcent
  have hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ 3 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(autOn (yOf152 T Mc M) (V154 T Mc M))) (x := ⟨a, ha⟩)
    rw [hcard3] at this
    simpa using congrArg Subtype.val this
  have hact := exists_nontrivial_action_of_comm_eq c3
  have hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1 := fun x hx =>
    mul_self_eq_one_of_mem_Tb h h4 x (A4.autOn_mono h.rc_le_T hx)
  exact ⟨yOf152 T Mc M, isY1_Y h hK (by decide) hex (isSmallQuot_of_Y_three h hK hcard3 hRe hact)
    (c3.unique hYb)⟩

theorem exists_Y1_five (hFr : S152N2.Frobenius20IsSz2) (h : Data T Mc M)
    (c3 : Lemma15203Concl T Mc M) (hi : Case15203i T Mc M)
    (hc : Case1517Five T M (V154 T Mc M) (mBar0 T Mc M)) :
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  have hinvM := involution_mem_mBar0 h (Or.inr (Or.inr hc))
  obtain ⟨hYb, hcent, -⟩ := hi
  obtain ⟨-, ⟨e⟩, hT, -⟩ := hc
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcardE, -, hinvD⟩ := dihedral_shape (n := 5) (by decide) e
  have hcard5 : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 5 := by
    rw [hYb]
    exact hcardE
  have hK := imageOTwoQuot_inf_ker_eq_bot h hcent
  have hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ 5 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(autOn (yOf152 T Mc M) (V154 T Mc M))) (x := ⟨a, ha⟩)
    rw [hcard5] at this
    simpa using congrArg Subtype.val this
  have hact := exists_nontrivial_action_of_comm_eq c3
  have hRY : rcOf Mc M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
    h.rc_le_T.trans (T_le_normalizer_yOf T Mc M)
  have hRT : autOn (rcOf Mc M) (V154 T Mc M) ≤ autOn T (V154 T Mc M) :=
    A4.autOn_mono h.rc_le_T
  have hquot : IsSmallQuot152 (yOf152 T Mc M ⊔ rcOf Mc M) := by
    rcases hT with hT | hT
    · obtain ⟨f⟩ := hT
      have hTc : Nat.card (autOn T (V154 T Mc M)) = 2 := by
        rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card]
        rfl
      obtain ⟨e'⟩ := quot_dihedral_of_star h h.yOf_le_M hRY (p := 5) (by norm_num) hK hcard5
        (fun x hx => mul_self_eq_one_of_card_two hTc x (hRT hx)) hact
      exact Or.inr (Or.inl ⟨e'⟩)
    · obtain ⟨f⟩ := hT
      have hTc : Nat.card (autOn T (V154 T Mc M)) = 4 := by
        rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card]
        rfl
      by_cases hR4 : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) = 4
      ·
        have hRTe : autOn (rcOf Mc M) (V154 T Mc M) = autOn T (V154 T Mc M) :=
          Subgroup.eq_of_le_of_card_ge hRT (by rw [hR4, hTc])
        set g : ↥(autOn T (V154 T Mc M)) := f.symm (Multiplicative.ofAdd 1) with hg
        have hg4 : orderOf (g : MulAut (V154 T Mc M)) = 4 := by
          rw [Subgroup.orderOf_coe, hg, MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf,
            ZMod.addOrderOf_one]
        have hgR : (g : MulAut (V154 T Mc M)) ∈ autOn (rcOf Mc M) (V154 T Mc M) := by
          rw [hRTe]
          exact g.2
        have hg2T : (g : MulAut (V154 T Mc M)) ^ 2 ∈ autOn T (V154 T Mc M) :=
          (autOn T (V154 T Mc M)).pow_mem g.2 2
        have hg2o : orderOf ((g : MulAut (V154 T Mc M)) ^ 2) = 2 := by
          rw [orderOf_pow_of_dvd (x := (g : MulAut (V154 T Mc M))) (by norm_num)
            (by rw [hg4]; norm_num), hg4]
        have hg2one : ((g : MulAut (V154 T Mc M)) ^ 2) ^ 2 = 1 := by
          have := pow_orderOf_eq_one ((g : MulAut (V154 T Mc M)) ^ 2)
          rwa [hg2o] at this
        have hg2ne : (g : MulAut (V154 T Mc M)) ^ 2 ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hg2o
          omega
        have hg2M := hinvM _ hg2T hg2one hg2ne
        have hinv : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M),
            (g : MulAut (V154 T Mc M)) ^ 2 * a * ((g : MulAut (V154 T Mc M)) ^ 2)⁻¹ = a⁻¹ := by
          intro a ha
          rw [hYb] at ha
          exact hinvD _ hg2M hg2o a ha
        obtain ⟨e'⟩ := quot_sz_of_star h hFr h.yOf_le_M hRY hK hcard5 hR4 hgR hg4 hinv
        exact Or.inr (Or.inr ⟨e'⟩)
      ·
        have hdvd : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) ∣ 4 := by
          rw [← hTc]
          exact Subgroup.card_dvd_of_le hRT
        have hne1 : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) ≠ 1 := by
          intro h1
          obtain ⟨r, hr, a, ha, hra⟩ := hact
          have hbot := Subgroup.card_eq_one.mp h1
          rw [hbot, Subgroup.mem_bot] at hr
          apply hra
          rw [hr]
          simp
        have hRc2 : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) = 2 := by
          have hle : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
          have hpos : 0 < Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) := Nat.card_pos
          interval_cases hn : Nat.card (autOn (rcOf Mc M) (V154 T Mc M))
          · exact absurd rfl hne1
          · rfl
          · omega
          · exact absurd rfl hR4
        obtain ⟨e'⟩ := quot_dihedral_of_star h h.yOf_le_M hRY (p := 5) (by norm_num) hK hcard5
          (mul_self_eq_one_of_card_two hRc2) hact
        exact Or.inr (Or.inl ⟨e'⟩)
  exact ⟨yOf152 T Mc M, isY1_Y h hK (by decide) hex hquot (c3.unique hYb)⟩

end S152Y

end CFSG.Quasithin
