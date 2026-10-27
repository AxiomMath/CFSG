module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.OrderThreeActionTwoGroup
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3ClassicalSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup.X1
  Subgroup

private theorem mul_ne_one_of_comm {G : Type} [Group G] {a b : G}
    (ha : a ^ 3 = 1) (hba : ∀ j < 3, b ≠ a ^ j) : a * b ≠ 1 := by
  intro h
  have hb_eq : b = a ^ 2 := by
    have ha2 : a ^ 2 = a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      rw [← pow_succ, show 2 + 1 = 3 by norm_num, ha]
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ := by rw [h, mul_one]
      _ = a ^ 2 := ha2.symm
  exact hba 2 (by norm_num) hb_eq

private theorem mul_sq_ne_one_of_comm {G : Type} [Group G] {a b : G}
    (hb : b ^ 3 = 1) (hba : ∀ j < 3, b ≠ a ^ j) : a * b ^ 2 ≠ 1 := by
  intro h
  have hb2 : (b ^ 2)⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one]
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, hb]
  have ha_eq_b : a = b := by
    calc a = a * b ^ 2 * (b ^ 2)⁻¹ := by group
      _ = (b ^ 2)⁻¹ := by rw [h, one_mul]
      _ = b := hb2
  exact hba 1 (by norm_num) (by simpa using ha_eq_b.symm)

private theorem b_eq_sq_sq {G : Type} [Group G] {b : G} (hb : b ^ 3 = 1) :
    b = (b ^ 2) ^ 2 := by
  calc b = b ^ 4 := by rw [show 4 = 3 + 1 by norm_num, pow_succ, hb, one_mul]
    _ = (b ^ 2) ^ 2 := by group

private theorem mul_sq_mul_inv_eq {G : Type} [Group G] {a b : G} (hab : a * b = b * a) :
    b = a * b ^ 2 * (a * b)⁻¹ := by
  rw [mul_inv_rev]
  symm
  calc a * b ^ 2 * (b⁻¹ * a⁻¹) = a * b * a⁻¹ := by group
    _ = b * a * a⁻¹ := by rw [hab]
    _ = b := by group

private theorem b_not_mem_zpowers_a {G : Type} [Group G] [Finite G] {a b : G}
    (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (hba : ∀ j < 3, b ≠ a ^ j) :
    b ∉ Subgroup.zpowers a := by
  classical
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  intro hbA
  rw [CFSG.EvenSmallLie.Child3.SelK3Classical.mem_zpowers_of_orderOf_eq_three hao] at hbA
  rcases hbA with h | h | h
  · exact hb1 h
  · exact hba 1 (by norm_num) (by simpa using h)
  · exact hba 2 (by norm_num) h

private theorem a_not_mem_zpowers_b {G : Type} [Group G] [Finite G] {a b : G}
    (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hba : ∀ j < 3, b ≠ a ^ j) :
    a ∉ Subgroup.zpowers b := by
  classical
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  intro haB
  rw [CFSG.EvenSmallLie.Child3.SelK3Classical.mem_zpowers_of_orderOf_eq_three hbo] at haB
  rcases haB with h | h | h
  · exact ha1 h
  · exact hba 1 (by norm_num) (by simpa using h.symm)
  · have hb_eq : b = a ^ 2 := by
      calc b = (b ^ 2) ^ 2 := b_eq_sq_sq hb
        _ = a ^ 2 := by rw [← h]
    exact hba 2 (by norm_num) hb_eq

private theorem zpowers_a_ne {G : Type} [Group G] [Finite G] {a b : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hba : ∀ j < 3, b ≠ a ^ j) :
    Subgroup.zpowers a ≠ Subgroup.zpowers b ∧
    Subgroup.zpowers a ≠ Subgroup.zpowers (a * b) ∧
    Subgroup.zpowers a ≠ Subgroup.zpowers (a * b ^ 2) := by
  have hb_not_mem_a := b_not_mem_zpowers_a ha ha1 hba
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hb_not_mem_a
    rw [h]
    exact Subgroup.mem_zpowers b
  · intro h
    apply hb_not_mem_a
    have h1 : a⁻¹ * (a * b) ∈ Subgroup.zpowers a :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) (by
        rw [h]; exact Subgroup.mem_zpowers (a * b))
    simpa using h1
  · intro h
    apply hb_not_mem_a
    have h1 : a⁻¹ * (a * b ^ 2) ∈ Subgroup.zpowers a :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) (by
        rw [h]; exact Subgroup.mem_zpowers (a * b ^ 2))
    have hb2 : b ^ 2 ∈ Subgroup.zpowers a := by simpa using h1
    rw [b_eq_sq_sq hb]
    exact Subgroup.pow_mem _ hb2 2

private theorem zpowers_b_ne {G : Type} [Group G] [Finite G] {a b : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j) :
    Subgroup.zpowers b ≠ Subgroup.zpowers (a * b) ∧
    Subgroup.zpowers b ≠ Subgroup.zpowers (a * b ^ 2) ∧
    Subgroup.zpowers (a * b) ≠ Subgroup.zpowers (a * b ^ 2) := by
  classical
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hacard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hcomm : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hcomm.mul_pow, ha, hb, mul_one]
  have hab_card : Nat.card (Subgroup.zpowers (a * b)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hab3 (mul_ne_one_of_comm ha hba)]
  have hb_not_mem_a := b_not_mem_zpowers_a ha ha1 hba
  have ha_not_mem_b := a_not_mem_zpowers_b hb ha1 hba
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : a * b * b⁻¹ ∈ Subgroup.zpowers b :=
      Subgroup.mul_mem _ (by rw [h]; exact Subgroup.mem_zpowers (a * b))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
    have ha_mem_b : a ∈ Subgroup.zpowers b := by simpa [mul_assoc] using h1
    exact ha_not_mem_b ha_mem_b
  · intro h
    have hab2_mem_b : a * b ^ 2 ∈ Subgroup.zpowers b := by
      rw [h]
      exact Subgroup.mem_zpowers (a * b ^ 2)
    have h1 : a * b ^ 2 * (b ^ 2)⁻¹ ∈ Subgroup.zpowers b :=
      Subgroup.mul_mem _ hab2_mem_b
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) 2))
    have ha_mem_b : a ∈ Subgroup.zpowers b := by simpa using h1
    exact ha_not_mem_b ha_mem_b
  · intro h
    have hb_eq := mul_sq_mul_inv_eq hab
    have hc_mem : a * b ∈ Subgroup.zpowers (a * b) := Subgroup.mem_zpowers _
    have hab2_mem : a * b ^ 2 ∈ Subgroup.zpowers (a * b) := by
      rw [h]
      exact Subgroup.mem_zpowers (a * b ^ 2)
    have hb_mem_c : b ∈ Subgroup.zpowers (a * b) := by
      have hmem : a * b ^ 2 * (a * b)⁻¹ ∈ Subgroup.zpowers (a * b) :=
        Subgroup.mul_mem _ hab2_mem (Subgroup.inv_mem _ hc_mem)
      convert hmem using 2
    have ha_mem_c : a ∈ Subgroup.zpowers (a * b) := by
      have h2 : a * b * b⁻¹ ∈ Subgroup.zpowers (a * b) :=
        Subgroup.mul_mem _ hc_mem (Subgroup.inv_mem _ hb_mem_c)
      simpa [mul_assoc] using h2
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers (a * b) :=
      Subgroup.zpowers_le.mpr ha_mem_c
    have heq : Subgroup.zpowers a = Subgroup.zpowers (a * b) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hacard, hab_card])
    apply hb_not_mem_a
    rw [heq]
    exact hb_mem_c

private theorem zpowers_four_ne {G : Type} [Group G] [Finite G] {a b : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j) :
    Subgroup.zpowers a ≠ Subgroup.zpowers b ∧
    Subgroup.zpowers a ≠ Subgroup.zpowers (a * b) ∧
    Subgroup.zpowers a ≠ Subgroup.zpowers (a * b ^ 2) ∧
    Subgroup.zpowers b ≠ Subgroup.zpowers (a * b) ∧
    Subgroup.zpowers b ≠ Subgroup.zpowers (a * b ^ 2) ∧
    Subgroup.zpowers (a * b) ≠ Subgroup.zpowers (a * b ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := zpowers_a_ne ha hb ha1 hba
  obtain ⟨h4, h5, h6⟩ := zpowers_b_ne ha hb ha1 hab hba
  exact ⟨h1, h2, h3, h4, h5, h6⟩

private theorem fixV_zpowers_eq_sup_inf_ker {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {g : MulAut W} (hgA : g ∈ A)
    (hsup : fixV A ⊔ (normHom A).ker = ⊤) :
    fixV (Subgroup.zpowers g) =
      fixV A ⊔ (fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) := by
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ fixV A ⊔ (normHom A).ker := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨u, hu, k, hk, huk⟩ := Subgroup.mem_sup.1 hw'
    have hgu : g u = u := mem_fixV.1 hu g hgA
    have hgw : g w = w := mem_fixV_zpowers.1 hw
    have hkD : k ∈ fixV (Subgroup.zpowers g) := by
      rw [mem_fixV_zpowers]
      calc g k = g (u⁻¹ * w) := by rw [← huk, inv_mul_cancel_left]
        _ = (g u)⁻¹ * g w := by rw [map_mul, map_inv]
        _ = u⁻¹ * w := by rw [hgu, hgw]
        _ = k := by rw [← huk, inv_mul_cancel_left]
    rw [← huk]
    exact Subgroup.mem_sup.2 ⟨u, hu, k, Subgroup.mem_inf.2 ⟨hkD, hk⟩, rfl⟩
  · refine sup_le ?_ ?_
    · exact fun u hu => CFSG.QuasithinUnique.Setup.X1.fixV_anti
        (Subgroup.zpowers_le.mpr hgA) hu
    · exact fun v hv => hv.1

theorem index_mul_card_inf_ker_eq {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {g : MulAut W} (hgA : g ∈ A)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥)
    (hcard : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W) :
    (fixV (Subgroup.zpowers g)).index *
        Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) =
      Nat.card ↥(normHom A).ker := by
  have hsup : fixV A ⊔ (normHom A).ker = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (H := fixV A ⊔ (normHom A).ker) ?_
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV A) (normHom A).ker
      (fun _ _ _ _ => mul_comm _ _)).1
    rw [hfix, Subgroup.card_bot, mul_one, hcard] at h
    exact h
  have hdecomp := fixV_zpowers_eq_sup_inf_ker hgA hsup
  have hinf : fixV A ⊓ (fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) = ⊥ := by
    refine le_bot_iff.1 ?_
    calc fixV A ⊓ (fixV (Subgroup.zpowers g) ⊓ (normHom A).ker)
        ≤ fixV A ⊓ (normHom A).ker := inf_le_inf_left _ inf_le_right
      _ = ⊥ := hfix
  have hcardD : Nat.card ↥(fixV (Subgroup.zpowers g)) =
      Nat.card ↥(fixV A) * Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) := by
    have hdecomp_card : Nat.card ↥(fixV (Subgroup.zpowers g)) =
        Nat.card ↥(fixV A ⊔ (fixV (Subgroup.zpowers g) ⊓ (normHom A).ker)) := by
      conv_lhs => rw [hdecomp]
    rw [hdecomp_card]
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV A)
      (fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) (fun _ _ _ _ => mul_comm _ _)).1
    rwa [hinf, Subgroup.card_bot, mul_one] at h
  have hW' : Nat.card ↥(fixV (Subgroup.zpowers g)) * (fixV (Subgroup.zpowers g)).index =
      Nat.card W := Subgroup.card_mul_index _
  rw [hcardD, ← hcard] at hW'
  have h : Nat.card ↥(fixV A) *
      (Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ (normHom A).ker) *
        (fixV (Subgroup.zpowers g)).index) = Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker := by
    rw [← mul_assoc]
    exact hW'
  have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have := Nat.mul_left_cancel hpos h
  rw [mul_comm]
  exact this

private theorem relIndex_eq_three_of_le_of_card {G : Type} [Group G]
    {A D : Subgroup G} (hDA : D ≤ A) (hAcard : Nat.card ↥A = 9)
    (hDcard : Nat.card ↥D = 3) : D.relIndex A = 3 := by
  have h := D.relIndex_mul_card A
  rw [inf_of_le_left hDA, hDcard, hAcard] at h
  omega

private theorem subgroups_sub_ne {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {a b : MulAut W}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j)
    (h0A : Subgroup.zpowers a ≤ A) (h1A : Subgroup.zpowers b ≤ A)
    (h2A : Subgroup.zpowers (a * b) ≤ A) (h3A : Subgroup.zpowers (a * b ^ 2) ≤ A) :
    (Subgroup.zpowers a).subgroupOf A ≠ (Subgroup.zpowers b).subgroupOf A ∧
    (Subgroup.zpowers a).subgroupOf A ≠ (Subgroup.zpowers (a * b)).subgroupOf A ∧
    (Subgroup.zpowers a).subgroupOf A ≠ (Subgroup.zpowers (a * b ^ 2)).subgroupOf A ∧
    (Subgroup.zpowers b).subgroupOf A ≠ (Subgroup.zpowers (a * b)).subgroupOf A ∧
    (Subgroup.zpowers b).subgroupOf A ≠ (Subgroup.zpowers (a * b ^ 2)).subgroupOf A ∧
    (Subgroup.zpowers (a * b)).subgroupOf A ≠
      (Subgroup.zpowers (a * b ^ 2)).subgroupOf A := by
  have hne := zpowers_four_ne (G := MulAut W) ha hb ha1 hab hba
  have hsub_inj : ∀ {X Y : Subgroup (MulAut W)}, X ≤ A → Y ≤ A →
      X.subgroupOf A = Y.subgroupOf A → X = Y := by
    intro X Y hXA hYA h
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hXA, inf_of_le_left hYA] at h
    exact h
  exact ⟨fun h => hne.1 (hsub_inj h0A h1A h),
    fun h => hne.2.1 (hsub_inj h0A h2A h),
    fun h => hne.2.2.1 (hsub_inj h0A h3A h),
    fun h => hne.2.2.2.1 (hsub_inj h1A h2A h),
    fun h => hne.2.2.2.2.1 (hsub_inj h1A h3A h),
    fun h => hne.2.2.2.2.2 (hsub_inj h2A h3A h)⟩

private theorem e9_mem_four {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} (hAp : ∀ x ∈ A, x ^ 3 = 1) (hAcard : Nat.card ↥A = 9)
    {D0 D1 D2 D3 : Subgroup (MulAut W)}
    (hD0A : D0 ≤ A) (hD1A : D1 ≤ A) (hD2A : D2 ≤ A) (hD3A : D3 ≤ A)
    (hD0c : Nat.card ↥D0 = 3) (hD1c : Nat.card ↥D1 = 3)
    (hD2c : Nat.card ↥D2 = 3) (hD3c : Nat.card ↥D3 = 3)
    (hdist : D0.subgroupOf A ≠ D1.subgroupOf A ∧ D0.subgroupOf A ≠ D2.subgroupOf A ∧
      D0.subgroupOf A ≠ D3.subgroupOf A ∧ D1.subgroupOf A ≠ D2.subgroupOf A ∧
      D1.subgroupOf A ≠ D3.subgroupOf A ∧ D2.subgroupOf A ≠ D3.subgroupOf A) :
    ∀ D : Subgroup (MulAut W), D ≤ A → D.relIndex A = 3 →
      D = D0 ∨ D = D1 ∨ D = D2 ∨ D = D3 := by
  classical
  intro D hDA hDrel
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := hdist
  have hDcard : Nat.card ↥D = 3 := by
    have h := D.relIndex_mul_card A
    rw [hDrel, inf_of_le_left hDA] at h
    omega
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
  have hdA : d ∈ A := hDA hdD
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdord : Nat.card ↥(Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hAp d hdA) hd1']
  have h_of_mem : ∀ {E : Subgroup (MulAut W)}, d ∈ E → Nat.card ↥E = 3 → D = E := by
    intro E hdE hE3
    have hzE : Subgroup.zpowers d = E := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdE) ?_
      rw [hdord, hE3]
    have hzD : Subgroup.zpowers d = D := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD) ?_
      rw [hdord, hDcard]
    exact hzD.symm.trans hzE
  have hsub0 : Nat.card ↥(D0.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD0A).toEquiv, hD0c]
  have hsub1 : Nat.card ↥(D1.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD1A).toEquiv, hD1c]
  have hsub2 : Nat.card ↥(D2.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD2A).toEquiv, hD2c]
  have hsub3 : Nat.card ↥(D3.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD3A).toEquiv, hD3c]
  have hcover := CFSG.GroupTheory.exists_mem_of_card_eq_nine_of_four_lines
    (G := ↥A) hAcard hsub0 hsub1 hsub2 hsub3 ⟨h01, h02, h03, h12, h13, h23⟩ ⟨d, hdA⟩
  rcases hcover with h | h | h | h
  · exact Or.inl (h_of_mem ((Subgroup.mem_subgroupOf).1 h) hD0c)
  · exact Or.inr (Or.inl (h_of_mem ((Subgroup.mem_subgroupOf).1 h) hD1c))
  · exact Or.inr (Or.inr (Or.inl (h_of_mem ((Subgroup.mem_subgroupOf).1 h) hD2c)))
  · exact Or.inr (Or.inr (Or.inr (h_of_mem ((Subgroup.mem_subgroupOf).1 h) hD3c)))

private theorem e9_hD {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j)
    (hAp : ∀ x ∈ A, x ^ 3 = 1) (hAcard : Nat.card ↥A = 9) :
    ∀ D : Subgroup (MulAut W),
      (D = Subgroup.zpowers a ∨ D = Subgroup.zpowers b ∨ D = Subgroup.zpowers (a * b) ∨
        D = Subgroup.zpowers (a * b ^ 2)) ↔ D ≤ A ∧ D.relIndex A = 3 := by
  classical
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hcomm : Commute a b := hab
  have h0A : Subgroup.zpowers a ≤ A := by rw [hA]; exact le_sup_left
  have h1A : Subgroup.zpowers b ≤ A := by rw [hA]; exact le_sup_right
  have h2A : Subgroup.zpowers (a * b) ≤ A := by
    rw [hA]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b))
  have h3A : Subgroup.zpowers (a * b ^ 2) ≤ A := by
    rw [hA]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mul_mem_sup (Subgroup.mem_zpowers a)
        (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) 2))
  have h0c : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have h1c : Nat.card ↥(Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb hb1]
  have hab3 : (a * b) ^ 3 = 1 := by rw [hcomm.mul_pow, ha, hb, mul_one]
  have h2c : Nat.card ↥(Subgroup.zpowers (a * b)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hab3 (mul_ne_one_of_comm ha hba)]
  have hb2pow : (b ^ 2) ^ 3 = 1 := by
    calc (b ^ 2) ^ 3 = b ^ (2 * 3) := by rw [pow_mul]
      _ = (b ^ 3) ^ 2 := by rw [show 2 * 3 = 3 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hb, one_pow]
  have h3pow : (a * b ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow, ha, hb2pow, mul_one]
  have h3c : Nat.card ↥(Subgroup.zpowers (a * b ^ 2)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h3pow (mul_sq_ne_one_of_comm hb hba)]
  have h0rel : (Subgroup.zpowers a).relIndex A = 3 :=
    relIndex_eq_three_of_le_of_card h0A hAcard h0c
  have h1rel : (Subgroup.zpowers b).relIndex A = 3 :=
    relIndex_eq_three_of_le_of_card h1A hAcard h1c
  have h2rel : (Subgroup.zpowers (a * b)).relIndex A = 3 :=
    relIndex_eq_three_of_le_of_card h2A hAcard h2c
  have h3rel : (Subgroup.zpowers (a * b ^ 2)).relIndex A = 3 :=
    relIndex_eq_three_of_le_of_card h3A hAcard h3c
  have hdist := subgroups_sub_ne ha hb ha1 hab hba h0A h1A h2A h3A
  intro D
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨h0A, h0rel⟩
    · exact ⟨h1A, h1rel⟩
    · exact ⟨h2A, h2rel⟩
    · exact ⟨h3A, h3rel⟩
  · rintro ⟨hDA, hDrel⟩
    exact e9_mem_four hAp hAcard h0A h1A h2A h3A h0c h1c h2c h3c hdist
      D hDA hDrel

theorem e9_hyperplane_card {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ 3 = 1)
    (hAcard : Nat.card ↥A = 9)
    (hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥) :
    Nat.card ↥(normHom A).ker =
      Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker) *
      Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ (normHom A).ker) *
      Nat.card ↥(fixV (Subgroup.zpowers (a * b)) ⊓ (normHom A).ker) *
      Nat.card ↥(fixV (Subgroup.zpowers (a * b ^ 2)) ⊓ (normHom A).ker) := by
  classical
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    {Subgroup.zpowers a, Subgroup.zpowers b, Subgroup.zpowers (a * b),
      Subgroup.zpowers (a * b ^ 2)}
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = 3 := by
    intro D
    rw [show D ∈ 𝒟 ↔ (D = Subgroup.zpowers a ∨ D = Subgroup.zpowers b ∨
        D = Subgroup.zpowers (a * b) ∨ D = Subgroup.zpowers (a * b ^ 2)) by
      simp [𝒟]]
    exact e9_hD hA ha hb ha1 hab hba hAp hAcard D
  have hKprod := card_eq_prod_card_fixV_inf_hyperplanes (W := W) hW (p := 3)
    (by norm_num) hAc hAp hKinv hfix 𝒟 h𝒟
  rw [hKprod]
  have hne := zpowers_four_ne (G := MulAut W) ha hb ha1 hab hba
  simp only [𝒟]
  rw [Finset.prod_insert (by simp [hne.1, hne.2.1, hne.2.2.1]),
    Finset.prod_insert (by simp [hne.2.2.2.1, hne.2.2.2.2.1]),
    Finset.prod_insert (by simp [hne.2.2.2.2.2]),
    Finset.prod_singleton]
  ring

private theorem eq_of_mul_eq_of_index_eq {i j d e K : ℕ} (hi : 0 < i)
    (h1 : i * d = K) (h2 : j * e = K) (hij : i = j) : d = e := by
  have h : i * d = i * e := by
    calc i * d = K := h1
      _ = j * e := h2.symm
      _ = i * e := by rw [hij]
  exact Nat.mul_left_cancel hi h

private theorem e9_cube_of_prod {i0 i1 i2 i3 c0 c1 c2 c3 K : ℕ}
    (hpos1 : 0 < i1) (hpos2 : 0 < i2) (hpos3 : 0 < i3)
    (hposc : 0 < c0)
    (hrel0 : i0 * c0 = K) (hrel1 : i1 * c1 = K) (hrel2 : i2 * c2 = K)
    (hrel3 : i3 * c3 = K) (h₁ : i1 = i0) (h₂ : i2 = i0) (h₃ : i3 = i0)
    (hprod : K = c0 * c1 * c2 * c3) : i0 = c0 ^ 3 := by
  have hc1eq : c1 = c0 := eq_of_mul_eq_of_index_eq hpos1 hrel1 hrel0 h₁
  have hc2eq : c2 = c0 := eq_of_mul_eq_of_index_eq hpos2 hrel2 hrel0 h₂
  have hc3eq : c3 = c0 := eq_of_mul_eq_of_index_eq hpos3 hrel3 hrel0 h₃
  have hK4 : K = c0 ^ 4 := by rw [hprod, hc1eq, hc2eq, hc3eq]; ring
  have h4 : c0 ^ 4 = i0 * c0 := by rw [← hK4, hrel0]
  have h4' : c0 * c0 ^ 3 = c0 * i0 := by
    rw [show c0 * c0 ^ 3 = c0 ^ 4 by rw [show 4 = 1 + 3 by norm_num, pow_add, pow_one]]
    rw [mul_comm] at h4
    exact h4
  exact (Nat.mul_left_cancel hposc h4').symm

private theorem e9_index_cube {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < 3, b ≠ a ^ j)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ 3 = 1)
    (hAcard : Nat.card ↥A = 9)
    (hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥)
    (hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W)
    (h₁ : (fixV (Subgroup.zpowers b)).index = (fixV (Subgroup.zpowers a)).index)
    (h₂ : (fixV (Subgroup.zpowers (a * b))).index =
      (fixV (Subgroup.zpowers a)).index)
    (h₃ : (fixV (Subgroup.zpowers (a * b ^ 2))).index =
      (fixV (Subgroup.zpowers a)).index) :
    (fixV (Subgroup.zpowers a)).index =
      (Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker)) ^ 3 := by
  classical
  have hga : a ∈ A := by
    rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hgb : b ∈ A := by
    rw [hA]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hgab : a * b ∈ A := by
    rw [hA]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)
  have hgab2 : a * b ^ 2 ∈ A := by
    rw [hA]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a)
      (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) 2)
  have hrel0 := index_mul_card_inf_ker_eq hga hfix hcardK
  have hrel1 := index_mul_card_inf_ker_eq hgb hfix hcardK
  have hrel2 := index_mul_card_inf_ker_eq hgab hfix hcardK
  have hrel3 := index_mul_card_inf_ker_eq hgab2 hfix hcardK
  have hprod := e9_hyperplane_card hW hA ha hb ha1 hab hba hAc hAp hAcard hKinv hfix
  refine e9_cube_of_prod ?_ ?_ ?_ Nat.card_pos hrel0 hrel1 hrel2 hrel3 h₁ h₂ h₃ hprod
  · rw [Subgroup.index_eq_card]; exact Nat.card_pos
  · rw [Subgroup.index_eq_card]; exact Nat.card_pos
  · rw [Subgroup.index_eq_card]; exact Nat.card_pos

private theorem b_mem_stab_fixV_inf_ker {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hab : a * b = b * a) (hbA : b ∈ A)
    (hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker) :
    b ∈ CFSG.Quasithin.stabSub
      (fixV (Subgroup.zpowers a) ⊓ (normHom A).ker) := by
  classical
  have hcomm : Commute a b := hab
  have hcomm_inv : Commute a b⁻¹ := hcomm.inv_right
  have hbinvA : b⁻¹ ∈ A := A.inv_mem hbA
  have hforward_b : ∀ v : W, v ∈ fixV (Subgroup.zpowers a) ⊓ (normHom A).ker →
      b v ∈ fixV (Subgroup.zpowers a) ⊓ (normHom A).ker := by
    intro v hv
    obtain ⟨hvD, hvK⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixV_zpowers]
      have habv : a (b v) = b (a v) := by
        simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f v) hab
      rw [habv, mem_fixV_zpowers.1 hvD]
    · exact hKinv b hbA v hvK
  have hforward_binv : ∀ v : W, v ∈ fixV (Subgroup.zpowers a) ⊓ (normHom A).ker →
      b⁻¹ v ∈ fixV (Subgroup.zpowers a) ⊓ (normHom A).ker := by
    intro v hv
    obtain ⟨hvD, hvK⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixV_zpowers]
      have habv : a (b⁻¹ v) = b⁻¹ (a v) := by
        simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f v) hcomm_inv.eq
      rw [habv, mem_fixV_zpowers.1 hvD]
    · exact hKinv b⁻¹ hbinvA v hvK
  rw [CFSG.Quasithin.mem_stabSub]
  intro v
  constructor
  · intro hv
    have h := hforward_binv (b v) hv
    simpa using h
  · exact hforward_b v

private theorem c_four_pow {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b) (hab : a * b = b * a)
    (hb : b ^ 3 = 1) (hbA : b ∈ A)
    (hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥) :
    ∃ j : ℕ, Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker) = 4 ^ j := by
  classical
  let V : Subgroup W := fixV (Subgroup.zpowers a) ⊓ (normHom A).ker
  have hb_stab := b_mem_stab_fixV_inf_ker hab hbA hKinv
  let bV : MulAut ↥V := CFSG.Quasithin.resHom V ⟨b, hb_stab⟩
  have hbV3 : bV ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨b, hb_stab⟩ : CFSG.Quasithin.stabSub V) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb)
    rw [h3, map_one]
  have hfpf : ∀ v : ↥V, bV v = v → v = 1 := by
    intro v hv
    apply Subtype.ext
    have hbv : b (v : W) = (v : W) := by
      have := congrArg (fun z : ↥V => (z : W)) hv
      simpa [bV, CFSG.Quasithin.resHom_apply] using this
    obtain ⟨hvD, hvK⟩ := Subgroup.mem_inf.1 v.2
    have hvDb : (v : W) ∈ fixV (Subgroup.zpowers b) := by
      rw [mem_fixV_zpowers]
      exact hbv
    have hvA : (v : W) ∈ fixV A := by
      rw [hA, fixV_sup]
      exact Subgroup.mem_inf.2 ⟨hvD, hvDb⟩
    have hmem : (v : W) ∈ fixV A ⊓ (normHom A).ker := Subgroup.mem_inf.2 ⟨hvA, hvK⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hmem
  have hV2 : ∀ v : ↥V, v * v = 1 := fun v => Subtype.ext (by simpa using hW v)
  obtain ⟨j, hj⟩ := exists_card_eq_four_pow (V := ↥V) hV2 hbV3 hfpf
  exact ⟨j, hj⟩

theorem exists_index_eq_two_pow_six_mul_of_e9 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {a b : MulAut W} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < 3, b ≠ a ^ j)
    (h₁ : (fixV (zpowers b)).index = (fixV (zpowers a)).index)
    (h₂ : (fixV (zpowers (a * b))).index = (fixV (zpowers a)).index)
    (h₃ : (fixV (zpowers (a * b ^ 2))).index = (fixV (zpowers a)).index) :
    ∃ j : ℕ, (fixV (zpowers a)).index = 2 ^ (6 * j) := by
  classical
  let A : Subgroup (MulAut W) := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b := rfl
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hcarda : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hao]
  have hcommXA : ∀ x ∈ Subgroup.zpowers a, x * b = b * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute a b from hab) n).eq
  obtain ⟨hAea, hAsupcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (X := Subgroup.zpowers a) (v := b) hcarda hbo
    (b_not_mem_zpowers_a ha ha1 hba) hcommXA
  have hAcard : Nat.card ↥A = 9 := by
    simpa [A] using hAsupcard
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAea.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : ∀ x ∈ A, x ^ 3 = 1 := hAea.2
  have hodd : Odd (Nat.card ↥A) := by rw [hAcard]; norm_num
  have hfix : fixV A ⊓ (normHom A).ker = ⊥ := fixV_inf_ker_normHom hW hodd
  have hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W :=
    card_ker_normHom_mul hW hodd
  have hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker := fun x hx k hk =>
    map_ker_normHom (Subgroup.le_normalizer hx) hk
  have hidx := e9_index_cube hW hA ha hb ha1 hab hba hAc hAp hAcard hKinv hfix hcardK h₁ h₂ h₃
  have hbA : b ∈ A := by
    rw [hA]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  obtain ⟨j, hj⟩ := c_four_pow hW hA hab hb hbA hKinv hfix
  refine ⟨j, ?_⟩
  calc (fixV (Subgroup.zpowers a)).index
      = (Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker)) ^ 3 := hidx
    _ = (4 ^ j) ^ 3 := by rw [hj]
    _ = 4 ^ (j * 3) := by rw [← pow_mul]
    _ = (2 ^ 2) ^ (j * 3) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    _ = 2 ^ (2 * (j * 3)) := by rw [← pow_mul]
    _ = 2 ^ (6 * j) := by congr 1; ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

end
