module

public import CFSG.Quasithin.Background.C124YZClass

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Quasithin Equiv Equiv.Perm

instance instFiniteDM (m : ℕ) : Finite (DM m) := by
  have h1 : Finite (FFModel.symDn m).Amb :=
    inferInstanceAs (Finite (Multiplicative (Fin m → ZMod 2)))
  have h2 : Finite ↥(FFModel.symDn m).sec := Subtype.finite
  exact Quotient.finite _

section Six

theorem dAct_faithful {m : ℕ} (hm : 5 ≤ m) (ρ : Perm (Fin m)) (h : ∀ q, dAct m ρ q = q) :
    ρ = 1 := by
  refine G64.symDn_faithful hm ρ fun x hx => ?_
  have h1 := h (QuotientGroup.mk ⟨x, hx⟩)
  have h2 : (QuotientGroup.mk ⟨(FFModel.symDn m).act ρ x, G6.permAct_mem_coreMod ρ hx⟩ :
      DM m) = QuotientGroup.mk ⟨x, hx⟩ := h1
  have h3 := QuotientGroup.eq.1 h2
  rw [Subgroup.mem_subgroupOf] at h3
  have h3' : ((FFModel.symDn m).act ρ x)⁻¹ * x ∈ (FFModel.symDn m).ker := h3
  have h4 := Subgroup.inv_mem _ h3'
  convert h4 using 1
  rw [mul_inv_rev, inv_inv, mul_comm]

theorem exists_swap_of_card_le_two {m : ℕ} {H : Subgroup (Perm (Fin m))} (hH : IsSwapGroup H)
    (hne : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ x y : Fin m, x ≠ y ∧ swap x y ∈ H ∧ ∀ d ∈ H, d = 1 ∨ d = swap x y := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcard2 : Nat.card H = 2 :=
    le_antisymm hcard ((Subgroup.one_lt_card_iff_ne_bot H).2 hne)
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ x := by
    by_contra h
    push Not at h
    exact hb1' (Equiv.ext h)
  have hsw : swap x (b x) ∈ H := (hH b hb x).resolve_left hx
  have hsw1 : swap x (b x) ≠ 1 := fun h => hx ((swap_eq_one_iff.1 h).symm)
  refine ⟨x, b x, Ne.symm hx, hsw, fun d hd => ?_⟩
  by_contra hcon
  push Not at hcon
  exact G6.false_of_card_two hcard2 hd hsw hcon.1 hsw1 hcon.2

theorem fixed_iff_of_swap {m : ℕ} {H : Subgroup (Perm (Fin m))} {x y z : Fin m} (hxy : x ≠ y)
    (hsw : swap x y ∈ H) (hall : ∀ d ∈ H, d = 1 ∨ d = swap x y) :
    (∀ d ∈ H, d z = z) ↔ z ≠ x ∧ z ≠ y := by
  constructor
  · intro h
    have := h _ hsw
    refine ⟨fun hzx => ?_, fun hzy => ?_⟩
    · rw [hzx, swap_apply_left] at this
      exact hxy this.symm
    · rw [hzy, swap_apply_right] at this
      exact hxy this
  · rintro ⟨hzx, hzy⟩ d hd
    rcases hall d hd with rfl | rfl
    · rfl
    · exact swap_apply_of_ne_of_ne hzx hzy

theorem isSwap_of_index_le_two {m : ℕ} (hm : 5 ≤ m) {b : Perm (Fin m)} (hb1 : b ≠ 1)
    (hbb : b * b = 1) (hidx : (fixAct (dAct m) (Subgroup.zpowers b)).index ≤ 2) :
    b.IsSwap := by
  classical
  have hinj : Function.Injective (dAct m) := by
    rw [injective_iff_map_eq_one]
    exact fun ρ h => dAct_faithful hm ρ fun q => by rw [h]; rfl
  set a : MulAut (DM m) := dAct m b with ha
  have haa : a * a = 1 := by rw [ha, ← map_mul, hbb, map_one]
  have hmove : ∃ q, a q ≠ q := by
    by_contra h
    push Not at h
    exact hb1 (dAct_faithful hm b h)
  let φ : DM m →* DM m :=
    { toFun := fun q => a q * q⁻¹
      map_one' := by simp
      map_mul' := fun q r => by
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hker : φ.ker = fixAct (dAct m) (Subgroup.zpowers b) := by
    ext q
    rw [MonoidHom.mem_ker]
    show a q * q⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    constructor
    · intro h x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rcases zpow_eq_one_or_self' hbb k with h1 | h1
      · rw [h1, map_one]
        rfl
      · rw [h1]
        exact h
    · intro h
      exact h b (Subgroup.mem_zpowers b)
  have hcomm_le : commV (Subgroup.zpowers a) ≤ φ.range := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_eq_one_or_self' haa k with h1 | h1
    · rw [h1]
      exact ⟨1, by simp⟩
    · rw [h1]
      exact ⟨v, rfl⟩
  have hrange : Nat.card φ.range ≤ 2 := by
    rw [← Subgroup.index_ker, hker]
    exact hidx
  have hc2 : Nat.card (commV (Subgroup.zpowers a)) = 2 := by
    refine le_antisymm ((Subgroup.card_le_of_le hcomm_le).trans hrange) ?_
    obtain ⟨q, hq⟩ := hmove
    have hmem : a q * q⁻¹ ∈ commV (Subgroup.zpowers a) :=
      G6.mem_commV_of_mem (Subgroup.mem_zpowers a) q
    have hne : commV (Subgroup.zpowers a) ≠ ⊥ := fun h => by
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hq hmem
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  let X : Subgroup (MulAut (DM m)) := (dAct m).range
  let θ : ↥X ≃* Perm (Fin m) := (MonoidHom.ofInjective hinj).symm
  have hnorm : ((FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec).Normal :=
    Subgroup.normal_of_isMulCommutative _
  let β : ↥(G6.coreMod m) →* DM m :=
    QuotientGroup.mk' ((FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec)
  have hequiv : ∀ (x : ↥X) (u : ↥(G6.coreMod m)),
      β (G6.coreAct m (θ x) u) = (x : MulAut (DM m)) (β u) := by
    intro x u
    have hx : dAct m (θ x) = (x : MulAut (DM m)) := MonoidHom.apply_ofInjective_symm hinj x
    rw [← hx]
    rfl
  have hkerβ : β.ker ≤ G6.natKer m := by
    intro u hu
    have h1 : u ∈ (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec :=
      (QuotientGroup.eq_one_iff
        (N := (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec) u).1 hu
    exact (Subgroup.mem_subgroupOf.1 h1).1
  have haX : a ∈ X := ⟨b, rfl⟩
  have hswap := G6.isSwap_of_card_commV_eq_two hm θ β hequiv hkerβ haX hc2
  have hθ : θ ⟨a, haX⟩ = b := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (MonoidHom.ofInjective_apply hinj).symm
  rwa [hθ] at hswap

end Six

section SixFacts

@[expose] noncomputable def modelFactsSix : ModelFacts 6 (DM 6) (dAct 6) 2 where
  pairModel := pairModelDM (by norm_num)
  index_ge B hsq hcomm hcard := by
    by_cases hB : B = ⊥
    · rw [hB, Subgroup.card_bot]
      exact Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
    · have h2 : Nat.card B = 2 := le_antisymm hcard ((Subgroup.one_lt_card_iff_ne_bot B).2 hB)
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      obtain ⟨q, hq⟩ : ∃ q, dAct 6 b q ≠ q := by
        by_contra h
        push Not at h
        exact hb1' (dAct_faithful (by norm_num) b h)
      have hne : fixAct (dAct 6) B ≠ ⊤ := fun h =>
        hq ((h ▸ Subgroup.mem_top q : q ∈ fixAct (dAct 6) B) b hb)
      have h1 : (fixAct (dAct 6) B).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
      have h0 : (fixAct (dAct 6) B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
  isSwapGroup B hsq hcomm hne hcard hidx := by
    have h2 : Nat.card B = 2 := le_antisymm hcard ((Subgroup.one_lt_card_iff_ne_bot B).2 hne)
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hall : ∀ d ∈ B, d = 1 ∨ d = b := by
      intro d hd
      by_contra hcon
      push Not at hcon
      exact G6.false_of_card_two h2 hd hb hcon.1 hb1' hcon.2
    have hzp : Subgroup.zpowers b = B := by
      refine le_antisymm (Subgroup.zpowers_le.2 hb) fun d hd => ?_
      rcases hall d hd with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hsw := isSwap_of_index_le_two (by norm_num) hb1' (hsq b hb)
      (by rw [hzp]; omega)
    obtain ⟨x, y, hxy, rfl⟩ := hsw
    intro d hd z
    rcases hall d hd with rfl | rfl
    · exact Or.inl rfl
    · by_cases h : swap x y z = z
      · exact Or.inl h
      · right
        have hz : z = x ∨ z = y := by
          by_contra hcon
          push Not at hcon
          exact h (swap_apply_of_ne_of_ne hcon.1 hcon.2)
        rcases hz with rfl | rfl
        · rw [swap_apply_left]
          exact hb
        · rw [swap_apply_right, swap_comm]
          exact hb
  exists_fixed H hH hp hcard := by
    by_cases hne : H = ⊥
    · exact ⟨0, fun d hd => by rw [hne, Subgroup.mem_bot] at hd; rw [hd]; rfl⟩
    · obtain ⟨x, y, hxy, hsw, hall⟩ := exists_swap_of_card_le_two hH hne hcard
      obtain ⟨c, hcx, hcy, -, -⟩ := exists_not_mem_four (by norm_num : 5 ≤ 6) x y x y
      exact ⟨c, (fixed_iff_of_swap hxy hsw hall).2 ⟨hcx, hcy⟩⟩
  trichotomy H hH hp hne hcard x hx := by
    obtain ⟨u, v, huv, hsw, hall⟩ := exists_swap_of_card_le_two hH hne hcard
    left
    obtain ⟨f₁, h1u, h1v, h1x, -⟩ := exists_not_mem_four (by norm_num : 5 ≤ 6) u v x x
    obtain ⟨f₂, h2u, h2v, h2x, h2f⟩ := exists_not_mem_four (by norm_num : 5 ≤ 6) u v x f₁
    exact ⟨f₁, f₂, h1x, h2x, fun h => h2f h.symm,
      (fixed_iff_of_swap huv hsw hall).2 ⟨h1u, h1v⟩,
      (fixed_iff_of_swap huv hsw hall).2 ⟨h2u, h2v⟩⟩

end SixFacts

end CFSG.Quasithin.C124.YZ
