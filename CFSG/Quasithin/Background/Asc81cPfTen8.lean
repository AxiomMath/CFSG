module

public import CFSG.Quasithin.Background.Asc81cPfBasic

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] {G X Y : Subgroup (MulAut W)}

section Aux

theorem map_conj_map_conj (X : Subgroup (MulAut W)) (y z : MulAut W) :
    (X.map (MulAut.conj z).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      X.map (MulAut.conj (y * z)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem map_conj_one (X : Subgroup (MulAut W)) :
    X.map (MulAut.conj (1 : MulAut W)).toMonoidHom = X := by
  rw [map_one]
  exact Subgroup.map_id X

theorem mem_commSub_map_conj (X : Subgroup (MulAut W)) (y : MulAut W) {u : W}
    (hu : u ∈ commSub (⊤ : Subgroup W) X) :
    y u ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y).toMonoidHom) := by
  rw [commSub_map_conj]
  exact ⟨u, hu, rfl⟩

theorem zpow_apply_eq {a : MulAut W} {u : W} (h : a u = u) (k : ℤ) : (a ^ k) u = u := by
  have h1 : a ∈ MulAction.stabilizer (MulAut W) u := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have h2 := (MulAction.stabilizer (MulAut W) u).zpow_mem h1 k
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2

theorem apply_ne_of_fixes {x : MulAut W} {a b c : W} (ha : x a ≠ a) (hb : x b = b)
    (hc : x c = c) : x (a * b * c) ≠ a * b * c := by
  rw [map_mul, map_mul, hb, hc]
  intro h
  exact ha (mul_right_cancel (mul_right_cancel h))

end Aux

variable [Finite W]

theorem ten_eight (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X) (hY : Hyp101 G Y)
    (hab : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ a ∈ X.map (MulAut.conj y).toMonoidHom,
      ∀ b ∈ X.map (MulAut.conj y').toMonoidHom, a * b = b * a) :
    ∀ y ∈ Y, X.map (MulAut.conj y).toMonoidHom = X := by
  have hXc : ∀ y ∈ Y, Hyp101 G (X.map (MulAut.conj y).toMonoidHom) := fun y hy =>
    (hyp102_map_conj hX (hY.1 hy)).1
  have hX1 : Hyp101 G X := hX.1
  have hfix : ∀ z ∈ Y, ∀ z' ∈ Y,
      X.map (MulAut.conj z).toMonoidHom ≠ X.map (MulAut.conj z').toMonoidHom →
      ∀ v ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj z).toMonoidHom),
        ∀ x ∈ X.map (MulAut.conj z').toMonoidHom, x v = v :=
    fun z hz z' hz' hne v hv x hx =>
      commSub_le_fixV_of_commute hW (hXc z hz) (hXc z' hz') hne (hab z hz z' hz') hv x hx
  have hdisj : ∀ z ∈ Y, ∀ z' ∈ Y,
      X.map (MulAut.conj z).toMonoidHom ≠ X.map (MulAut.conj z').toMonoidHom →
      commSub (⊤ : Subgroup W) (X.map (MulAut.conj z).toMonoidHom) ⊓
        commSub ⊤ (X.map (MulAut.conj z').toMonoidHom) = ⊥ :=
    fun z hz z' hz' hne =>
      commSub_inf_commSub_eq_bot hW (hXc z hz) (hXc z' hz') hne (hab z hz z' hz')
  have h1Y : (1 : MulAut W) ∈ Y := Y.one_mem
  have hX0 := map_conj_one X
  have hmove : ∀ z ∈ Y, ∀ v ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj z).toMonoidHom),
      v ≠ 1 → ∃ x ∈ X.map (MulAut.conj z).toMonoidHom, x v ≠ v := by
    intro z hz v hv hv1
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ X.map (MulAut.conj z).toMonoidHom, x ≠ 1 := by
      by_contra hall
      push Not at hall
      exact (hXc z hz).2.1 ((Subgroup.eq_bot_iff_forall _).2 hall)
    exact ⟨x, hx, fun h => hx1 (eq_one_of_apply_eq (hXc z hz) hx hv hv1 h)⟩
  by_contra hne
  push Not at hne
  obtain ⟨y₀, hy₀, hy₀X⟩ := hne
  have hy₀X' : X.map (MulAut.conj y₀).toMonoidHom ≠ X.map (MulAut.conj 1).toMonoidHom := by
    rwa [hX0]
  have hA : ∀ a ∈ Y, X.map (MulAut.conj a).toMonoidHom = X → a = 1 := by
    intro a ha haX
    by_contra ha1
    obtain ⟨u₀, hu₀, hu₀1⟩ := exists_ne_one hX1
    have hu₀' : y₀ u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₀).toMonoidHom) :=
      mem_commSub_map_conj X y₀ hu₀
    have hu₀X : u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj 1).toMonoidHom) := by
      rwa [hX0]
    have haU : ∀ u ∈ commSub (⊤ : Subgroup W) X, a u ∈ commSub (⊤ : Subgroup W) X := by
      intro u hu
      have h1 := mem_commSub_map_conj X a hu
      rwa [haX] at h1
    by_cases hfx : ∃ u ∈ commSub (⊤ : Subgroup W) X, u ≠ 1 ∧ a u = u
    · obtain ⟨u, hu, hu1, hau⟩ := hfx
      have hzp : Subgroup.zpowers a ≠ ⊥ := fun h0 => ha1 ((Subgroup.zpowers_eq_bot).1 h0)
      have hufix : u ∈ fixV Y := by
        rw [← fixV_eq_of_le hW hY ((Subgroup.zpowers_le).2 ha) hzp]
        intro b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact zpow_apply_eq hau k
      have hy₀u : y₀ u = u := hufix y₀ hy₀
      have h1 : u ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₀).toMonoidHom) ⊓
          commSub ⊤ (X.map (MulAut.conj 1).toMonoidHom) := by
        refine ⟨?_, by rwa [hX0]⟩
        rw [← hy₀u]
        exact mem_commSub_map_conj X y₀ hu
      rw [hdisj y₀ hy₀ 1 h1Y hy₀X'] at h1
      exact hu1 h1
    · push Not at hfx
      have hUY : commSub (⊤ : Subgroup W) X ≤ commSub ⊤ Y := by
        intro w hw
        let f : commSub (⊤ : Subgroup W) X → commSub (⊤ : Subgroup W) X := fun v =>
          ⟨a v * (v : W)⁻¹, (commSub ⊤ X).mul_mem (haU v v.2) ((commSub ⊤ X).inv_mem v.2)⟩
        have hf : Function.Injective f := by
          intro v v' hvv
          have h1 : a v * (v : W)⁻¹ = a v' * (v' : W)⁻¹ := congrArg Subtype.val hvv
          have h2 : a ((v : W) * (v' : W)⁻¹) = (v : W) * (v' : W)⁻¹ := by
            have h3 : a (v : W) = a (v' : W) * (v' : W)⁻¹ * v := mul_inv_eq_iff_eq_mul.1 h1
            rw [map_mul, map_inv, h3, mul_inv_eq_iff_eq_mul]
            ac_rfl
          by_contra hne
          have hne' : (v : W) * (v' : W)⁻¹ ≠ 1 := fun h0 =>
            hne (Subtype.ext (mul_inv_eq_one.1 h0))
          exact hfx _ ((commSub ⊤ X).mul_mem v.2 ((commSub ⊤ X).inv_mem v'.2)) hne' h2
        obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hf) ⟨w, hw⟩
        have h1 : a v * (v : W)⁻¹ = w := congrArg Subtype.val hv
        rw [← h1]
        exact Subgroup.subset_closure ⟨a, ha, v, Subgroup.mem_top _, rfl⟩
      have hwY : u₀ * y₀ u₀ ∈ commSub (⊤ : Subgroup W) Y :=
        (commSub ⊤ Y).mul_mem (hUY hu₀) (commSub_stable' hy₀ (hUY hu₀))
      have hw1 : u₀ * y₀ u₀ ≠ 1 := by
        intro h0
        have h2 : y₀ u₀ = u₀⁻¹ := eq_inv_of_mul_eq_one_right h0
        have h3 : y₀ u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₀).toMonoidHom) ⊓
            commSub ⊤ (X.map (MulAut.conj 1).toMonoidHom) :=
          ⟨hu₀', by rw [h2]; exact (commSub ⊤ _).inv_mem hu₀X⟩
        rw [hdisj y₀ hy₀ 1 h1Y hy₀X'] at h3
        apply hu₀1
        have h4 : y₀ u₀ = y₀ 1 := by rw [map_one]; exact h3
        exact y₀.injective h4
      obtain ⟨y, hy, hyu⟩ := exists_apply_eq hY (hUY hu₀) hu₀1 hwY hw1
      have hyu' : u₀ * y₀ u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y).toMonoidHom) := by
        rw [← hyu]
        exact mem_commSub_map_conj X y hu₀
      by_cases hy1 : X.map (MulAut.conj y).toMonoidHom = X.map (MulAut.conj 1).toMonoidHom
      · rw [hy1] at hyu'
        have h2 : y₀ u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₀).toMonoidHom) ⊓
            commSub ⊤ (X.map (MulAut.conj 1).toMonoidHom) := by
          refine ⟨hu₀', ?_⟩
          have h3 := (commSub ⊤ _).mul_mem ((commSub ⊤ _).inv_mem hu₀X) hyu'
          rwa [inv_mul_cancel_left] at h3
        rw [hdisj y₀ hy₀ 1 h1Y hy₀X'] at h2
        apply hu₀1
        have h4 : y₀ u₀ = y₀ 1 := by rw [map_one]; exact h2
        exact y₀.injective h4
      by_cases hy2 : X.map (MulAut.conj y).toMonoidHom = X.map (MulAut.conj y₀).toMonoidHom
      · rw [hy2] at hyu'
        have h2 : u₀ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₀).toMonoidHom) ⊓
            commSub ⊤ (X.map (MulAut.conj 1).toMonoidHom) := by
          refine ⟨?_, hu₀X⟩
          have h3 := (commSub ⊤ _).mul_mem hyu' ((commSub ⊤ _).inv_mem hu₀')
          rwa [mul_inv_cancel_right] at h3
        rw [hdisj y₀ hy₀ 1 h1Y hy₀X'] at h2
        exact hu₀1 h2
      obtain ⟨x, hx, hxw⟩ := hmove y hy _ hyu' hw1
      apply hxw
      rw [map_mul, hfix 1 h1Y y hy (Ne.symm hy1) u₀ hu₀X x hx,
        hfix y₀ hy₀ y hy (Ne.symm hy2) _ hu₀' x hx]
  have hinj : ∀ z ∈ Y, ∀ z' ∈ Y,
      X.map (MulAut.conj z).toMonoidHom = X.map (MulAut.conj z').toMonoidHom → z = z' := by
    intro z hz z' hz' hzz
    have h1 : X.map (MulAut.conj (z⁻¹ * z')).toMonoidHom = X := by
      rw [← map_conj_map_conj, ← hzz, map_conj_map_conj, inv_mul_cancel, hX0]
    have h2 := hA _ (Y.mul_mem (Y.inv_mem hz) hz') h1
    rw [inv_mul_eq_one] at h2
    exact h2
  obtain ⟨y₁, hy₁, hy₁1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hY.2.1 ((Subgroup.eq_bot_iff_forall _).2 hall)
  have hodd₁ : Odd (orderOf y₁) := odd_orderOf_of_mem hY.2.2.2.1 hy₁
  obtain ⟨y₂, hy₂def⟩ : ∃ y₂, y₂ = y₁ * y₁ := ⟨_, rfl⟩
  have hy₂ : y₂ ∈ Y := by
    rw [hy₂def]
    exact Y.mul_mem hy₁ hy₁
  have hy₂1 : y₂ ≠ 1 := by
    intro h0
    rw [hy₂def] at h0
    have h2 : orderOf y₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h0)
    have h3 : orderOf y₁ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h4 | h4
      · exact h4
      · rw [h4] at hodd₁
        exact absurd hodd₁ (by decide)
    exact hy₁1 (orderOf_eq_one_iff.1 h3)
  have hy₁₂ : y₁ ≠ y₂ := by
    intro h0
    apply hy₁1
    have : y₁ * 1 = y₁ * y₁ := by rw [mul_one, ← hy₂def]; exact h0
    exact (mul_left_cancel this).symm
  obtain ⟨u, hu, hu1⟩ := exists_ne_one hX1
  obtain ⟨x₁, hx₁, hx₁1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hX1.2.1 ((Subgroup.eq_bot_iff_forall _).2 hall)
  set u' := x₁ u with hu'def
  have hu' : u' ∈ commSub (⊤ : Subgroup W) X := commSub_stable' hx₁ hu
  have hu'1 : u' ≠ 1 := by
    intro h0
    apply hu1
    have h2 : x₁ u = x₁ 1 := by rw [map_one]; exact h0
    exact x₁.injective h2
  have huu' : u * u' ≠ 1 := by
    intro h0
    have h2 : u' = u := by
      have h3 := eq_inv_of_mul_eq_one_right h0
      rw [h3, inv_eq_of_mul_eq_one_right (by rw [← pow_two, hW])]
    exact hx₁1 (eq_one_of_apply_eq hX1 hx₁ hu hu1 h2)
  have huX : u ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj 1).toMonoidHom) := by rwa [hX0]
  have hu'X : u' ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj 1).toMonoidHom) := by
    rwa [hX0]
  have huu'X : u * u' ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj 1).toMonoidHom) :=
    (commSub ⊤ _).mul_mem huX hu'X
  have hv₁ : y₁ u ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₁).toMonoidHom) :=
    mem_commSub_map_conj X y₁ hu
  have hv₂ : y₂ u' ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y₂).toMonoidHom) :=
    mem_commSub_map_conj X y₂ hu'
  have hv₁1 : y₁ u ≠ 1 := fun h0 => hu1 (y₁.injective (h0.trans (map_one y₁).symm))
  have hv₂1 : y₂ u' ≠ 1 := fun h0 => hu'1 (y₂.injective (h0.trans (map_one y₂).symm))
  have hsq : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (by rw [← pow_two, hW])
  have hwa : y₁ u * u⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
    Subgroup.subset_closure ⟨y₁, hy₁, u, Subgroup.mem_top u, rfl⟩
  have hwb : (u * u') * y₁ u * y₂ u' ∈ commSub (⊤ : Subgroup W) Y := by
    have h1 : y₂ u' * u'⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
      Subgroup.subset_closure ⟨y₂, hy₂, u', Subgroup.mem_top u', rfl⟩
    have h2 := (commSub ⊤ Y).mul_mem hwa h1
    have h3 : y₁ u * u⁻¹ * (y₂ u' * u'⁻¹) = (u * u') * y₁ u * y₂ u' := by
      rw [hsq u, hsq u']
      ac_rfl
    rwa [h3] at h2
  have hne₀₁ : X.map (MulAut.conj 1).toMonoidHom ≠ X.map (MulAut.conj y₁).toMonoidHom :=
    fun h => hy₁1 (hinj 1 h1Y y₁ hy₁ h).symm
  have hne₀₂ : X.map (MulAut.conj 1).toMonoidHom ≠ X.map (MulAut.conj y₂).toMonoidHom :=
    fun h => hy₂1 (hinj 1 h1Y y₂ hy₂ h).symm
  have hne₁₂ : X.map (MulAut.conj y₁).toMonoidHom ≠ X.map (MulAut.conj y₂).toMonoidHom :=
    fun h => hy₁₂ (hinj y₁ hy₁ y₂ hy₂ h)
  have hmove0 : ∀ x ∈ X.map (MulAut.conj 1).toMonoidHom, x ≠ 1 →
      x ((u * u') * y₁ u * y₂ u') ≠ (u * u') * y₁ u * y₂ u' := fun x hx hx1 =>
    apply_ne_of_fixes (fun h => hx1 (eq_one_of_apply_eq (hXc 1 h1Y) hx huu'X huu' h))
      (hfix y₁ hy₁ 1 h1Y hne₀₁.symm _ hv₁ x hx) (hfix y₂ hy₂ 1 h1Y hne₀₂.symm _ hv₂ x hx)
  have hmove1 : ∀ x ∈ X.map (MulAut.conj y₁).toMonoidHom, x ≠ 1 →
      x ((u * u') * y₁ u * y₂ u') ≠ (u * u') * y₁ u * y₂ u' := by
    intro x hx hx1
    have h1 : x (y₁ u * (u * u') * y₂ u') ≠ y₁ u * (u * u') * y₂ u' := apply_ne_of_fixes
      (fun h => hx1 (eq_one_of_apply_eq (hXc y₁ hy₁) hx hv₁ hv₁1 h))
      (hfix 1 h1Y y₁ hy₁ hne₀₁ _ huu'X x hx) (hfix y₂ hy₂ y₁ hy₁ hne₁₂.symm _ hv₂ x hx)
    have h2 : y₁ u * (u * u') * y₂ u' = (u * u') * y₁ u * y₂ u' := by ac_rfl
    rwa [h2] at h1
  have hmove2 : ∀ x ∈ X.map (MulAut.conj y₂).toMonoidHom, x ≠ 1 →
      x ((u * u') * y₁ u * y₂ u') ≠ (u * u') * y₁ u * y₂ u' := by
    intro x hx hx1
    have h1 : x (y₂ u' * (u * u') * y₁ u) ≠ y₂ u' * (u * u') * y₁ u := apply_ne_of_fixes
      (fun h => hx1 (eq_one_of_apply_eq (hXc y₂ hy₂) hx hv₂ hv₂1 h))
      (hfix 1 h1Y y₂ hy₂ hne₀₂ _ huu'X x hx) (hfix y₁ hy₁ y₂ hy₂ hne₁₂ _ hv₁ x hx)
    have h2 : y₂ u' * (u * u') * y₁ u = (u * u') * y₁ u * y₂ u' := by ac_rfl
    rwa [h2] at h1
  have hnontriv : ∀ z ∈ Y, ∃ x ∈ X.map (MulAut.conj z).toMonoidHom, x ≠ 1 := by
    intro z hz
    by_contra hall
    push Not at hall
    exact (hXc z hz).2.1 ((Subgroup.eq_bot_iff_forall _).2 hall)
  have hwb1 : (u * u') * y₁ u * y₂ u' ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := hnontriv 1 h1Y
    intro h0
    apply hmove0 x hx hx1
    rw [h0, map_one]
  have hwa1 : y₁ u * u⁻¹ ≠ 1 := by
    intro h0
    have h1 : y₁ u = u := mul_inv_eq_one.1 h0
    have h2 : u ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj 1).toMonoidHom) ⊓
        commSub ⊤ (X.map (MulAut.conj y₁).toMonoidHom) := ⟨huX, h1 ▸ hv₁⟩
    rw [hdisj 1 h1Y y₁ hy₁ hne₀₁] at h2
    exact hu1 h2
  obtain ⟨y, hy, hyw⟩ := exists_apply_eq hY hwa hwa1 hwb hwb1
  have hyy₁ : y * y₁ ∈ Y := Y.mul_mem hy hy₁
  have hc₁ : y (y₁ u) ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj (y * y₁)).toMonoidHom) := by
    rw [← MulAut.mul_apply]
    exact mem_commSub_map_conj X (y * y₁) hu
  have hc₂ : y u⁻¹ ∈ commSub (⊤ : Subgroup W) (X.map (MulAut.conj y).toMonoidHom) :=
    mem_commSub_map_conj X y ((commSub ⊤ X).inv_mem hu)
  have hfixw : ∀ z ∈ Y, z ≠ y * y₁ → z ≠ y →
      ∀ x ∈ X.map (MulAut.conj z).toMonoidHom, x (y (y₁ u * u⁻¹)) = y (y₁ u * u⁻¹) := by
    intro z hz hz₁ hz₂ x hx
    have hz₁' : X.map (MulAut.conj (y * y₁)).toMonoidHom ≠ X.map (MulAut.conj z).toMonoidHom :=
      fun h => hz₁ (hinj _ hyy₁ _ hz h).symm
    have hz₂' : X.map (MulAut.conj y).toMonoidHom ≠ X.map (MulAut.conj z).toMonoidHom :=
      fun h => hz₂ (hinj _ hy _ hz h).symm
    rw [map_mul, map_mul, hfix _ hyy₁ z hz hz₁' _ hc₁ x hx, hfix _ hy z hz hz₂' _ hc₂ x hx]
  by_cases a0 : (1 : MulAut W) ≠ y * y₁ ∧ (1 : MulAut W) ≠ y
  · obtain ⟨x, hx, hx1⟩ := hnontriv 1 h1Y
    apply hmove0 x hx hx1
    rw [← hyw]
    exact hfixw 1 h1Y a0.1 a0.2 x hx
  by_cases a1 : y₁ ≠ y * y₁ ∧ y₁ ≠ y
  · obtain ⟨x, hx, hx1⟩ := hnontriv y₁ hy₁
    apply hmove1 x hx hx1
    rw [← hyw]
    exact hfixw y₁ hy₁ a1.1 a1.2 x hx
  by_cases a2 : y₂ ≠ y * y₁ ∧ y₂ ≠ y
  · obtain ⟨x, hx, hx1⟩ := hnontriv y₂ hy₂
    apply hmove2 x hx hx1
    rw [← hyw]
    exact hfixw y₂ hy₂ a2.1 a2.2 x hx
  push Not at a0 a1 a2
  have e0 : (1 : MulAut W) = y * y₁ ∨ (1 : MulAut W) = y := by
    by_cases h : (1 : MulAut W) = y * y₁
    · exact Or.inl h
    · exact Or.inr (a0 h)
  have e1 : y₁ = y * y₁ ∨ y₁ = y := by
    by_cases h : y₁ = y * y₁
    · exact Or.inl h
    · exact Or.inr (a1 h)
  have e2 : y₂ = y * y₁ ∨ y₂ = y := by
    by_cases h : y₂ = y * y₁
    · exact Or.inl h
    · exact Or.inr (a2 h)
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  all_goals first
    | exact absurd (e0.trans e1.symm) (Ne.symm hy₁1)
    | exact absurd (e0.trans e2.symm) (Ne.symm hy₂1)
    | exact absurd (e1.trans e2.symm) hy₁₂

end Pf

end Asc81c

end CFSG.Quasithin
