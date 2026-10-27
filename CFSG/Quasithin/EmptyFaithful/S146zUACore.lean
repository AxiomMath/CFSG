module

public import CFSG.Quasithin.EmptyFaithful.S14612EC

public section

namespace CFSG.Quasithin.S146zU.UA

open CFSG.Quasithin

section Basic

variable {Y : Type} [CommGroup Y]

theorem mem_commV_gen {L : Subgroup (MulAut Y)} {a : MulAut Y} (ha : a ∈ L) (v : Y) :
    a v * v⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨a, ha, v, rfl⟩

theorem commV_le_fixV_symm {L₁ L₂ : Subgroup (MulAut Y)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hD : commV L₁ ≤ fixV L₂) :
    commV L₂ ≤ fixV L₁ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨b, hb, v, rfl⟩
  rw [SetLike.mem_coe, mem_fixV]
  intro a ha
  have h2 : b (a v * v⁻¹) = a v * v⁻¹ := hD (mem_commV_gen ha v) b hb
  have hab : (a * b) v = (b * a) v := by rw [hcomm a ha b hb]
  simp only [MulAut.mul_apply, map_mul, map_inv] at h2 hab ⊢
  rw [hab]
  have h3 : b (a v) = a v * v⁻¹ * b v := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact h2
  rw [h3]
  calc a v * v⁻¹ * b v * (a v)⁻¹ = (a v * (a v)⁻¹) * (b v * v⁻¹) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = b v * v⁻¹ := by rw [mul_inv_cancel, one_mul]

theorem mul_inv_eq_inv_of_mul_eq {P Q p q : Y} (h : P * Q = p * q) : P * p⁻¹ = (Q * q⁻¹)⁻¹ := by
  have h1 : P * p⁻¹ * (Q * q⁻¹) = 1 := by
    calc P * p⁻¹ * (Q * q⁻¹) = (P * Q) * (p⁻¹ * q⁻¹) := by
          simp only [mul_left_comm, mul_assoc]
      _ = (p * q) * (p⁻¹ * q⁻¹) := by rw [h]
      _ = 1 := by rw [← mul_inv, mul_inv_cancel]
  exact eq_inv_of_mul_eq_one_left h1

end Basic

section Core

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem eq_one_of_mem_commV_zpowers (hY : ∀ v : Y, v ^ 2 = 1) {a : MulAut Y} (ha : a ^ 5 = 1)
    {w : Y} (hc : w ∈ commV (Subgroup.zpowers a)) (hf : a w = w) : w = 1 := by
  have hodd : Odd (Nat.card (Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one ha)
  have hfix : w ∈ fixV (Subgroup.zpowers a) := by
    have h : a ∈ MulAction.stabilizer (MulAut Y) w := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hf
    intro g hg
    have := (Subgroup.zpowers_le.mpr h) hg
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  have hbot := commV_inf_fixV_eq_bot hY hodd
  have hw : w ∈ commV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers a) := ⟨hc, hfix⟩
  rw [hbot] at hw
  exact Subgroup.mem_bot.mp hw

omit [Finite Y] in
theorem apply_mul_split {L₁ L₂ : Subgroup (MulAut Y)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hD₁ : commV L₁ ≤ fixV L₂)
    (hD₂ : commV L₂ ≤ fixV L₁) {c₁ c₂ : MulAut Y} (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂) {u₁ u₂ : Y}
    (hu₁ : u₁ ∈ commV L₁) (hu₂ : u₂ ∈ commV L₂) :
    (c₁ * c₂) (u₁ * u₂) = c₁ u₁ * c₂ u₂ := by
  have h1 : c₂ u₁ = u₁ := hD₁ hu₁ c₂ hc₂
  have h2 : c₁ u₂ = u₂ := hD₂ hu₂ c₁ hc₁
  have h3 : c₁ (c₂ u₂) = c₂ u₂ := by
    have : (c₁ * c₂) u₂ = (c₂ * c₁) u₂ := by rw [hcomm c₁ hc₁ c₂ hc₂]
    simp only [MulAut.mul_apply] at this
    rw [this, h2]
  simp only [MulAut.mul_apply, map_mul]
  rw [h1, h3]

omit [Finite Y] in
theorem apply_mul_inv_mem_sup {L₁ L₂ : Subgroup (MulAut Y)} {b₁ b₂ : MulAut Y} (hb₁ : b₁ ∈ L₁)
    (hb₂ : b₂ ∈ L₂) (u : Y) : (b₁ * b₂) u * u⁻¹ ∈ commV L₁ ⊔ commV L₂ := by
  have e : (b₁ * b₂) u * u⁻¹ = (b₁ (b₂ u) * (b₂ u)⁻¹) * (b₂ u * u⁻¹) := by
    rw [MulAut.mul_apply]
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact Subgroup.mul_mem_sup (mem_commV_gen hb₁ _) (mem_commV_gen hb₂ _)

theorem eq_one_or_eq_one {L₁ L₂ : Subgroup (MulAut Y)} (hY : ∀ v : Y, v ^ 2 = 1)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hD₁ : commV L₁ ≤ fixV L₂)
    (h5₁ : ∀ c ∈ L₁, ∀ d ∈ L₁, c ^ 5 = 1 → d ^ 5 = 1 → c * d = d * c → c ≠ 1 →
      d ∈ Subgroup.zpowers c)
    (h5₂ : ∀ c ∈ L₂, ∀ d ∈ L₂, c ^ 5 = 1 → d ^ 5 = 1 → c * d = d * c → c ≠ 1 →
      d ∈ Subgroup.zpowers c)
    {a₁ b₁ a₂ b₂ : MulAut Y} (ha₁ : a₁ ∈ L₁) (hb₁ : b₁ ∈ L₁) (ha₂ : a₂ ∈ L₂) (hb₂ : b₂ ∈ L₂)
    (ha₁5 : a₁ ^ 5 = 1) (hb₁5 : b₁ ^ 5 = 1) (ha₂5 : a₂ ^ 5 = 1) (hb₂5 : b₂ ^ 5 = 1)
    (hab₁ : a₁ * b₁ = b₁ * a₁) (hab₂ : a₂ * b₂ = b₂ * a₂)
    {W : Subgroup Y} (hW : W ≠ ⊥) (hfix : ∀ w ∈ W, (a₁ * a₂) w = w)
    (hsurj : ∀ w ∈ W, ∃ u ∈ W, w = (b₁ * b₂) u * u⁻¹) : a₁ = 1 ∨ a₂ = 1 := by
  have hD₂ : commV L₂ ≤ fixV L₁ := commV_le_fixV_symm hcomm hD₁
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne₁, hne₂⟩ := hcon
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨u, huW, hwu⟩ := hsurj w hwW
  have huY : u ∈ commV L₁ ⊔ commV L₂ := by
    obtain ⟨u', -, hu'⟩ := hsurj u huW
    rw [hu']
    exact apply_mul_inv_mem_sup hb₁ hb₂ u'
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp huY
  set w₁ : Y := b₁ u₁ * u₁⁻¹ with hw₁def
  set w₂ : Y := b₂ u₂ * u₂⁻¹ with hw₂def
  have hw₁ : w₁ ∈ commV L₁ := mem_commV_gen hb₁ u₁
  have hw₂ : w₂ ∈ commV L₂ := mem_commV_gen hb₂ u₂
  have hww : w = w₁ * w₂ := by
    rw [hwu, apply_mul_split hcomm hD₁ hD₂ hb₁ hb₂ hu₁ hu₂, hw₁def, hw₂def, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have hxw : a₁ w₁ * a₂ w₂ = w₁ * w₂ := by
    have := hfix w hwW
    rwa [hww, apply_mul_split hcomm hD₁ hD₂ ha₁ ha₂ hw₁ hw₂] at this
  have he : a₁ w₁ * w₁⁻¹ = (a₂ w₂ * w₂⁻¹)⁻¹ := mul_inv_eq_inv_of_mul_eq hxw
  have heY₂ : a₁ w₁ * w₁⁻¹ ∈ commV L₂ := by
    rw [he]
    exact (commV L₂).inv_mem (mem_commV_gen ha₂ w₂)
  have hae : a₁ (a₁ w₁ * w₁⁻¹) = a₁ w₁ * w₁⁻¹ := hD₂ heY₂ a₁ ha₁
  have he1 : a₁ w₁ * w₁⁻¹ = 1 :=
    eq_one_of_mem_commV_zpowers hY ha₁5
      (mem_commV_gen (Subgroup.mem_zpowers a₁) w₁) hae
  have ha₁w₁ : a₁ w₁ = w₁ := mul_inv_eq_one.mp he1
  have ha₂w₂ : a₂ w₂ = w₂ := by
    rw [ha₁w₁] at hxw
    exact mul_left_cancel hxw
  have hb₁a : b₁ ∈ Subgroup.zpowers a₁ := h5₁ a₁ ha₁ b₁ hb₁ ha₁5 hb₁5 hab₁ hne₁
  have hb₂a : b₂ ∈ Subgroup.zpowers a₂ := h5₂ a₂ ha₂ b₂ hb₂ ha₂5 hb₂5 hab₂ hne₂
  have hw₁1 : w₁ = 1 :=
    eq_one_of_mem_commV_zpowers hY ha₁5 (mem_commV_gen hb₁a u₁) ha₁w₁
  have hw₂1 : w₂ = 1 :=
    eq_one_of_mem_commV_zpowers hY ha₂5 (mem_commV_gen hb₂a u₂) ha₂w₂
  exact hw1' (by rw [hww, hw₁1, hw₂1, mul_one])

theorem core {L₁ L₂ : Subgroup (MulAut Y)} (hY : ∀ v : Y, v ^ 2 = 1)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hD₁ : commV L₁ ≤ fixV L₂)
    (h5₁ : ∀ c ∈ L₁, ∀ d ∈ L₁, c ^ 5 = 1 → d ^ 5 = 1 → c * d = d * c → c ≠ 1 →
      d ∈ Subgroup.zpowers c)
    (h5₂ : ∀ c ∈ L₂, ∀ d ∈ L₂, c ^ 5 = 1 → d ^ 5 = 1 → c * d = d * c → c ≠ 1 →
      d ∈ Subgroup.zpowers c)
    {a₁ b₁ a₂ b₂ : MulAut Y} (ha₁ : a₁ ∈ L₁) (hb₁ : b₁ ∈ L₁) (ha₂ : a₂ ∈ L₂) (hb₂ : b₂ ∈ L₂)
    (ha₁5 : a₁ ^ 5 = 1) (hb₁5 : b₁ ^ 5 = 1) (ha₂5 : a₂ ^ 5 = 1) (hb₂5 : b₂ ^ 5 = 1)
    (hab₁ : a₁ * b₁ = b₁ * a₁) (hab₂ : a₂ * b₂ = b₂ * a₂) (hx : a₁ * a₂ ≠ 1)
    (hy : b₁ * b₂ ∉ Subgroup.zpowers (a₁ * a₂)) {X₁ X₂ : Subgroup Y} (hX₁ : X₁ ≠ ⊥)
    (hX₂ : X₂ ≠ ⊥) (hxX₂ : ∀ w ∈ X₂, (a₁ * a₂) w = w) (hyX₁ : ∀ w ∈ X₁, (b₁ * b₂) w = w)
    (hX₂y : ∀ w ∈ X₂, ∃ u ∈ X₂, w = (b₁ * b₂) u * u⁻¹)
    (hX₁x : ∀ w ∈ X₁, ∃ u ∈ X₁, w = (a₁ * a₂) u * u⁻¹) :
    (a₂ = 1 ∧ b₁ = 1 ∧ X₁ ≤ commV L₁ ∧ X₂ ≤ commV L₂) ∨
      (a₁ = 1 ∧ b₂ = 1 ∧ X₁ ≤ commV L₂ ∧ X₂ ≤ commV L₁) := by
  have h1 : a₁ = 1 ∨ a₂ = 1 :=
    eq_one_or_eq_one hY hcomm hD₁ h5₁ h5₂ ha₁ hb₁ ha₂ hb₂ ha₁5 hb₁5 ha₂5 hb₂5 hab₁ hab₂ hX₂ hxX₂
      hX₂y
  have h2 : b₁ = 1 ∨ b₂ = 1 :=
    eq_one_or_eq_one hY hcomm hD₁ h5₁ h5₂ hb₁ ha₁ hb₂ ha₂ hb₁5 ha₁5 hb₂5 ha₂5 hab₁.symm
      hab₂.symm hX₁ hyX₁ hX₁x
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    exfalso
    have ha₂1 : a₂ ≠ 1 := by
      intro h
      exact hx (by rw [h1, h, mul_one])
    apply hy
    rw [h1, h2, one_mul, one_mul]
    exact h5₂ a₂ ha₂ b₂ hb₂ ha₂5 hb₂5 hab₂ ha₂1
  ·
    right
    refine ⟨h1, h2, fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨u, -, rfl⟩ := hX₁x w hw
      rw [h1, one_mul]
      exact mem_commV_gen ha₂ u
    · obtain ⟨u, -, rfl⟩ := hX₂y w hw
      rw [h2, mul_one]
      exact mem_commV_gen hb₁ u
  ·
    left
    refine ⟨h1, h2, fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨u, -, rfl⟩ := hX₁x w hw
      rw [h1, mul_one]
      exact mem_commV_gen ha₁ u
    · obtain ⟨u, -, rfl⟩ := hX₂y w hw
      rw [h2, one_mul]
      exact mem_commV_gen hb₂ u
  ·
    exfalso
    have ha₁1 : a₁ ≠ 1 := by
      intro h
      exact hx (by rw [h, h1, mul_one])
    apply hy
    rw [h1, h2, mul_one, mul_one]
    exact h5₁ a₁ ha₁ b₁ hb₁ ha₁5 hb₁5 hab₁ ha₁1

end Core

end CFSG.Quasithin.S146zU.UA
