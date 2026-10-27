module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup

public section

namespace CFSG.Quasithin.SteinbergBX

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Offender Module Matrix

namespace QuaternionActor

@[expose] def slA (q : ℕ) : SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] def slB : (q : ℕ) → SpecialLinearGroup (Fin 2) (ZMod q)
  | 3 => ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩
  | 5 => ⟨!![2, 0; 0, 3], by rw [Matrix.det_fin_two_of]; decide⟩
  | _ => 1

@[expose] def quatEval {G : Type*} [Monoid G] (x y : G) : QuaternionGroup 2 → G
  | .a i => x ^ i.val
  | .xa i => y * x ^ i.val

theorem quatEval_mul (q : ℕ) (hq : q = 3 ∨ q = 5) (g h : QuaternionGroup 2) :
    quatEval (slA q) (slB q) (g * h) = quatEval (slA q) (slB q) g * quatEval (slA q) (slB q) h := by
  rcases hq with rfl | rfl <;> revert g h <;> decide

theorem quatEval_injective (q : ℕ) (hq : q = 3 ∨ q = 5) :
    Function.Injective (quatEval (slA q) (slB q)) := by
  intro g h hgh
  revert g h
  rcases hq with rfl | rfl <;> decide

@[expose] def quatHom (q : ℕ) (hq : q = 3 ∨ q = 5) :
    QuaternionGroup 2 →* SpecialLinearGroup (Fin 2) (ZMod q) :=
  MonoidHom.mk' (quatEval (slA q) (slB q)) (quatEval_mul q hq)

theorem quatHom_apply (q : ℕ) (hq : q = 3 ∨ q = 5) (g : QuaternionGroup 2) :
    quatHom q hq g = quatEval (slA q) (slB q) g :=
  rfl

theorem quatHom_injective (q : ℕ) (hq : q = 3 ∨ q = 5) : Function.Injective (quatHom q hq) :=
  quatEval_injective q hq

theorem card_range_quatHom (q : ℕ) (hq : q = 3 ∨ q = 5) : Nat.card (quatHom q hq).range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (quatHom_injective q hq)).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

@[expose] def slU : SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def quatOmega : QuaternionGroup 2 → QuaternionGroup 2 :=
  quatEval (QuaternionGroup.xa 2) (QuaternionGroup.xa 1)

theorem quatOmega_intertwine (g : QuaternionGroup 2) :
    quatHom 3 (Or.inl rfl) (quatOmega g) = slU * quatHom 3 (Or.inl rfl) g * slU⁻¹ := by
  revert g
  decide

theorem exists_intertwine (x y : QuaternionGroup 2)
    (hmul : ∀ g h, quatEval x y (g * h) = quatEval x y g * quatEval x y h)
    (h3 : ∀ g, quatEval x y (quatEval x y (quatEval x y g)) = g) (h1 : ∃ g, quatEval x y g ≠ g) :
    ∃ x' y' : QuaternionGroup 2,
      (∀ g h, quatEval x' y' (g * h) = quatEval x' y' g * quatEval x' y' h) ∧
      (∀ g h, quatEval x' y' g = quatEval x' y' h → g = h) ∧
      ∀ g, quatEval x' y' (quatOmega g) = quatEval x y (quatEval x' y' g) := by
  revert x y
  decide

theorem det_entries {R : Type*} [CommRing R] (g : SpecialLinearGroup (Fin 2) R) :
    g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

theorem mul_entry {R : Type*} [CommRing R] (g h : SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    (g * h).1 i j = g.1 i 0 * h.1 0 j + g.1 i 1 * h.1 1 j := by
  change (g.1 * h.1) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_of_entries {R : Type*} [CommRing R] {g h : SpecialLinearGroup (Fin 2) R}
    (h00 : g.1 0 0 = h.1 0 0) (h01 : g.1 0 1 = h.1 0 1) (h10 : g.1 1 0 = h.1 1 0)
    (h11 : g.1 1 1 = h.1 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem involution_entries_three : ∀ w x y z : ZMod 3, w * z - x * y = 1 →
    w * w + x * y = 1 → w * x + x * z = 0 → y * w + z * y = 0 → y * x + z * z = 1 →
    (w = 1 ∧ x = 0 ∧ y = 0 ∧ z = 1) ∨ (w = -1 ∧ x = 0 ∧ y = 0 ∧ z = -1) := by
  decide

theorem involution_entries_five : ∀ w x y z : ZMod 5, w * z - x * y = 1 →
    w * w + x * y = 1 → w * x + x * z = 0 → y * w + z * y = 0 → y * x + z * z = 1 →
    (w = 1 ∧ x = 0 ∧ y = 0 ∧ z = 1) ∨ (w = -1 ∧ x = 0 ∧ y = 0 ∧ z = -1) := by
  decide

theorem eq_one_or_eq_neg_one_of_mul_self (q : ℕ) (hq : q = 3 ∨ q = 5)
    (g : SpecialLinearGroup (Fin 2) (ZMod q)) (hg : g * g = 1) : g = 1 ∨ g = -1 := by
  have h1 : ∀ i j : Fin 2, (g * g).1 i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) i j :=
    fun i j => by rw [hg]; rfl
  have e00 := h1 0 0
  have e01 := h1 0 1
  have e10 := h1 1 0
  have e11 := h1 1 1
  simp only [mul_entry, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  have key : ∀ w x y z : ZMod q, w * z - x * y = 1 → w * w + x * y = 1 → w * x + x * z = 0 →
      y * w + z * y = 0 → y * x + z * z = 1 →
      (w = 1 ∧ x = 0 ∧ y = 0 ∧ z = 1) ∨ (w = -1 ∧ x = 0 ∧ y = 0 ∧ z = -1) := by
    rcases hq with rfl | rfl
    exacts [involution_entries_three, involution_entries_five]
  rcases key _ _ _ _ (det_entries g) e00 e01 e10 e11 with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · left
    refine eq_of_entries ?_ ?_ ?_ ?_
    · rw [a]; rfl
    · rw [b]; rfl
    · rw [c]; rfl
    · rw [d]; rfl
  · right
    refine eq_of_entries ?_ ?_ ?_ ?_
    · rw [a]; rfl
    · rw [b]; exact neg_zero.symm
    · rw [c]; exact neg_zero.symm
    · rw [d]; rfl

theorem quatHom_three_sq (i : QuaternionGroup 2) :
    quatHom 3 (Or.inl rfl) i * quatHom 3 (Or.inl rfl) i = 1 ∨
      quatHom 3 (Or.inl rfl) i * quatHom 3 (Or.inl rfl) i = -1 := by
  revert i
  decide

theorem mem_range_quatHom_three_entries : ∀ w x y z : ZMod 3, w * z - x * y = 1 →
    ((w * w + x * y = 1 ∧ w * x + x * z = 0 ∧ y * w + z * y = 0 ∧ y * x + z * z = 1) ∨
      (w * w + x * y = -1 ∧ w * x + x * z = 0 ∧ y * w + z * y = 0 ∧ y * x + z * z = -1)) →
    ∃ i : QuaternionGroup 2, (quatHom 3 (Or.inl rfl) i).1 0 0 = w ∧
      (quatHom 3 (Or.inl rfl) i).1 0 1 = x ∧ (quatHom 3 (Or.inl rfl) i).1 1 0 = y ∧
      (quatHom 3 (Or.inl rfl) i).1 1 1 = z := by
  decide

theorem mem_range_quatHom_three (g : SpecialLinearGroup (Fin 2) (ZMod 3))
    (hg : g * g = 1 ∨ g * g = -1) : g ∈ (quatHom 3 (Or.inl rfl)).range := by
  have hentries : (g.1 0 0 * g.1 0 0 + g.1 0 1 * g.1 1 0 = 1 ∧
      g.1 0 0 * g.1 0 1 + g.1 0 1 * g.1 1 1 = 0 ∧ g.1 1 0 * g.1 0 0 + g.1 1 1 * g.1 1 0 = 0 ∧
      g.1 1 0 * g.1 0 1 + g.1 1 1 * g.1 1 1 = 1) ∨
      (g.1 0 0 * g.1 0 0 + g.1 0 1 * g.1 1 0 = -1 ∧
      g.1 0 0 * g.1 0 1 + g.1 0 1 * g.1 1 1 = 0 ∧ g.1 1 0 * g.1 0 0 + g.1 1 1 * g.1 1 0 = 0 ∧
      g.1 1 0 * g.1 0 1 + g.1 1 1 * g.1 1 1 = -1) := by
    rcases hg with hg | hg
    · left
      have h1 : ∀ i j : Fin 2, (g * g).1 i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j :=
        fun i j => by rw [hg]; rfl
      refine ⟨?_, ?_, ?_, ?_⟩ <;> [have h2 := h1 0 0; have h2 := h1 0 1; have h2 := h1 1 0;
        have h2 := h1 1 1] <;> rw [mul_entry] at h2 <;> rw [h2] <;> rfl
    · right
      have h1 : ∀ i j : Fin 2, (g * g).1 i j = (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j :=
        fun i j => by rw [hg]; rfl
      refine ⟨?_, ?_, ?_, ?_⟩ <;> [have h2 := h1 0 0; have h2 := h1 0 1; have h2 := h1 1 0;
        have h2 := h1 1 1] <;> rw [mul_entry] at h2 <;> rw [h2] <;> rfl
  obtain ⟨i, h00, h01, h10, h11⟩ :=
    mem_range_quatHom_three_entries _ _ _ _ (det_entries g) hentries
  exact ⟨i, eq_of_entries h00 h01 h10 h11⟩

instance quatHom_three_range_normal : (quatHom 3 (Or.inl rfl)).range.Normal := by
  constructor
  rintro _ ⟨i, rfl⟩ g
  apply mem_range_quatHom_three
  have hc : ∀ x : SpecialLinearGroup (Fin 2) (ZMod 3), (-1 : SpecialLinearGroup (Fin 2) (ZMod 3)) *
      x = x * -1 := fun x => by rw [neg_one_mul, mul_neg_one]
  rcases quatHom_three_sq i with h | h
  · left
    calc g * quatHom 3 _ i * g⁻¹ * (g * quatHom 3 _ i * g⁻¹) =
        g * (quatHom 3 _ i * quatHom 3 _ i) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · right
    calc g * quatHom 3 _ i * g⁻¹ * (g * quatHom 3 _ i * g⁻¹) =
        g * (quatHom 3 _ i * quatHom 3 _ i) * g⁻¹ := by group
      _ = -1 := by rw [h, ← hc, mul_assoc, mul_inv_cancel, mul_one]

theorem slU_pow_three : slU ^ 3 = 1 := by decide

theorem orderOf_slU : orderOf slU = 3 :=
  orderOf_eq_prime slU_pow_three (by decide)

theorem card_SL_three : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem isComplement'_three :
    (quatHom 3 (Or.inl rfl)).range.IsComplement' (zpowers slU) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [card_range_quatHom, Nat.card_zpowers, orderOf_slU, card_SL_three]
  · refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [card_range_quatHom, Nat.card_zpowers, orderOf_slU]
    decide

theorem nonempty_mulEquiv_of_intertwine {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] (N₁ : Subgroup G₁) (N₂ : Subgroup G₂) [N₁.Normal] [N₂.Normal] {u₁ : G₁}
    {u₂ : G₂} (h₁ : N₁.IsComplement' (zpowers u₁)) (h₂ : N₂.IsComplement' (zpowers u₂))
    (hord : orderOf u₁ = orderOf u₂) (Θ : N₁ ≃* N₂)
    (hΘ : ∀ n : N₁, Θ (MulAut.conjNormal u₁ n) = MulAut.conjNormal u₂ (Θ n)) :
    Nonempty (G₁ ≃* G₂) := by
  classical
  have hg₁ : ∀ x : zpowers u₁, x ∈ zpowers (⟨u₁, mem_zpowers u₁⟩ : zpowers u₁) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, Subtype.ext (by simp)⟩
  have hg₂ : ∀ x : zpowers u₂, x ∈ zpowers (⟨u₂, mem_zpowers u₂⟩ : zpowers u₂) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, Subtype.ext (by simp)⟩
  have hord' : orderOf (⟨u₁, mem_zpowers u₁⟩ : zpowers u₁) =
      orderOf (⟨u₂, mem_zpowers u₂⟩ : zpowers u₂) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
  let fg : zpowers u₁ ≃* zpowers u₂ := mulEquivOfOrderOfEq hg₁ hg₂ hord'
  have hfg : fg ⟨u₁, mem_zpowers u₁⟩ = ⟨u₂, mem_zpowers u₂⟩ :=
    mulEquivOfOrderOfEq_apply_gen hg₁ hg₂ hord'
  set φ₁ : zpowers u₁ →* MulAut N₁ :=
    (N₁.normalizerMonoidHom).comp (inclusion (N₁.normalizer_eq_top ▸ le_top)) with hφ₁
  set φ₂ : zpowers u₂ →* MulAut N₂ :=
    (N₂.normalizerMonoidHom).comp (inclusion (N₂.normalizer_eq_top ▸ le_top)) with hφ₂
  have hF : (MulAut.congr Θ).toMonoidHom.comp φ₁ = φ₂.comp fg.toMonoidHom := by
    rw [MonoidHom.eq_iff_eq_on_generator hg₁]
    ext n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply]
    rw [hfg]
    have h1 := hΘ (Θ.symm n)
    rw [MulEquiv.apply_symm_apply] at h1
    exact congrArg Subtype.val h1
  have hcompat : ∀ k : zpowers u₁, (φ₁ k).trans Θ = Θ.trans (φ₂ (fg k)) := by
    intro k
    ext n
    have h1 := congrArg (fun F : zpowers u₁ →* MulAut N₂ => (F k) (Θ n)) hF
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    simp only [MulEquiv.trans_apply]
    exact congrArg Subtype.val h1
  exact ⟨(SemidirectProduct.mulEquivSubgroup h₁).symm.trans
    ((SemidirectProduct.congr Θ fg hcompat).trans (SemidirectProduct.mulEquivSubgroup h₂))⟩

theorem false_of_commute {G : Type*} [Group G] [Finite G] (hG : NoPQuotient 2 G) (B : Subgroup G)
    (hBp : IsPGroup 2 B) (hB3 : Nat.card (G ⧸ B) = 3) (hB1 : B ≠ ⊥) (u : G)
    (hu : orderOf u = 3) (hc : ∀ b ∈ B, u * b = b * u) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hBp.exists_card_eq
  have hGcard : Nat.card G = 3 * 2 ^ j := by
    rw [B.card_eq_card_quotient_mul_card_subgroup, hB3, hj]
  have hUcard : Nat.card (zpowers u) = 3 := by rw [Nat.card_zpowers, hu]
  have hsup : B ⊔ zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : 2 ^ j ∣ Nat.card (B ⊔ zpowers u : Subgroup G) :=
      hj ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : 3 ∣ Nat.card (B ⊔ zpowers u : Subgroup G) :=
      hUcard ▸ Subgroup.card_dvd_of_le le_sup_right
    have h3 : 3 * 2 ^ j ∣ Nat.card (B ⊔ zpowers u : Subgroup G) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right j (by decide)) h2 h1
    exact le_antisymm (Subgroup.card_le_card_group _)
      (hGcard ▸ Nat.le_of_dvd Nat.card_pos h3)
  have hUn : (zpowers u).Normal := by
    have hle : B ⊔ zpowers u ≤ normalizer (zpowers u : Set G) := by
      refine sup_le (fun b hb => ?_) (le_normalizer)
      rw [mem_normalizer_iff]
      intro h
      have hcomm : ∀ k : ℤ, b * u ^ k * b⁻¹ = u ^ k := fun k => by
        rw [((Commute.zpow_left (hc b hb) k).symm).eq, mul_inv_cancel_right]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (hcomm k).symm⟩
      · intro hh
        obtain ⟨k, hk⟩ := hh
        have hk' : u ^ k = b * h * b⁻¹ := hk
        refine ⟨k, ?_⟩
        change u ^ k = h
        have h1 : b * h * b⁻¹ = b * u ^ k * b⁻¹ := by rw [hcomm, hk']
        exact (mul_left_cancel (mul_right_cancel h1)).symm
    rw [hsup] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.2 hle)
  have hq : IsPGroup 2 (G ⧸ zpowers u) := by
    refine IsPGroup.of_card (n := j) ?_
    have h1 := (zpowers u).card_eq_card_quotient_mul_card_subgroup
    rw [hGcard, hUcard] at h1
    omega
  have hU := hG (zpowers u) hq
  have h1 : Nat.card (zpowers u) = Nat.card G := by rw [hU, Subgroup.card_top]
  rw [hUcard, hGcard] at h1
  have hj0 : j = 0 := by
    by_contra hj0
    have : 2 ≤ 2 ^ j := Nat.le_self_pow hj0 2
    omega
  exact hB1 (Subgroup.eq_bot_of_card_eq B (by rw [hj, hj0, pow_zero]))

theorem commute_of_card_le_four (q : ℕ) [NeZero q] (hq : q = 3 ∨ q = 5)
    {J : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q))} (B : Subgroup J) [B.Normal]
    (hBp : IsPGroup 2 B) (hB4 : Nat.card B ≤ 4) (u : J) (hu : u ^ 3 = 1) (b : J) (hb : b ∈ B) :
    u * b = b * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hneg : ∀ x : SpecialLinearGroup (Fin 2) (ZMod q), -1 * x = x * -1 := fun x => by
    rw [neg_one_mul, mul_neg_one]
  obtain ⟨j, hj⟩ := hBp.exists_card_eq
  have hj2 : j ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hb4 : b ^ 4 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard B hb
    rw [hj] at h1
    have h2 : 2 ^ j ∣ 4 := by
      rw [show 4 = 2 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 2 hj2
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)
  have hone_ne : (1 : SpecialLinearGroup (Fin 2) (ZMod q)) ≠ -1 := by
    rcases hq with rfl | rfl <;> decide
  by_cases hb2 : b * b = 1
  ·
    rcases eq_one_or_eq_neg_one_of_mul_self q hq (b : SpecialLinearGroup (Fin 2) (ZMod q))
        (by rw [← Subgroup.coe_mul, hb2]; rfl) with h | h
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h, mul_one, one_mul]
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h, hneg]
  ·
    have hsq : ((b : SpecialLinearGroup (Fin 2) (ZMod q)) * b) = -1 := by
      rcases eq_one_or_eq_neg_one_of_mul_self q hq ((b : SpecialLinearGroup (Fin 2) (ZMod q)) * b)
          (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul,
            show b * b * (b * b) = b ^ 4 by simp [pow_succ, mul_assoc], hb4]; rfl)
          with h | h
      · exact absurd (Subtype.ext (by rw [Subgroup.coe_mul, h]; rfl)) hb2
      · exact h
    have hord : orderOf b = 4 := by
      have h1 : ¬ b ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hb2
      have h2 : b ^ 2 ^ (1 + 1) = 1 := by norm_num; exact hb4
      exact orderOf_eq_prime_pow h1 h2
    have hle : zpowers b ≤ B := (Subgroup.zpowers_le).2 hb
    have hBz : zpowers b = B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact hB4)
    have hc : u * b * u⁻¹ ∈ zpowers b := by
      rw [hBz]
      exact (inferInstance : B.Normal).conj_mem b hb u
    obtain ⟨m, hm, hcm⟩ := (mem_zpowers_iff_mem_range_orderOf.1 hc |> Finset.mem_image.1)
    rw [hord, Finset.mem_range] at hm
    have hcsq :
        (((u * b * u⁻¹) * (u * b * u⁻¹) : J) : SpecialLinearGroup (Fin 2) (ZMod q)) = -1 := by
      have h1 : (u * b * u⁻¹) * (u * b * u⁻¹) = u * (b * b) * u⁻¹ := by group
      rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hsq, ← hneg, mul_assoc,
        ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, mul_one]
    interval_cases m
    · exfalso
      rw [pow_zero] at hcm
      rw [← hcm, mul_one] at hcsq
      exact hone_ne (by rw [← hcsq]; rfl)
    · rw [pow_one] at hcm
      calc u * b = (u * b * u⁻¹) * u := by group
        _ = b * u := by rw [← hcm]
    · exfalso
      rw [← hcm, ← pow_add] at hcsq
      have h1 : b ^ (2 + 2) = 1 := hb4
      rw [h1] at hcsq
      exact hone_ne (by rw [← hcsq]; rfl)
    · exfalso
      have hconj : ∀ k : ℕ, u ^ k * b * u⁻¹ ^ k = b ^ (3 ^ k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc u ^ (k + 1) * b * u⁻¹ ^ (k + 1) = u ^ k * (u * b * u⁻¹) * u⁻¹ ^ k := by group
            _ = u ^ k * b ^ 3 * u⁻¹ ^ k := by rw [← hcm]
            _ = (u ^ k * b * u⁻¹ ^ k) ^ 3 := by rw [inv_pow, conj_pow]
            _ = b ^ (3 ^ (k + 1)) := by rw [ih, ← pow_mul, pow_succ]
      have h1 := hconj 3
      rw [hu, inv_pow, hu, inv_one, one_mul, mul_one] at h1
      have h2 : b ^ (3 ^ 3) = b ^ 3 := by
        rw [show 3 ^ 3 = 4 * 6 + 3 by norm_num, pow_add, pow_mul, hb4, one_pow, one_mul]
      rw [h2] at h1
      apply hb2
      calc b * b = b⁻¹ * (b * b * b) := by group
        _ = b⁻¹ * b ^ 3 := by rw [pow_three, mul_assoc]
        _ = 1 := by rw [← h1, inv_mul_cancel]

theorem card_SL_two (q : ℕ) [Fact q.Prime] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod q)) = q * (q ^ 2 - 1) := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hp : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hp1 : 0 < q - 1 := by omega
  have h1 : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    have h2 : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, sq]
    rw [h2]
    ring
  rw [h1, Nat.mul_div_cancel _ hp1]

theorem le_three_of_two_pow_dvd {k m : ℕ} (h : 2 ^ k ∣ m) (hm : ¬ 16 ∣ m) : k ≤ 3 := by
  by_contra hk
  exact hm ((pow_dvd_pow 2 (show 4 ≤ k by omega)).trans h)

theorem core (q : ℕ) [Fact q.Prime] (hq : q = 3 ∨ q = 5)
    (J : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q))) (hJ : NoPQuotient 2 J)
    (hB1 : pCore 2 J ≠ ⊥) (hJB : Nat.card (J ⧸ pCore 2 J) = 3) :
    Nat.card (pCore 2 J) = 8 ∧ Nat.card J = 24 ∧
    (∃ s : SpecialLinearGroup (Fin 2) (ZMod q),
      (pCore 2 J).map J.subtype = (quatHom q hq).range.map (MulAut.conj s).toMonoidHom) ∧
    Nonempty (J ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) ∧ (q = 3 → J = ⊤) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hBp : IsPGroup 2 (pCore 2 J) := pCore_isPGroup
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hJcard : Nat.card J = 3 * 2 ^ k := by
    rw [(pCore 2 J).card_eq_card_quotient_mul_card_subgroup, hJB, hk]
  have hSL := card_SL_two q
  have hdvd : 3 * 2 ^ k ∣ q * (q ^ 2 - 1) := by
    rw [← hJcard, ← hSL]
    exact Subgroup.card_subgroup_dvd_card J
  have hk3 : k ≤ 3 := by
    rcases hq with rfl | rfl
    · norm_num at hdvd
      exact le_three_of_two_pow_dvd
        (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (show 3 * 2 ^ k ∣ 3 * 8 from hdvd))
        (by norm_num)
    · norm_num at hdvd
      exact le_three_of_two_pow_dvd
        (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (show 3 * 2 ^ k ∣ 3 * 40 from hdvd))
        (by norm_num)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := J) 3
    (by rw [hJcard]; exact dvd_mul_right 3 _)
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hkeq : k = 3 := by
    by_contra hne
    have hB4 : Nat.card (pCore 2 J) ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    exact false_of_commute hJ (pCore 2 J) hBp hJB hB1 u hu fun b hb =>
      commute_of_card_le_four q hq (pCore 2 J) hBp hB4 u hu3 b hb
  subst hkeq
  have hB8 : Nat.card (pCore 2 J) = 8 := by rw [hk]; norm_num
  have hJ24 : Nat.card J = 24 := by rw [hJcard]; norm_num
  have hB'card : Nat.card ((pCore 2 J).map J.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hB8]
  have hQcard := card_range_quatHom q hq
  have hindex : ∀ H : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q)), Nat.card H = 8 →
      ¬ 2 ∣ H.index := by
    intro H hH h2
    have h1 := H.card_mul_index
    rw [hH, hSL] at h1
    rcases hq with rfl | rfl <;> norm_num at h1 <;> omega
  have hB'p : IsPGroup 2 ((pCore 2 J).map J.subtype) :=
    IsPGroup.of_card (n := 3) (by rw [hB'card]; norm_num)
  have hQp : IsPGroup 2 (quatHom q hq).range :=
    IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) (ZMod q))
    (hQp.toSylow (hindex _ hQcard)) (hB'p.toSylow (hindex _ hB'card))
  have hconj : (pCore 2 J).map J.subtype =
      (quatHom q hq).range.map (MulAut.conj s).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 (SpecialLinearGroup (Fin 2) (ZMod q)) =>
      (P : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q)))) hs
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    rfl
  refine ⟨hB8, hJ24, ⟨s, hconj⟩, ?_, fun h3 => ?_⟩
  swap
  · subst h3
    apply Subgroup.eq_top_of_card_eq
    rw [hJ24, hSL]
    norm_num
  have hQeq : (quatHom q hq).range.map (MulAut.conj s).toMonoidHom = (pCore 2 J).map J.subtype :=
    hconj.symm
  let Φ₁ : QuaternionGroup 2 ≃* pCore 2 J :=
    (MonoidHom.ofInjective (quatHom_injective q hq)).trans
      (((MulAut.conj s).subgroupMap (quatHom q hq).range).trans
        ((MulEquiv.subgroupCongr hQeq).trans
          (Subgroup.equivMapOfInjective (pCore 2 J) J.subtype J.subtype_injective).symm))
  let αE : QuaternionGroup 2 ≃* QuaternionGroup 2 :=
    (Φ₁.trans (MulAut.conjNormal u)).trans Φ₁.symm
  have hαE : ∀ g, Φ₁ (αE g) = MulAut.conjNormal u (Φ₁ g) := fun g => by
    simp only [αE, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hcN3 : ∀ n : pCore 2 J,
      MulAut.conjNormal u (MulAut.conjNormal u (MulAut.conjNormal u n)) = n := fun n => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
      ← pow_three', hu3, map_one, MulAut.one_apply]
  have hα3 : ∀ g, αE (αE (αE g)) = g := fun g => by
    apply Φ₁.injective
    rw [hαE, hαE, hαE, hcN3]
  have hα1 : ∃ g, αE g ≠ g := by
    by_contra hcon
    push Not at hcon
    apply false_of_commute hJ (pCore 2 J) hBp hJB hB1 u hu
    intro b hb
    obtain ⟨g, hg⟩ := Φ₁.surjective ⟨b, hb⟩
    have h2 : MulAut.conjNormal u (Φ₁ g) = Φ₁ g := by rw [← hαE, hcon g]
    rw [hg] at h2
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    calc u * b = (u * b * u⁻¹) * u := by group
      _ = b * u := by rw [h3]
  have hαeval : ∀ g, αE g = quatEval (αE (QuaternionGroup.a 1)) (αE (QuaternionGroup.xa 0)) g := by
    intro g
    cases g with
    | a i =>
      change αE (QuaternionGroup.a i) = αE (QuaternionGroup.a 1) ^ i.val
      rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change αE (QuaternionGroup.xa i) =
        αE (QuaternionGroup.xa 0) * αE (QuaternionGroup.a 1) ^ i.val
      rw [← map_pow, ← map_mul, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val,
        QuaternionGroup.xa_mul_a, zero_add]
  obtain ⟨x', y', hmul', hinj', hint⟩ :=
    exists_intertwine (αE (QuaternionGroup.a 1)) (αE (QuaternionGroup.xa 0))
      (fun g h => by rw [← hαeval, ← hαeval, ← hαeval, map_mul])
      (fun g => by rw [← hαeval, ← hαeval, ← hαeval, hα3])
      (by
        obtain ⟨g, hg⟩ := hα1
        exact ⟨g, by rwa [← hαeval]⟩)
  let ψ0 : QuaternionGroup 2 →* QuaternionGroup 2 := MonoidHom.mk' (quatEval x' y') hmul'
  have hψinj : Function.Injective ψ0 := fun g h hgh => hinj' g h hgh
  let ψ : QuaternionGroup 2 ≃* QuaternionGroup 2 :=
    MulEquiv.ofBijective ψ0 ⟨hψinj, Finite.injective_iff_surjective.1 hψinj⟩
  have hψ : ∀ g, ψ g = quatEval x' y' g := fun g => rfl
  let ΦJ : QuaternionGroup 2 ≃* pCore 2 J := ψ.trans Φ₁
  have hΦJ : ∀ g, ΦJ (quatOmega g) = MulAut.conjNormal u (ΦJ g) := by
    intro g
    simp only [ΦJ, MulEquiv.trans_apply]
    rw [hψ, hint, ← hψ, ← hαeval, hαE]
  let Φ₃ : QuaternionGroup 2 ≃* (quatHom 3 (Or.inl rfl)).range :=
    MonoidHom.ofInjective (quatHom_injective 3 (Or.inl rfl))
  have hΦ₃ : ∀ g, Φ₃ (quatOmega g) = MulAut.conjNormal slU (Φ₃ g) := by
    intro g
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply,
      quatOmega_intertwine]
  let Θ : pCore 2 J ≃* (quatHom 3 (Or.inl rfl)).range := ΦJ.symm.trans Φ₃
  have hΘ : ∀ n, Θ (MulAut.conjNormal u n) = MulAut.conjNormal slU (Θ n) := by
    intro n
    obtain ⟨m, rfl⟩ := ΦJ.surjective n
    simp only [Θ, MulEquiv.trans_apply]
    rw [← hΦJ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hΦ₃]
  have hcompl : (pCore 2 J).IsComplement' (zpowers u) := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [hB8, Nat.card_zpowers, hu, hJ24]
    · refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hB8, Nat.card_zpowers, hu]
      decide
  exact nonempty_mulEquiv_of_intertwine (pCore 2 J) (quatHom 3 (Or.inl rfl)).range hcompl
    isComplement'_three (by rw [hu, orderOf_slU]) Θ hΘ

@[expose] def glA (q : ℕ) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) :=
  SpecialLinearGroup.toGL (slA q)

@[expose] def glB (q : ℕ) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) :=
  SpecialLinearGroup.toGL (slB q)

@[expose] def quatActor (q : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :=
  closure {glA q, glB q}

theorem quatActor_eq (q : ℕ) (hq : q = 3 ∨ q = 5) :
    quatActor q = (quatHom q hq).range.map SpecialLinearGroup.toGL := by
  have hA : glA q ∈ quatActor q := subset_closure (Set.mem_insert _ _)
  have hB : glB q ∈ quatActor q := subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · rw [quatActor, closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨quatHom q hq (QuaternionGroup.a 1), ⟨_, rfl⟩, ?_⟩
      change SpecialLinearGroup.toGL (slA q ^ 1) = _
      rw [pow_one]
      rfl
    · refine ⟨quatHom q hq (QuaternionGroup.xa 0), ⟨_, rfl⟩, ?_⟩
      change SpecialLinearGroup.toGL (slB q * slA q ^ 0) = _
      rw [pow_zero, mul_one]
      rfl
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    cases g with
    | a i =>
      change SpecialLinearGroup.toGL (slA q ^ i.val) ∈ quatActor q
      rw [map_pow]
      exact pow_mem hA _
    | xa i =>
      change SpecialLinearGroup.toGL (slB q * slA q ^ i.val) ∈ quatActor q
      rw [map_mul, map_pow]
      exact mul_mem hB (pow_mem hA _)

theorem card_quatActor (q : ℕ) (hq : q = 3 ∨ q = 5) : Nat.card (quatActor q) = 8 := by
  rw [quatActor_eq q hq, card_map_of_injective SpecialLinearGroup.toGL_injective,
    card_range_quatHom]

theorem coe_quatActor (q : ℕ) (hq : q = 3 ∨ q = 5) :
    (quatActor q : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) =
      {1, -1, glA q, -glA q, glB q, -glB q, glA q * glB q, -(glA q * glB q)} := by
  ext x
  rw [SetLike.mem_coe, quatActor_eq q hq]
  simp only [mem_map, MonoidHom.mem_range, exists_exists_eq_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    revert g
    rcases hq with rfl | rfl <;> decide
  · rcases hq with rfl | rfl <;> rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem glA_mul_glA (q : ℕ) (hq : q = 3 ∨ q = 5) : glA q * glA q = -1 := by
  rcases hq with rfl | rfl <;> decide

theorem glB_mul_glB (q : ℕ) (hq : q = 3 ∨ q = 5) : glB q * glB q = -1 := by
  rcases hq with rfl | rfl <;> decide

theorem glA_mul_glB (q : ℕ) (hq : q = 3 ∨ q = 5) : glA q * glB q = -(glB q * glA q) := by
  rcases hq with rfl | rfl <;> decide

@[expose] noncomputable def slEquiv {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (e : Basis (Fin 2) K W) (s : Matrix.SpecialLinearGroup (Fin 2) K) : W ≃ₗ[K] W :=
  LinearEquiv.ofLinearMap (Matrix.toLin e e s.1) (Matrix.toLin e e (s⁻¹).1)
    (by rw [← Matrix.toLin_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one])

theorem toMatrix_map_slEquiv {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (e : Basis (Fin 2) K W) (s : Matrix.SpecialLinearGroup (Fin 2) K) (f : W →ₗ[K] W) :
    LinearMap.toMatrix (e.map (slEquiv e s)) (e.map (slEquiv e s)) f =
      (s⁻¹).1 * LinearMap.toMatrix e e f * s.1 := by
  have h1 : LinearMap.toMatrix (e.map (slEquiv e s)) (e.map (slEquiv e s)) f =
      LinearMap.toMatrix e e (Matrix.toLin e e (s⁻¹).1 ∘ₗ f ∘ₗ Matrix.toLin e e s.1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Basis.map_repr, Basis.map_apply]
    rfl
  rw [h1, LinearMap.toMatrix_comp e e e, LinearMap.toMatrix_comp e e e, LinearMap.toMatrix_toLin,
    LinearMap.toMatrix_toLin, Matrix.mul_assoc]

theorem no_common_line (q : ℕ) (hq : q = 3 ∨ q = 5) : ∀ x y : ZMod q,
    x * ((slA q).1 1 0 * x + (slA q).1 1 1 * y) - ((slA q).1 0 0 * x + (slA q).1 0 1 * y) * y = 0 →
    x * ((slB q).1 1 0 * x + (slB q).1 1 1 * y) - ((slB q).1 0 0 * x + (slB q).1 0 1 * y) * y = 0 →
    x = 0 ∧ y = 0 := by
  rcases hq with rfl | rfl <;> decide

theorem eq_bot_or_eq_top_of_invariant (q : ℕ) [Fact q.Prime] (hq : q = 3 ∨ q = 5) {W : Type*}
    [AddCommGroup W] [Module (ZMod q) W] (e : Basis (Fin 2) (ZMod q) W) (f₁ f₂ : W →ₗ[ZMod q] W)
    (h₁ : LinearMap.toMatrix e e f₁ = (slA q).1) (h₂ : LinearMap.toMatrix e e f₂ = (slB q).1)
    (U : Submodule (ZMod q) W) (hU₁ : ∀ w ∈ U, f₁ w ∈ U) (hU₂ : ∀ w ∈ U, f₂ w ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcon.1
  have hdet0 : ∀ w ∈ U, e.det ![u, w] = 0 := by
    intro w hw
    by_contra hne
    have h := (e.is_basis_iff_det (v := ![u, w])).2 (isUnit_iff_ne_zero.2 hne)
    apply hcon.2
    rw [eq_top_iff, ← h.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact huU
    · exact hw
  have hcoord : ∀ (f : W →ₗ[ZMod q] W) (i : Fin 2), e.repr (f u) i =
      LinearMap.toMatrix e e f i 0 * e.repr u 0 + LinearMap.toMatrix e e f i 1 * e.repr u 1 := by
    intro f i
    rw [← LinearMap.toMatrix_mulVec_repr e e f u, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd : ∀ w, e.det ![u, w] = e.repr u 0 * e.repr w 1 - e.repr w 0 * e.repr u 1 := by
    intro w
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply]
    rfl
  have k1 := hdet0 _ (hU₁ u huU)
  have k2 := hdet0 _ (hU₂ u huU)
  rw [hd, hcoord, hcoord, h₁] at k1
  rw [hd, hcoord, hcoord, h₂] at k2
  obtain ⟨hx, hy⟩ := no_common_line q hq _ _ k1 k2
  apply hu0
  apply e.repr.injective
  ext i
  fin_cases i
  · simpa using hx
  · simpa using hy

theorem residual_three_extension_in_two_plane_is_quaternion_actor (q : ℕ) (hq : q = 3 ∨ q = 5)
    {W : Type*} [AddCommGroup W] [Module (ZMod q) W] (hW : finrank (ZMod q) W = 2)
    (J : Subgroup (LinearMap.GeneralLinearGroup (ZMod q) W)) (hJ : NoPQuotient 2 J)
    (hB1 : pCore 2 J ≠ ⊥) (hJB : Nat.card (J ⧸ pCore 2 J) = 3) :
    J ≤ (_root_.SpecialLinearGroup.toGeneralLinearGroup (R := ZMod q) (V := W)).range ∧
    Nat.card (pCore 2 J) = 8 ∧ Nat.card J = 24 ∧
    (∀ U : Submodule (ZMod q) W, (∀ b ∈ pCore 2 J, ∀ w ∈ U,
      ((b : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) w ∈ U) →
      U = ⊥ ∨ U = ⊤) ∧
    (∃ e : Basis (Fin 2) (ZMod q) W, ∀ M : Matrix.GeneralLinearGroup (Fin 2) (ZMod q),
      M ∈ quatActor q ↔ ∃ b ∈ pCore 2 J, LinearMap.toMatrix e e
        ((b : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) = M) ∧
    ((glA q : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![0, 1; -1, 0] ∧
      (q = 3 → (glB q : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, 1; 1, -1]) ∧
      (q = 5 → (glB q : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![2, 0; 0, 3]) ∧
      (quatActor q : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) =
        {1, -1, glA q, -glA q, glB q, -glB q, glA q * glB q, -(glA q * glB q)} ∧
      glA q * glA q = -1 ∧ glB q * glB q = -1 ∧ glA q * glB q = -(glB q * glA q)) ∧
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    (q = 3 →
      J = (_root_.SpecialLinearGroup.toGeneralLinearGroup (R := ZMod q) (V := W)).range) := by
  classical
  have : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (ZMod q) W := Module.finite_of_finrank_eq_succ hW
  let e₀ : Basis (Fin 2) (ZMod q) W := Module.finBasisOfFinrankEq (ZMod q) W hW
  have hdet : ∀ g ∈ J,
      LinearMap.det ((g : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) = 1 := by
    intro g hg
    have hK : IsPGroup 2 (ZMod q)ˣ := by
      rcases hq with rfl | rfl
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card, ZMod.card_units]; rfl)
      · exact IsPGroup.of_card (n := 2) (by rw [Nat.card_eq_fintype_card, ZMod.card_units]; rfl)
    let f : J →* (ZMod q)ˣ :=
      (Units.map (LinearMap.det : (W →ₗ[ZMod q] W) →* ZMod q)).comp J.subtype
    have hker : f.ker = ⊤ :=
      hJ f.ker (hK.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f))
    have h1 : f ⟨g, hg⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      trivial
    exact congrArg Units.val h1
  have hSL : J ≤ (_root_.SpecialLinearGroup.toGeneralLinearGroup (R := ZMod q) (V := W)).range := by
    intro g hg
    have h1 : g ∈ Set.range
        ⇑(_root_.SpecialLinearGroup.toGeneralLinearGroup (R := ZMod q) (V := W)) := by
      rw [_root_.SpecialLinearGroup.mem_range_toGeneralLinearGroup_iff]
      apply Units.ext
      rw [LinearEquiv.coe_det]
      exact hdet g hg
    exact h1
  let ρ : J →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
    { toFun := fun g => ⟨LinearMap.toMatrix e₀ e₀
          ((g : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W),
        by rw [LinearMap.det_toMatrix]; exact hdet g g.2⟩
      map_one' := Subtype.ext (LinearMap.toMatrix_one e₀)
      map_mul' := fun g h => Subtype.ext (LinearMap.toMatrix_mul e₀ _ _) }
  have hρinj : Function.Injective ρ := by
    intro g h hgh
    have h1 : LinearMap.toMatrix e₀ e₀
        ((g : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) =
        LinearMap.toMatrix e₀ e₀
          ((h : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) :=
      congrArg Subtype.val hgh
    exact Subtype.ext (Units.ext ((LinearMap.toMatrix e₀ e₀).injective h1))
  set J₁ := ρ.range with hJ₁def
  let Φ : J ≃* J₁ := MonoidHom.ofInjective hρinj
  have : Finite J := Finite.of_equiv _ Φ.symm.toEquiv
  have hJ₁ : NoPQuotient 2 J₁ := noPQuotient_of_surjective Φ.toMonoidHom Φ.surjective hJ
  have hBmap : (pCore 2 J).map Φ.toMonoidHom = pCore 2 J₁ := pCore_map_iso 2 Φ
  have hBcard : Nat.card (pCore 2 J₁) = Nat.card (pCore 2 J) := by
    rw [← hBmap, card_map_of_injective (f := Φ.toMonoidHom) Φ.injective]
  have hJcard : Nat.card J₁ = Nat.card J := Nat.card_congr Φ.symm.toEquiv
  have hB1' : pCore 2 J₁ ≠ ⊥ := by
    rw [← hBmap]
    exact fun h => hB1 ((map_eq_bot_iff_of_injective (f := Φ.toMonoidHom) _ Φ.injective).1 h)
  have hJB₁ : Nat.card (J₁ ⧸ pCore 2 J₁) = 3 := by
    have h1 := (pCore 2 J).card_eq_card_quotient_mul_card_subgroup
    have h2 := (pCore 2 J₁).card_eq_card_quotient_mul_card_subgroup
    rw [hJB] at h1
    rw [hJcard, hBcard, h1] at h2
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h2).symm
  obtain ⟨hB8, hJ24, ⟨s, hs⟩, ⟨iso⟩, h3⟩ := core q hq J₁ hJ₁ hB1' hJB₁
  have hBQ : ∀ b : J, b ∈ pCore 2 J → ∃ x ∈ (quatHom q hq).range, s * x * s⁻¹ = ρ b := by
    intro b hb
    have h1 : ρ b ∈ (pCore 2 J₁).map J₁.subtype := by
      rw [← hBmap]
      exact ⟨Φ b, ⟨b, hb, rfl⟩, rfl⟩
    rw [hs] at h1
    obtain ⟨x, hx, hxb⟩ := h1
    exact ⟨x, hx, hxb⟩
  have hQB : ∀ x ∈ (quatHom q hq).range, ∃ b : J, b ∈ pCore 2 J ∧ ρ b = s * x * s⁻¹ := by
    intro x hx
    have h1 : s * x * s⁻¹ ∈ (pCore 2 J₁).map J₁.subtype := by
      rw [hs]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hBmap] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨b, hb, hyx⟩
  let e : Basis (Fin 2) (ZMod q) W := e₀.map (slEquiv e₀ s)
  have he : ∀ g : J, LinearMap.toMatrix e e
      ((g : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) = (s⁻¹ * ρ g * s).1 := by
    intro g
    rw [toMatrix_map_slEquiv]
    rfl
  have hbasis : ∀ M : Matrix.GeneralLinearGroup (Fin 2) (ZMod q), M ∈ quatActor q ↔
      ∃ b ∈ pCore 2 J, LinearMap.toMatrix e e
        ((b : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) = M := by
    intro M
    rw [quatActor_eq q hq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, hb, hbx⟩ := hQB x hx
      refine ⟨b, hb, ?_⟩
      have h1 : s⁻¹ * ρ b * s = x := by rw [hbx]; group
      rw [he, h1]
      rfl
    · rintro ⟨b, hb, hbM⟩
      obtain ⟨x, hx, hxb⟩ := hBQ b hb
      refine ⟨x, hx, Units.ext ?_⟩
      have h1 : s⁻¹ * ρ b * s = x := by rw [← hxb]; group
      rw [← hbM, he, h1]
      rfl
  have hirr : ∀ U : Submodule (ZMod q) W, (∀ b ∈ pCore 2 J, ∀ w ∈ U,
      ((b : LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W) w ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    obtain ⟨b₁, hb₁, h₁⟩ := (hbasis (glA q)).1 (subset_closure (Set.mem_insert _ _))
    obtain ⟨b₂, hb₂, h₂⟩ := (hbasis (glB q)).1 (subset_closure (Set.mem_insert_of_mem _ rfl))
    exact eq_bot_or_eq_top_of_invariant q hq e _ _ h₁ h₂ U (hU b₁ hb₁) (hU b₂ hb₂)
  have hq3 : q = 3 →
      J = (_root_.SpecialLinearGroup.toGeneralLinearGroup (R := ZMod q) (V := W)).range := by
    intro hq3
    refine le_antisymm hSL ?_
    rintro _ ⟨u, rfl⟩
    have hdetu : (LinearMap.toMatrix e₀ e₀ ((_root_.SpecialLinearGroup.toGeneralLinearGroup u :
        LinearMap.GeneralLinearGroup (ZMod q) W) : W →ₗ[ZMod q] W)).det = 1 := by
      rw [LinearMap.det_toMatrix]
      exact _root_.SpecialLinearGroup.det_eq_one u
    have hmem : (⟨_, hdetu⟩ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) ∈ J₁ := by
      rw [h3 hq3]
      trivial
    obtain ⟨j, hj⟩ := hmem
    have hju : (j : LinearMap.GeneralLinearGroup (ZMod q) W) =
        _root_.SpecialLinearGroup.toGeneralLinearGroup u := by
      apply Units.ext
      apply (LinearMap.toMatrix e₀ e₀).injective
      exact congrArg Subtype.val hj
    rw [← hju]
    exact j.2
  refine ⟨hSL, by rw [← hBcard]; exact hB8, by rw [← hJcard]; exact hJ24, hirr, ⟨e, hbasis⟩,
    ⟨rfl, fun h => by subst h; rfl, fun h => by subst h; rfl, coe_quatActor q hq, glA_mul_glA q hq,
      glB_mul_glB q hq, glA_mul_glB q hq⟩, ⟨Φ.trans iso⟩, hq3⟩

end QuaternionActor

end CFSG.Quasithin.SteinbergBX
