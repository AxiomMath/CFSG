module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FixFactsA7
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open Equiv Matrix CFSG.Quasithin

namespace FFL

section Lift

variable {G H : Type*} [Group G] [Group H] {f : G →* H}

theorem eq_of_sq_eq_one (hk : ∀ x, f x = 1 → (∀ y, x * y = y * x) ∧ x ^ 3 = 1) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : f a = f b) : a = b := by
  set w := a⁻¹ * b with hw
  have hfw : f w = 1 := by rw [hw, map_mul, map_inv, hab, inv_mul_cancel]
  obtain ⟨hwc, hw3⟩ := hk w hfw
  have hb' : b = a * w := by rw [hw, mul_inv_cancel_left]
  have hw2 : w * w = 1 := by
    calc w * w = (a * a) * (w * w) := by rw [ha, one_mul]
      _ = a * (a * w) * w := by simp only [mul_assoc]
      _ = a * (w * a) * w := by rw [hwc a]
      _ = (a * w) * (a * w) := by simp only [mul_assoc]
      _ = 1 := by rw [← hb', hb]
  have hw1 : w = 1 := by
    have h3 : w = w ^ 3 * (w * w)⁻¹ := by group
    rw [h3, hw3, hw2, inv_one, one_mul]
  rw [hb', hw1, mul_one]

theorem exists_sq_lift (hk : ∀ x, f x = 1 → (∀ y, x * y = y * x) ∧ x ^ 3 = 1)
    (hf : Function.Surjective f) {σ : H} (hσ : σ * σ = 1) : ∃ t : G, t * t = 1 ∧ f t = σ := by
  obtain ⟨x, rfl⟩ := hf σ
  refine ⟨x ^ 3, ?_, ?_⟩
  · have h1 : f (x * x) = 1 := by rw [map_mul, hσ]
    obtain ⟨-, h3⟩ := hk _ h1
    rw [← pow_add, show 3 + 3 = 2 * 3 from rfl, pow_mul, pow_two, h3]
  · rw [map_pow, pow_succ, pow_two, hσ, one_mul]

theorem comm_of_sq_eq_one (hk : ∀ x, f x = 1 → (∀ y, x * y = y * x) ∧ x ^ 3 = 1) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : f a * f b = f b * f a) : a * b = b * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hinv : a * b * a⁻¹ * (a * b * a⁻¹) = 1 := by
    rw [hai]
    calc a * b * a * (a * b * a) = a * b * (a * a) * (b * a) := by simp only [mul_assoc]
      _ = a * (b * b) * a := by rw [ha, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [hb, mul_one, ha]
  have h := eq_of_sq_eq_one hk (a := a * b * a⁻¹) (b := b) hinv hb
    (by rw [map_mul, map_mul, map_inv, hab, mul_inv_cancel_right])
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h]

theorem mul_eq_of_sq_eq_one (hk : ∀ x, f x = 1 → (∀ y, x * y = y * x) ∧ x ^ 3 = 1) {g t s : G}
    (ht : t * t = 1) (hs : s * s = 1) (h : f t * f g = f g * f s) : t * g = g * s := by
  have h1 := eq_of_sq_eq_one hk (a := g⁻¹ * t * g) (b := s)
    (by rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht, mul_one,
      inv_mul_cancel])
    hs (by rw [map_mul, map_mul, map_inv, mul_assoc, h, inv_mul_cancel_left])
  calc t * g = g * (g⁻¹ * t * g) := by group
    _ = g * s := by rw [h1]

end Lift

section Fix

variable {K : Type} [Field K]

@[expose] noncomputable def fixSub3 (A : Matrix (Fin 3) (Fin 3) K) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (Matrix.toLin' A - LinearMap.id)

theorem mem_fixSub3 {A : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} :
    v ∈ fixSub3 A ↔ A *ᵥ v = v := by
  rw [fixSub3, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem eq_one_of_forall_mulVec {A : Matrix (Fin 3) (Fin 3) K} (h : ∀ v, A *ᵥ v = v) : A = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_mulVec, h]

theorem finrank_fixSub3_le {A : Matrix (Fin 3) (Fin 3) K} (hA : A ≠ 1) :
    Module.finrank K ↥(fixSub3 A) ≤ 2 := by
  have hne : fixSub3 A ≠ ⊤ := by
    intro h
    apply hA
    apply eq_one_of_forall_mulVec
    intro v
    exact mem_fixSub3.1 (h ▸ Submodule.mem_top)
  have h := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at h
  omega

theorem fixSub3_dichotomy {A B : Matrix (Fin 3) (Fin 3) K} (hA : A ≠ 1) (hB : B ≠ 1) :
    Module.finrank K ↥(fixSub3 A ⊓ fixSub3 B) ≤ 1 ∨ fixSub3 A = fixSub3 B := by
  by_cases h : Module.finrank K ↥(fixSub3 A ⊓ fixSub3 B) ≤ 1
  · exact Or.inl h
  · right
    have hA2 := finrank_fixSub3_le hA
    have hB2 := finrank_fixSub3_le hB
    have e1 : fixSub3 A ⊓ fixSub3 B = fixSub3 A :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
    have e2 : fixSub3 A ⊓ fixSub3 B = fixSub3 B :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
    exact e1.symm.trans e2

theorem eq_bot_or_line {F : Submodule K (Fin 3 → K)} (hF : Module.finrank K ↥F ≤ 1) :
    F = ⊥ ∨ ∃ a ∈ F, a ≠ 0 ∧ ∀ v ∈ F, ∃ μ : K, v = μ • a := by
  by_cases h : F = ⊥
  · exact Or.inl h
  · right
    obtain ⟨a, haF, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have h1 : Module.finrank K ↥F = 1 := by
      have : Module.finrank K ↥F ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.1 h0)
      omega
    have h2 := (finrank_eq_one_iff_of_nonzero' (⟨a, haF⟩ : ↥F)
      (fun h0 => ha0 (congrArg Subtype.val h0))).1 h1
    refine ⟨a, haF, ha0, fun v hv => ?_⟩
    obtain ⟨μ, hμ⟩ := h2 ⟨v, hv⟩
    exact ⟨μ, (congrArg Subtype.val hμ).symm⟩

variable [CharP K 2]

theorem comm_of_fix_eq {B C : Matrix (Fin 3) (Fin 3) K} (hB : B * B = 1) (hC : C * C = 1)
    (h : ∀ v, B *ᵥ v = v ↔ C *ᵥ v = v) : B * C = C * B := by
  have hneg : ∀ w : Fin 3 → K, -w = w := fun w => by
    funext i
    exact CharTwo.neg_eq (w i)
  have hfix : ∀ {A : Matrix (Fin 3) (Fin 3) K}, A * A = 1 → ∀ v,
      A *ᵥ (A *ᵥ v + v) = A *ᵥ v + v := by
    intro A hA v
    rw [mulVec_add, mulVec_mulVec, hA, one_mulVec, add_comm]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec]
  have h1 : B *ᵥ (C *ᵥ v + v) = C *ᵥ v + v := (h _).2 (hfix hC v)
  have h2 : C *ᵥ (B *ᵥ v + v) = B *ᵥ v + v := (h _).1 (hfix hB v)
  rw [mulVec_add] at h1 h2
  have e1 : B *ᵥ (C *ᵥ v) = C *ᵥ v + v + B *ᵥ v := by
    have := eq_sub_of_add_eq h1
    rwa [sub_eq_add_neg, hneg] at this
  have e2 : C *ᵥ (B *ᵥ v) = B *ᵥ v + v + C *ᵥ v := by
    have := eq_sub_of_add_eq h2
    rwa [sub_eq_add_neg, hneg] at this
  rw [e1, e2]
  abel

end Fix

section Mat

variable {K : Type} [Field K] {Γ₀ : Subgroup (GL (Fin 3) K)}

abbrev glMat (x : ↥Γ₀) : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem glMat_mul (x y : ↥Γ₀) : glMat (x * y) = glMat x * glMat y := rfl

theorem glMat_one : glMat (1 : ↥Γ₀) = 1 := rfl

theorem glMat_injective {x y : ↥Γ₀} (h : glMat x = glMat y) : x = y := Subtype.ext (Units.ext h)

theorem glMat_mulVec_mul (x y : ↥Γ₀) (v : Fin 3 → K) :
    glMat (x * y) *ᵥ v = glMat x *ᵥ (glMat y *ᵥ v) := by
  rw [glMat_mul, mulVec_mulVec]

theorem glMat_mulVec_pow_three (x : ↥Γ₀) (v : Fin 3 → K) :
    glMat (x ^ 3) *ᵥ v = glMat x *ᵥ (glMat x *ᵥ (glMat x *ᵥ v)) := by
  rw [pow_succ, pow_two, glMat_mulVec_mul, glMat_mulVec_mul]

theorem glMat_mulVec_inv (x : ↥Γ₀) (v : Fin 3 → K) : glMat x⁻¹ *ᵥ (glMat x *ᵥ v) = v := by
  rw [← glMat_mulVec_mul, inv_mul_cancel, glMat_one, one_mulVec]

theorem exists_gamma_of_line [Fintype K] [CharP K 2] (hK : Fintype.card K = 4) {H : Type*}
    [Group H] (f : ↥Γ₀ →* H) (hscal : ∀ x, f x = 1 → ∃ d : K, glMat x = d • 1) {z : ↥Γ₀}
    (hfz : f z = 1) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {t s g : ↥Γ₀} (hfg : f g ≠ 1)
    (hfg3 : f g ^ 3 = 1) (hF : Module.finrank K ↥(fixSub3 (glMat t) ⊓ fixSub3 (glMat s)) ≤ 1)
    (hinv : ∀ v, glMat t *ᵥ v = v → glMat s *ᵥ v = v →
      glMat t *ᵥ (glMat g *ᵥ v) = glMat g *ᵥ v ∧ glMat s *ᵥ (glMat g *ᵥ v) = glMat g *ᵥ v) :
    ∃ γ : ↥Γ₀, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
      ∀ v, glMat t *ᵥ v = v → glMat s *ᵥ v = v → glMat γ *ᵥ v = v := by
  have hmemF : ∀ v, glMat t *ᵥ v = v → glMat s *ᵥ v = v →
      v ∈ fixSub3 (glMat t) ⊓ fixSub3 (glMat s) :=
    fun v h1 h2 => ⟨mem_fixSub3.2 h1, mem_fixSub3.2 h2⟩
  rcases eq_bot_or_line hF with hbot | ⟨a, haF, ha0, hline⟩
  · refine ⟨z, hz3, hz1, fun v h1 h2 => ?_⟩
    have hv := hmemF v h1 h2
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv, mulVec_zero]
  · have ha1 : glMat t *ᵥ a = a := mem_fixSub3.1 haF.1
    have ha2 : glMat s *ᵥ a = a := mem_fixSub3.1 haF.2
    obtain ⟨c, hc⟩ := hscal z hfz
    have hzv : ∀ v, glMat z *ᵥ v = c • v := fun v => by rw [hc, smul_mulVec, one_mulVec]
    have hsmul_eq : ∀ d : K, d • a = a → d = 1 := by
      intro d hd
      have h0 : (d - 1) • a = 0 := by rw [sub_smul, one_smul, hd, sub_self]
      rcases smul_eq_zero.1 h0 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h ha0
    have hc3 : c ^ 3 = 1 := by
      apply hsmul_eq
      have h := glMat_mulVec_pow_three z a
      rw [hz3, glMat_one, one_mulVec, hzv, hzv, hzv, smul_smul, smul_smul] at h
      rw [show c ^ 3 = c * c * c by ring]
      exact h.symm
    have hc1 : c ≠ 1 := by
      intro h1
      apply hz1
      apply glMat_injective
      rw [hc, h1, one_smul, glMat_one]
    have hcc : 1 + c + c ^ 2 = 0 := by
      have h : (c - 1) * (1 + c + c ^ 2) = 0 := by linear_combination hc3
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hc1)
    obtain ⟨l, hl⟩ := hline _ (hmemF _ (hinv a ha1 ha2).1 (hinv a ha1 ha2).2)
    have hl0 : l ≠ 0 := by
      intro h0
      apply ha0
      rw [← glMat_mulVec_inv g a, hl, h0, zero_smul, mulVec_zero]
    have hl3 : l ^ 3 = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one l hl0
      rwa [hK] at h
    have hlc : l = 1 ∨ l = c ∨ l = c ^ 2 := by
      have h : (l - 1) * (l - c) * (l - c ^ 2) = 0 := by
        linear_combination hl3 - l ^ 2 * hcc + l * c * hcc - hc3
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (Or.inl (sub_eq_zero.1 h))
      · exact Or.inr (Or.inr (sub_eq_zero.1 h))
    obtain ⟨γ, hfγ, hγa⟩ : ∃ γ : ↥Γ₀, f γ = f g ∧ glMat γ *ᵥ a = a := by
      rcases hlc with hl1 | hl1 | hl1 <;> rw [hl1] at hl
      · exact ⟨g, rfl, by rw [hl, one_smul]⟩
      · refine ⟨g * z * z, by rw [map_mul, map_mul, hfz, mul_one, mul_one], ?_⟩
        rw [glMat_mulVec_mul, glMat_mulVec_mul, hzv, hzv, smul_smul, mulVec_smul, hl, smul_smul,
          show c * c * c = c ^ 3 by ring, hc3, one_smul]
      · refine ⟨g * z, by rw [map_mul, hfz, mul_one], ?_⟩
        rw [glMat_mulVec_mul, hzv, mulVec_smul, hl, smul_smul, show c * c ^ 2 = c ^ 3 by ring,
          hc3, one_smul]
    refine ⟨γ, ?_, fun h => hfg (by rw [← hfγ, h, map_one]), fun v h1 h2 => ?_⟩
    · obtain ⟨d, hd⟩ := hscal (γ ^ 3) (by rw [map_pow, hfγ, hfg3])
      have h := glMat_mulVec_pow_three γ a
      rw [hγa, hγa, hγa, hd, smul_mulVec, one_mulVec] at h
      have hd1 : d = 1 := hsmul_eq d h
      apply glMat_injective
      rw [hd, hd1, one_smul, glMat_one]
    · obtain ⟨μ, hμ⟩ := hline v (hmemF v h1 h2)
      rw [hμ, mulVec_smul, hγa]

end Mat

@[expose] def a6s₁P : Perm (Fin 6) := swap 0 2 * swap 1 3
@[expose] def a6s₂P : Perm (Fin 6) := swap 0 1 * swap 2 3
@[expose] def a6s₃P : Perm (Fin 6) := swap 0 2 * swap 4 5
@[expose] def a6g₁P : Perm (Fin 6) := swap 0 1 * swap 1 2
@[expose] def a6g₂P : Perm (Fin 6) := swap 0 1 * swap 1 4 * (swap 2 3 * swap 3 5)

theorem a6P_mem : a6s₁P ∈ alternatingGroup (Fin 6) ∧ a6s₂P ∈ alternatingGroup (Fin 6) ∧
    a6s₃P ∈ alternatingGroup (Fin 6) ∧ a6g₁P ∈ alternatingGroup (Fin 6) ∧
    a6g₂P ∈ alternatingGroup (Fin 6) := by
  simp only [Perm.mem_alternatingGroup, a6s₁P, a6s₂P, a6s₃P, a6g₁P, a6g₂P]
  decide +kernel

@[expose] def a6s₁ : ↥(alternatingGroup (Fin 6)) := ⟨a6s₁P, a6P_mem.1⟩
@[expose] def a6s₂ : ↥(alternatingGroup (Fin 6)) := ⟨a6s₂P, a6P_mem.2.1⟩
@[expose] def a6s₃ : ↥(alternatingGroup (Fin 6)) := ⟨a6s₃P, a6P_mem.2.2.1⟩
@[expose] def a6g₁ : ↥(alternatingGroup (Fin 6)) := ⟨a6g₁P, a6P_mem.2.2.2.1⟩
@[expose] def a6g₂ : ↥(alternatingGroup (Fin 6)) := ⟨a6g₂P, a6P_mem.2.2.2.2⟩

theorem a6P_relations : a6s₁P * a6s₁P = 1 ∧ a6s₂P * a6s₂P = 1 ∧ a6s₃P * a6s₃P = 1 ∧
    a6s₁P ≠ 1 ∧ a6s₂P ≠ 1 ∧ a6s₃P ≠ 1 ∧ a6s₁P * a6s₂P = a6s₂P * a6s₁P ∧
    a6s₁P * a6s₃P = a6s₃P * a6s₁P ∧ a6s₂P * a6s₃P ≠ a6s₃P * a6s₂P ∧
    a6s₁P * a6g₁P = a6g₁P * (a6s₁P * a6s₂P) ∧ a6s₂P * a6g₁P = a6g₁P * a6s₁P ∧
    a6s₁P * a6g₂P = a6g₂P * a6s₃P ∧ a6s₃P * a6g₂P = a6g₂P * (a6s₁P * a6s₃P) ∧
    a6g₁P ^ 3 = 1 ∧ a6g₁P ≠ 1 ∧ a6g₂P ^ 3 = 1 ∧ a6g₂P ≠ 1 := by
  simp only [a6s₁P, a6s₂P, a6s₃P, a6g₁P, a6g₂P]
  decide +kernel

theorem a6_relations : a6s₁ * a6s₁ = 1 ∧ a6s₂ * a6s₂ = 1 ∧ a6s₃ * a6s₃ = 1 ∧
    a6s₁ ≠ 1 ∧ a6s₂ ≠ 1 ∧ a6s₃ ≠ 1 ∧ a6s₁ * a6s₂ = a6s₂ * a6s₁ ∧
    a6s₁ * a6s₃ = a6s₃ * a6s₁ ∧ a6s₂ * a6s₃ ≠ a6s₃ * a6s₂ ∧
    a6s₁ * a6g₁ = a6g₁ * (a6s₁ * a6s₂) ∧ a6s₂ * a6g₁ = a6g₁ * a6s₁ ∧
    a6s₁ * a6g₂ = a6g₂ * a6s₃ ∧ a6s₃ * a6g₂ = a6g₂ * (a6s₁ * a6s₃) ∧
    a6g₁ ^ 3 = 1 ∧ a6g₁ ≠ 1 ∧ a6g₂ ^ 3 = 1 ∧ a6g₂ ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    a6P_relations
  refine ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, fun h => h4 (congrArg Subtype.val h),
    fun h => h5 (congrArg Subtype.val h), fun h => h6 (congrArg Subtype.val h), Subtype.ext h7,
    Subtype.ext h8, fun h => h9 (congrArg Subtype.val h), Subtype.ext h10, Subtype.ext h11,
    Subtype.ext h12, Subtype.ext h13, Subtype.ext h14, fun h => h15 (congrArg Subtype.val h),
    Subtype.ext h16, fun h => h17 (congrArg Subtype.val h)⟩

end FFL

open FFL

theorem fixTripleA6_holds : FixTripleA6 := by
  intro K _ _ hK Γ₀ _ hhat hcen
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_two_of_card (n := 2) (by rw [hK]; norm_num)
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hhat
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    a6_relations
  set f : ↥Γ₀ →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Γ₀)) with hfdef
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥Γ₀))
  have hker : ∀ x, f x = 1 → x ∈ Subgroup.center ↥Γ₀ := by
    intro x hx
    have h0 : (QuotientGroup.mk' (Subgroup.center ↥Γ₀) x) = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).1 h0
  have hZexp : ∀ x ∈ Subgroup.center ↥Γ₀, x ^ 3 = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥Γ₀)) (x := ⟨x, hx⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hk : ∀ x, f x = 1 → (∀ y, x * y = y * x) ∧ x ^ 3 = 1 := fun x hx =>
    ⟨fun y => (Subgroup.mem_center_iff.1 (hker x hx) y).symm, hZexp x (hker x hx)⟩
  have hscal : ∀ x, f x = 1 → ∃ d : K, glMat x = d • 1 := fun x hx => hcen x (hker x hx)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (fun h => by
    rw [h, Subgroup.card_bot] at hZ3
    omega : Subgroup.center ↥Γ₀ ≠ ⊥)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hfz : f z = 1 := by
    rw [hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff z).2 hzZ]
    exact map_one e
  obtain ⟨t₁, ht₁, hft₁⟩ := exists_sq_lift hk hf h1
  obtain ⟨t₂, ht₂, hft₂⟩ := exists_sq_lift hk hf h2
  obtain ⟨t₃, ht₃, hft₃⟩ := exists_sq_lift hk hf h3
  obtain ⟨g₁, hg₁⟩ := hf a6g₁
  obtain ⟨g₂, hg₂⟩ := hf a6g₂
  have hc12 : t₁ * t₂ = t₂ * t₁ := comm_of_sq_eq_one hk ht₁ ht₂ (by rw [hft₁, hft₂, h7])
  have hc13 : t₁ * t₃ = t₃ * t₁ := comm_of_sq_eq_one hk ht₁ ht₃ (by rw [hft₁, hft₃, h8])
  have hsq_mul : ∀ {a b : ↥Γ₀}, a * a = 1 → b * b = 1 → a * b = b * a → a * b * (a * b) = 1 := by
    intro a b ha hb hab
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
  have hc1 : t₁ * g₁ = g₁ * (t₁ * t₂) := mul_eq_of_sq_eq_one hk ht₁ (hsq_mul ht₁ ht₂ hc12)
    (by rw [map_mul, hft₁, hft₂, hg₁, h10])
  have hc2 : t₂ * g₁ = g₁ * t₁ := mul_eq_of_sq_eq_one hk ht₂ ht₁ (by rw [hft₁, hft₂, hg₁, h11])
  have hc3 : t₁ * g₂ = g₂ * t₃ := mul_eq_of_sq_eq_one hk ht₁ ht₃ (by rw [hft₁, hft₃, hg₂, h12])
  have hc4 : t₃ * g₂ = g₂ * (t₁ * t₃) := mul_eq_of_sq_eq_one hk ht₃ (hsq_mul ht₁ ht₃ hc13)
    (by rw [map_mul, hft₁, hft₃, hg₂, h13])
  have hne : ∀ {t : ↥Γ₀} {σ : ↥(alternatingGroup (Fin 6))}, f t = σ → σ ≠ 1 → glMat t ≠ 1 := by
    intro t σ hft hσ h
    apply hσ
    rw [← hft, show t = 1 from glMat_injective h, map_one]
  have hM₁ := hne hft₁ h4
  have hM₂ := hne hft₂ h5
  have hM₃ := hne hft₃ h6
  have hfg₁ : f g₁ ≠ 1 := by rw [hg₁]; exact h15
  have hfg₂ : f g₂ ≠ 1 := by rw [hg₂]; exact h17
  have hfg₁3 : f g₁ ^ 3 = 1 := by rw [hg₁]; exact h14
  have hfg₂3 : f g₂ ^ 3 = 1 := by rw [hg₂]; exact h16
  have hfinal : ∀ s : ↥Γ₀, s * s = 1 → t₁ * s = s * t₁ → ∀ γ : ↥Γ₀, γ ^ 3 = 1 → γ ≠ 1 →
      (∀ v, glMat t₁ *ᵥ v = v → glMat s *ᵥ v = v → glMat γ *ᵥ v = v) →
      ∃ T₀ : Subgroup ↥Γ₀, IsPGroup 2 ↥T₀ ∧ ∃ γ : ↥Γ₀, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
        FFL.FixesFixed (FFModel.nat Γ₀) T₀ γ := by
    intro s hs hts γ hγ3 hγ1 hγ
    refine ⟨Subgroup.closure {t₁, s}, isPGroup_closure_pair ht₁ hs hts, γ, hγ3, hγ1, ?_⟩
    intro (m : Multiplicative (Fin 3 → K)) _ hm
    have hfix : ∀ τ ∈ Subgroup.closure {t₁, s},
        glMat τ *ᵥ Multiplicative.toAdd m = Multiplicative.toAdd m := by
      intro τ hτ
      have h : natAct Γ₀ τ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin 3 → K))) := hm τ hτ
      rw [Subgroup.mem_bot] at h
      exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp h)
    have hγm := hγ (Multiplicative.toAdd m)
      (hfix _ (Subgroup.subset_closure (Set.mem_insert _ _)))
      (hfix _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    show natAct Γ₀ γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin 3 → K)))
    rw [Subgroup.mem_bot]
    exact mul_inv_eq_one.mpr (congrArg Multiplicative.ofAdd hγm)
  rcases fixSub3_dichotomy hM₁ hM₂ with hF | hF
  ·
    obtain ⟨γ, hγ3, hγ1, hγ⟩ := exists_gamma_of_line hK' f hscal hfz hz1' (hZexp z hzZ) hfg₁
      hfg₁3 hF fun v hv₁ hv₂ => ⟨by
        rw [← glMat_mulVec_mul, hc1, glMat_mulVec_mul, glMat_mulVec_mul, hv₂, hv₁], by
        rw [← glMat_mulVec_mul, hc2, glMat_mulVec_mul, hv₁]⟩
    exact hfinal t₂ ht₂ hc12 γ hγ3 hγ1 hγ
  · rcases fixSub3_dichotomy hM₁ hM₃ with hF' | hF'
    ·
      obtain ⟨γ, hγ3, hγ1, hγ⟩ := exists_gamma_of_line hK' f hscal hfz hz1' (hZexp z hzZ)
        hfg₂ hfg₂3 hF' fun v hv₁ hv₃ => ⟨by
          rw [← glMat_mulVec_mul, hc3, glMat_mulVec_mul, hv₃], by
          rw [← glMat_mulVec_mul, hc4, glMat_mulVec_mul, glMat_mulVec_mul, hv₃, hv₁]⟩
      exact hfinal t₃ ht₃ hc13 γ hγ3 hγ1 hγ
    ·
      exfalso
      have hsame : ∀ v, glMat t₂ *ᵥ v = v ↔ glMat t₃ *ᵥ v = v := by
        intro v
        rw [← mem_fixSub3, ← mem_fixSub3, ← hF, ← hF']
      have hcomm := comm_of_fix_eq (congrArg glMat ht₂) (congrArg glMat ht₃) hsame
      apply h9
      have h23 : t₂ * t₃ = t₃ * t₂ := glMat_injective (by rw [glMat_mul, glMat_mul]; exact hcomm)
      rw [← hft₂, ← hft₃, ← map_mul, ← map_mul, h23]

end CFSG.Quasithin.EmptyFaithfulMultiple
