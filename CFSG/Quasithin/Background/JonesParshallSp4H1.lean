module

public import CFSG.Quasithin.Background.JonesParshallSp4Cocycle
public import CFSG.Quasithin.Background.JonesParshallOrthogonal

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit

variable {F : Type} [Field F]

@[expose] def lMat (t : F) : SL2 F := ⟨!![1, 0; t, 1], by simp [det_fin_two]⟩

theorem lMat_coe (t : F) : ((lMat t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl

variable [Fintype F] [CharP F 2]

omit [CharP F 2] in
theorem exists_ne_zero_one {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ, hF]
      calc ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
        _ < 2 ^ a := by
          calc 2 = 2 ^ 1 := by norm_num
            _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem hom_SL2_eq_zero {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) {φ : SL2 F → F}
    (hφ : ∀ M N, φ (M * N) = φ M + φ N) (M : SL2 F) : φ M = 0 := by
  classical
  have h1 : φ 1 = 0 := by
    have := hφ 1 1
    rw [one_mul] at this
    linear_combination -this
  have hinv : ∀ g, φ g⁻¹ = -φ g := fun g => by
    have := hφ g g⁻¹
    rw [mul_inv_cancel, h1] at this
    linear_combination -this
  have hconj : ∀ g h, φ (g * h * g⁻¹) = φ h := fun g h => by
    rw [hφ, hφ, hinv]
    ring
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hF ha
  have hc2 : c ^ 2 + 1 ≠ 0 := by
    intro h
    apply hc1
    have : (c + 1) ^ 2 = 0 := by rw [add_sq_F, one_pow]; exact h
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    exact (CharTwo.add_eq_zero.mp this)
  have hu : ∀ y, φ (uMat y) = 0 := fun y => by
    set x := y / (c ^ 2 + 1)
    have hx : y = c ^ 2 * x + x := by
      rw [← add_one_mul, mul_comm]
      exact (div_mul_cancel₀ y hc2).symm
    have e := hconj (tMat c hc0) (uMat x)
    rw [tMat_conj] at e
    rw [hx, ← uMat_mul, hφ, e]
    exact CharTwo.add_self_eq_zero _
  have hZ : φ ∈ Z1A (1 : SL2 F →* AddMonoid.End F) := fun g h => by
    rw [hφ]
    rfl
  have hB := mem_B1A_of_vanish (fun m : F => CharTwo.add_self_eq_zero m)
    (odd_index_stab_e1 hF (by omega)) hZ fun g hg => by
      rw [eq_uMat_of_mem_stab hg]
      exact hu _
  obtain ⟨m, hm⟩ := hB
  rw [← hm, coboundaryA_apply]
  exact sub_self m

omit [Fintype F] in
theorem radical_eq {c₀ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1) {G : F → F → F → (Ix → F)}
    (hG : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' → c = γ + γ' + α * β' + β * α' →
      G a b c = G α β γ + (qElt α β γ : GL Ix F) • G α' β' γ')
    (hL : ∀ (M : SL2 F) α β γ a b, a = (M : Matrix (Fin 2) (Fin 2) F) 1 0 * β +
        (M : Matrix (Fin 2) (Fin 2) F) 1 1 * α →
      b = (M : Matrix (Fin 2) (Fin 2) F) 0 0 * β + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * α →
      G a b γ = (iotaHom M : GL Ix F) • G α β γ) :
    ∃ k : F, ∀ α β γ, G α β γ = vec4 (γ * k) (β * k) 0 (α * k) := by
  have h2 : ∀ x : F, x + x = 0 := CharTwo.add_self_eq_zero
  set A₁ : F → F → F → F := fun α β γ => G α β γ (.inl 0) with hA₁
  set A₂ : F → F → F → F := fun α β γ => G α β γ (.inl 1) with hA₂
  set A₃ : F → F → F → F := fun α β γ => G α β γ (.inr 0) with hA₃
  set A₄ : F → F → F → F := fun α β γ => G α β γ (.inr 1) with hA₄
  have c1 : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' →
      c = γ + γ' + α * β' + β * α' → A₁ a b c = A₁ α β γ + (A₁ α' β' γ' + α * A₂ α' β' γ' +
        γ * A₃ α' β' γ' + β * A₄ α' β' γ') := fun α β γ α' β' γ' a b c ha hb hc => by
    have h := congrFun (hG α β γ α' β' γ' a b c ha hb hc) (.inl 0)
    rw [qElt_smul_apply] at h
    exact h
  have c2 : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' →
      c = γ + γ' + α * β' + β * α' → A₂ a b c = A₂ α β γ + (A₂ α' β' γ' + β * A₃ α' β' γ') :=
    fun α β γ α' β' γ' a b c ha hb hc => by
      have h := congrFun (hG α β γ α' β' γ' a b c ha hb hc) (.inl 1)
      rw [qElt_smul_apply] at h
      exact h
  have c3 : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' →
      c = γ + γ' + α * β' + β * α' → A₃ a b c = A₃ α β γ + A₃ α' β' γ' :=
    fun α β γ α' β' γ' a b c ha hb hc => by
      have h := congrFun (hG α β γ α' β' γ' a b c ha hb hc) (.inr 0)
      rw [qElt_smul_apply] at h
      exact h
  have c4 : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' →
      c = γ + γ' + α * β' + β * α' → A₄ a b c = A₄ α β γ + (A₄ α' β' γ' + α * A₃ α' β' γ') :=
    fun α β γ α' β' γ' a b c ha hb hc => by
      have h := congrFun (hG α β γ α' β' γ' a b c ha hb hc) (.inr 1)
      rw [qElt_smul_apply] at h
      exact h
  have hLc : ∀ (M : SL2 F) α β γ a b, a = (M : Matrix (Fin 2) (Fin 2) F) 1 0 * β +
        (M : Matrix (Fin 2) (Fin 2) F) 1 1 * α →
      b = (M : Matrix (Fin 2) (Fin 2) F) 0 0 * β + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * α →
      A₁ a b γ = A₁ α β γ ∧
      A₂ a b γ = (M : Matrix (Fin 2) (Fin 2) F) 0 0 * A₂ α β γ +
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 * A₄ α β γ ∧
      A₃ a b γ = A₃ α β γ ∧
      A₄ a b γ = (M : Matrix (Fin 2) (Fin 2) F) 1 0 * A₂ α β γ +
        (M : Matrix (Fin 2) (Fin 2) F) 1 1 * A₄ α β γ := fun M α β γ a b ha hb => by
    have h := hL M α β γ a b ha hb
    rw [iotaHom_smul_apply] at h
    exact ⟨congrFun h (.inl 0), congrFun h (.inl 1), congrFun h (.inr 0), congrFun h (.inr 1)⟩
  have s2 : ∀ α β γ α' β' γ', β * A₃ α' β' γ' = β' * A₃ α β γ := fun α β γ α' β' γ' => by
    have e1 := c2 α β γ α' β' γ' _ _ _ rfl rfl rfl
    have e2 := c2 α' β' γ' α β γ (α + α') (β + β') (γ + γ' + α * β' + β * α') (by ring)
      (by ring) (by ring)
    linear_combination e2 - e1
  have s4 : ∀ α β γ α' β' γ', α * A₃ α' β' γ' = α' * A₃ α β γ := fun α β γ α' β' γ' => by
    have e1 := c4 α β γ α' β' γ' _ _ _ rfl rfl rfl
    have e2 := c4 α' β' γ' α β γ (α + α') (β + β') (γ + γ' + α * β' + β * α') (by ring)
      (by ring) (by ring)
    linear_combination e2 - e1
  have hA₃ : ∀ α β γ, A₃ α β γ = 0 := fun α β γ => by
    have k0 : A₃ 1 0 0 = 0 := by
      have := s2 1 0 0 0 1 0
      rw [zero_mul, one_mul] at this
      exact this.symm
    have := s4 α β γ 1 0 0
    rw [k0, mul_zero, one_mul] at this
    exact this.symm
  have hT : ∀ (d : F) (hd : d ≠ 0) α β γ, A₁ (d⁻¹ * α) (d * β) γ = A₁ α β γ ∧
      A₂ (d⁻¹ * α) (d * β) γ = d * A₂ α β γ ∧ A₄ (d⁻¹ * α) (d * β) γ = d⁻¹ * A₄ α β γ :=
    fun d hd α β γ => by
      obtain ⟨e1, e2, -, e4⟩ := hLc (tMat d hd) α β γ (d⁻¹ * α) (d * β)
        (by simp [tMat_coe]) (by simp [tMat_coe])
      simp only [tMat_coe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, zero_mul, add_zero, zero_add] at e2 e4
      exact ⟨e1, e2, e4⟩
  have hU : ∀ t α β γ, A₁ α (β + t * α) γ = A₁ α β γ ∧
      A₂ α (β + t * α) γ = A₂ α β γ + t * A₄ α β γ ∧ A₄ α (β + t * α) γ = A₄ α β γ :=
    fun t α β γ => by
      obtain ⟨e1, e2, -, e4⟩ := hLc (uMat t) α β γ α (β + t * α)
        (by simp [uMat_coe]) (by simp [uMat_coe])
      simp only [uMat_coe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, zero_mul, one_mul, zero_add] at e2 e4
      exact ⟨e1, e2, e4⟩
  have hLo : ∀ t α β γ, A₁ (α + t * β) β γ = A₁ α β γ ∧ A₂ (α + t * β) β γ = A₂ α β γ :=
    fun t α β γ => by
      obtain ⟨e1, e2, -, -⟩ := hLc (lMat t) α β γ (α + t * β) β
        (by simp [lMat_coe]; ring) (by simp [lMat_coe])
      simp only [lMat_coe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, zero_mul, one_mul, add_zero] at e2
      exact ⟨e1, e2⟩
  have hd₀ : c₀⁻¹ ≠ 1 := fun h => hc₁ (inv_eq_one.mp h)
  have hA₂c : ∀ γ, A₂ 0 0 γ = 0 := fun γ => by
    have e := (hT c₀ hc₀ 0 0 γ).2.1
    rw [mul_zero, mul_zero] at e
    have : (c₀ - 1) * A₂ 0 0 γ = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc₁)
  have hA₄c : ∀ γ, A₄ 0 0 γ = 0 := fun γ => by
    have e := (hT c₀ hc₀ 0 0 γ).2.2
    rw [mul_zero, mul_zero] at e
    have : (c₀⁻¹ - 1) * A₄ 0 0 γ = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hd₀)
  have hA₂γ : ∀ α β γ, A₂ α β γ = A₂ α β 0 := fun α β γ => by
    have e := c2 α β 0 0 0 γ α β γ (by ring) (by ring) (by ring)
    rw [hA₂c, hA₃, mul_zero, add_zero, add_zero] at e
    exact e
  have hA₄γ : ∀ α β γ, A₄ α β γ = A₄ α β 0 := fun α β γ => by
    have e := c4 α β 0 0 0 γ α β γ (by ring) (by ring) (by ring)
    rw [hA₄c, hA₃, mul_zero, add_zero, add_zero] at e
    exact e
  have hA₂split : ∀ α β, A₂ α β 0 = A₂ α 0 0 + A₂ 0 β 0 := fun α β => by
    have e := c2 α 0 0 0 β 0 α β (α * β) (by ring) (by ring) (by ring)
    rw [hA₃, mul_zero, add_zero, hA₂γ] at e
    exact e
  have hA₄split : ∀ α β, A₄ α β 0 = A₄ α 0 0 + A₄ 0 β 0 := fun α β => by
    have e := c4 α 0 0 0 β 0 α β (α * β) (by ring) (by ring) (by ring)
    rw [hA₃, mul_zero, add_zero, hA₄γ] at e
    exact e
  have hA₂α : ∀ t, A₂ t 0 0 = 0 := fun t => by
    have e := (hLo t 0 1 0).2
    rw [mul_one, zero_add, hA₂γ, hA₂split, hA₂split 0 1] at e
    have h00 : A₂ 0 0 0 = 0 := hA₂c 0
    rw [h00, zero_add] at e
    linear_combination e
  have hA₄β : ∀ t, A₄ 0 t 0 = 0 := fun t => by
    have e := (hU t 1 0 0).2.2
    rw [mul_one, zero_add, hA₄γ, hA₄split, hA₄split 1 0] at e
    have h00 : A₄ 0 0 0 = 0 := hA₄c 0
    rw [h00, add_zero] at e
    linear_combination e
  have hA₂eq : ∀ α β γ, A₂ α β γ = β * A₂ 0 1 0 := fun α β γ => by
    rw [hA₂γ, hA₂split, hA₂α, zero_add]
    by_cases hβ : β = 0
    · rw [hβ, zero_mul]
      exact hA₂c 0
    · have e := (hT β hβ 0 1 0).2.1
      rw [mul_zero, mul_one] at e
      exact e
  have hA₄eq : ∀ α β γ, A₄ α β γ = α * A₄ 1 0 0 := fun α β γ => by
    rw [hA₄γ, hA₄split, hA₄β, add_zero]
    by_cases hα : α = 0
    · rw [hα, zero_mul]
      exact hA₄c 0
    · have e := (hT α⁻¹ (inv_ne_zero hα) 1 0 0).2.2
      rw [inv_inv, mul_one, mul_zero] at e
      exact e
  set k := A₂ 0 1 0
  have hk : A₄ 1 0 0 = k := by
    have e := (hU 1 1 0 0).2.1
    rw [hA₂eq, hA₂eq, hA₄eq] at e
    linear_combination -e
  rw [hk] at hA₄eq
  set D : F → F → F → F := fun α β γ => A₁ α β γ - γ * k with hD
  have hDadd : ∀ α β γ α' β' γ' a b c, a = α + α' → b = β + β' →
      c = γ + γ' + α * β' + β * α' → D a b c = D α β γ + D α' β' γ' :=
    fun α β γ α' β' γ' a b c ha hb hc => by
      simp only [hD]
      rw [c1 α β γ α' β' γ' a b c ha hb hc, hA₂eq, hA₃, hA₄eq, hc]
      ring
  have hDU : ∀ t α β γ, D α (β + t * α) γ = D α β γ := fun t α β γ => by
    simp only [hD]
    rw [(hU t α β γ).1]
  have hDL : ∀ t α β γ, D (α + t * β) β γ = D α β γ := fun t α β γ => by
    simp only [hD]
    rw [(hLo t α β γ).1]
  have hDsplit : ∀ α β γ, D α β γ = D α 0 0 + D 0 β 0 - D 0 0 (α * β) + D 0 0 γ :=
    fun α β γ => by
      have e1 := hDadd α β 0 0 0 γ α β γ (by ring) (by ring) (by ring)
      have e2 := hDadd α β 0 0 0 (α * β) α β (α * β) (by ring) (by ring) (by ring)
      have e3 := hDadd α 0 0 0 β 0 α β (α * β) (by ring) (by ring) (by ring)
      linear_combination e1 - e2 + e3
  have hD0 : D 0 0 0 = 0 := by
    have e := hDadd 0 0 0 0 0 0 0 0 0 (by ring) (by ring) (by ring)
    linear_combination -e
  have hβγ : ∀ t a, D 0 (t * a) 0 = D 0 0 (t * a ^ 2) := fun t a => by
    have e := hDU t a 0 0
    rw [zero_add, hDsplit, hDsplit a 0 0, hD0] at e
    have hz : D 0 0 0 = 0 := hD0
    rw [show a * (t * a) = t * a ^ 2 by ring, mul_zero] at e
    linear_combination e
  have hαγ : ∀ t b, D (t * b) 0 0 = D 0 0 (t * b ^ 2) := fun t b => by
    have e := hDL t 0 b 0
    rw [zero_add, hDsplit, hDsplit 0 b 0, hD0] at e
    rw [show t * b * b = t * b ^ 2 by ring, zero_mul] at e
    linear_combination e
  have hγconst : ∀ a : F, a ≠ 0 → D 0 0 a = D 0 0 1 := fun a ha => by
    have e1 := hβγ 1 1
    have e2 := hβγ (a⁻¹) a
    rw [one_mul, one_pow, one_mul] at e1
    rw [inv_mul_cancel₀ ha, show a⁻¹ * a ^ 2 = a by field_simp] at e2
    rw [← e2, e1]
  have hγadd : ∀ x y, D 0 0 (x + y) = D 0 0 x + D 0 0 y := fun x y =>
    hDadd 0 0 x 0 0 y 0 0 (x + y) (by ring) (by ring) (by ring)
  have hγ1 : D 0 0 1 = 0 := by
    have h1c : 1 + c₀ ≠ 0 := fun h => hc₁ (by
      have : c₀ = -1 := eq_neg_of_add_eq_zero_right h
      rw [this, CharTwo.neg_eq])
    have e := hγadd 1 c₀
    rw [hγconst _ h1c, hγconst _ hc₀] at e
    linear_combination -e
  have hγ0 : ∀ x, D 0 0 x = 0 := fun x => by
    by_cases hx : x = 0
    · rw [hx]
      exact hD0
    · rw [hγconst x hx, hγ1]
  have hβ0 : ∀ x, D 0 x 0 = 0 := fun x => by
    have e := hβγ x 1
    rw [mul_one, one_pow, mul_one, hγ0] at e
    exact e
  have hα0 : ∀ x, D x 0 0 = 0 := fun x => by
    have e := hαγ x 1
    rw [mul_one, one_pow, mul_one, hγ0] at e
    exact e
  refine ⟨k, fun α β γ => ?_⟩
  have hA₁eq : A₁ α β γ = γ * k := by
    have e : D α β γ = 0 := by rw [hDsplit, hα0, hβ0, hγ0, hγ0]; ring
    simp only [hD] at e
    exact sub_eq_zero.mp e
  rw [vec4_eta (G α β γ)]
  change vec4 (A₁ α β γ) (A₂ α β γ) (A₃ α β γ) (A₄ α β γ) = _
  rw [hA₁eq, hA₂eq, hA₃, hA₄eq]

theorem exists_sub_spF0_mem_B1A {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {f : ↥(sp4 F) → (Ix → F)} (hf : f ∈ Z1A (muSp (F := F))) :
    ∃ B : F, f - B • spF0 ∈ B1A (muSp (F := F)) := by
  classical
  have h2 : ∀ m : Ix → F, m + m = 0 := fun m => funext fun i => CharTwo.add_self_eq_zero (m i)
  have hι : ∀ M N : SL2 F, f (iotaHom (M * N)) =
      f (iotaHom M) + (iotaHom M : GL Ix F) • f (iotaHom N) := fun M N => by
    rw [map_mul]
    exact hf _ _
  have hφ1 : ∀ M, f (iotaHom M) (.inl 0) = 0 := hom_SL2_eq_zero hF ha fun M N => by
    have h := congrFun (hι M N) (.inl 0)
    rw [Pi.add_apply, iotaHom_smul_apply] at h
    exact h
  have hφ3 : ∀ M, f (iotaHom M) (.inr 0) = 0 := hom_SL2_eq_zero hF ha fun M N => by
    have h := congrFun (hι M N) (.inr 0)
    rw [Pi.add_apply, iotaHom_smul_apply] at h
    exact h
  set φN : SL2 F → (Fin 2 → F) := fun M => ![f (iotaHom M) (.inl 1), f (iotaHom M) (.inr 1)]
    with hφN
  have hφNZ : φN ∈ Z1A (mu2 (F := F)) := fun M N => by
    have h1 := congrFun (hι M N) (.inl 1)
    have h4 := congrFun (hι M N) (.inr 1)
    rw [Pi.add_apply, iotaHom_smul_apply] at h1 h4
    funext i
    rw [Pi.add_apply, mu2_apply]
    fin_cases i
    · change f (iotaHom (M * N)) (.inl 1) = f (iotaHom M) (.inl 1) +
        ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ φN N) 0
      rw [mulVec_two_zero]
      exact h1
    · change f (iotaHom (M * N)) (.inr 1) = f (iotaHom M) (.inr 1) +
        ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ φN N) 1
      rw [mulVec_two_one]
      exact h4
  obtain ⟨B, n, hn⟩ := exists_sub_mem_B1A hF ha hφNZ
  refine ⟨B, ?_⟩
  set m₀ : Ix → F := vec4 0 (n 0) 0 (n 1)
  set f' := f - B • spF0 - coboundaryA muSp m₀ with hf'
  have hf'Z : f' ∈ Z1A (muSp (F := F)) :=
    sub_mem (sub_mem hf (smul_spF0_mem B)) (B1A_le_Z1A _ ⟨_, rfl⟩)
  have hf'ι : ∀ M, f' (iotaHom M) = 0 := fun M => by
    have hn' : ∀ i, ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ n) i - n i = φN M i - B * f0 M i :=
      fun i => congrFun (congrFun hn M) i
    have hn0 := hn' 0
    have hn1 := hn' 1
    rw [mulVec_two_zero] at hn0
    rw [mulVec_two_one] at hn1
    have e0 : φN M 0 = f (iotaHom M) (.inl 1) := rfl
    have e1 : φN M 1 = f (iotaHom M) (.inr 1) := rfl
    rw [e0] at hn0
    rw [e1] at hn1
    have hs := spF0_iotaHom M
    have hm := iotaHom_smul M 0 (n 0) 0 (n 1)
    funext i
    rw [hf', Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, coboundaryA_apply, muSp_apply,
      Pi.smul_apply, hs, hm]
    rcases i with i | i <;> fin_cases i
    · change f (iotaHom M) (.inl 0) - B * 0 - (0 - 0) = 0
      rw [hφ1]
      ring
    · change f (iotaHom M) (.inl 1) - B * f0 M 0 -
        (((M : Matrix (Fin 2) (Fin 2) F) 0 0 * n 0 + (M : Matrix (Fin 2) (Fin 2) F) 0 1 * n 1) -
          n 0) = 0
      linear_combination -hn0
    · change f (iotaHom M) (.inr 0) - B * 0 - (0 - 0) = 0
      rw [hφ3]
      ring
    · change f (iotaHom M) (.inr 1) - B * f0 M 1 -
        (((M : Matrix (Fin 2) (Fin 2) F) 1 0 * n 0 + (M : Matrix (Fin 2) (Fin 2) F) 1 1 * n 1) -
          n 1) = 0
      linear_combination -hn1
  obtain ⟨c₀, hc₀, hc₁⟩ := exists_ne_zero_one hF ha
  obtain ⟨k, hk⟩ := radical_eq hc₀ hc₁ (G := fun α β γ => f' (qElt α β γ))
    (fun α β γ α' β' γ' a b c ha hb hc => by
      subst ha hb hc
      rw [← qElt_mul]
      exact hf'Z _ _)
    (fun M α β γ a b ha hb => by
      subst ha hb
      have e1 := hf'Z (iotaHom M) (qElt α β γ)
      rw [hf'ι, zero_add, iota_mul_qElt, hf'Z, hf'ι, map_zero, add_zero] at e1
      exact e1)
  set f'' := f' - coboundaryA muSp (vec4 0 0 k 0) with hf''
  have hf''Z : f'' ∈ Z1A (muSp (F := F)) := sub_mem hf'Z (B1A_le_Z1A _ ⟨_, rfl⟩)
  have hf''q : ∀ α β γ, f'' (qElt α β γ) = 0 := fun α β γ => by
    have hq := qElt_smul α β γ 0 0 k 0
    have hkq := hk α β γ
    rw [hf'', Pi.sub_apply, hkq, coboundaryA_apply, muSp_apply, hq, vec4_sub, vec4_sub,
      ← vec4_zero]
    congr 1 <;> ring
  have hf''ι : ∀ M, f'' (iotaHom M) = 0 := fun M => by
    have hm := iotaHom_smul M 0 0 k 0
    rw [hf'', Pi.sub_apply, hf'ι, coboundaryA_apply, muSp_apply, hm, vec4_sub, ← vec4_zero,
      vec4_sub]
    congr 1 <;> ring
  have hB'' : f'' ∈ B1A (muSp (F := F)) := by
    refine mem_B1A_of_vanish h2 (odd_index_stab_vec hF (by omega)) hf''Z fun g hg => ?_
    obtain ⟨α, β, γ, M, hgM⟩ := eq_qElt_mul_iota g.2 hg
    rw [show g = qElt α β γ * iotaHom M from Subtype.ext hgM, hf''Z, hf''q, hf''ι, map_zero,
      add_zero]
  have e : f - B • spF0 = f'' + coboundaryA muSp (vec4 0 0 k 0) + coboundaryA muSp m₀ := by
    rw [hf'', hf']
    abel
  rw [e]
  exact add_mem (add_mem hB'' ⟨_, rfl⟩) ⟨_, rfl⟩

theorem eq_zero_of_smul_spF0_mem_B1A (hcard : 2 < Fintype.card F) {B : F}
    (h : B • spF0 ∈ B1A (muSp (F := F))) : B = 0 := by
  obtain ⟨m, hm⟩ := h
  refine eq_zero_of_smul_f0_mem_B1A hcard ⟨![m (.inl 1), m (.inr 1)], funext fun M => ?_⟩
  have hM := congrFun hm (iotaHom M)
  rw [coboundaryA_apply, muSp_apply, iotaHom_smul_apply, Pi.smul_apply, spF0_iotaHom,
    vec4_smul] at hM
  funext i
  rw [coboundaryA_apply, mu2_apply, Pi.sub_apply, Pi.smul_apply]
  fin_cases i
  · have e := congrFun hM (.inl 1)
    rw [Pi.sub_apply] at e
    change ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ ![m (.inl 1), m (.inr 1)]) 0 - m (.inl 1) =
      B • f0 M 0
    rw [mulVec_two_zero]
    simpa [vec4] using e
  · have e := congrFun hM (.inr 1)
    rw [Pi.sub_apply] at e
    change ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ ![m (.inl 1), m (.inr 1)]) 1 - m (.inr 1) =
      B • f0 M 1
    rw [mulVec_two_one]
    simpa [vec4] using e

theorem card_Z1A_muSp {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) :
    Nat.card (Z1A (muSp (F := F))) = Fintype.card F * Nat.card (B1A (muSp (F := F))) := by
  have hcard : 2 < Fintype.card F := by
    rw [hF]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha
  let Φ : F × B1A (muSp (F := F)) → Z1A (muSp (F := F)) := fun p =>
    ⟨p.1 • spF0 + (p.2 : ↥(sp4 F) → (Ix → F)), add_mem (smul_spF0_mem p.1) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨B, b⟩ ⟨B', b'⟩ h
      have h' : B • spF0 (F := F) + (b : ↥(sp4 F) → (Ix → F)) = B' • spF0 (F := F) + b' := by
        simpa [Φ] using congrArg Subtype.val h
      have hBB : (B - B') • (spF0 : ↥(sp4 F) → (Ix → F)) ∈ B1A (muSp (F := F)) := by
        have : (B - B') • (spF0 : ↥(sp4 F) → (Ix → F)) = (b' : ↥(sp4 F) → (Ix → F)) - b := by
          calc (B - B') • (spF0 : ↥(sp4 F) → (Ix → F)) =
              (B • spF0 (F := F) + (b : ↥(sp4 F) → (Ix → F))) - (B' • spF0 (F := F) + b) := by
                rw [sub_smul]
                abel
            _ = (B' • spF0 (F := F) + b') - (B' • spF0 (F := F) + b) := by rw [h']
            _ = b' - b := by abel
        rw [this]
        exact sub_mem b'.2 b.2
      have hB : B = B' := sub_eq_zero.mp (eq_zero_of_smul_spF0_mem_B1A hcard hBB)
      subst hB
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      obtain ⟨B, hB⟩ := exists_sub_spF0_mem_B1A hF ha hf
      exact ⟨(B, ⟨_, hB⟩), Subtype.ext (by simp [Φ])⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_eq_fintype_card]

end CFSG.Quasithin.JonesParshall
