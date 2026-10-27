module

public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.EmptyFaithful.S151bW3Cnt
public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin

section Generic

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem fixV_zpowers_conj151b (g a : MulAut W) :
    fixV (Subgroup.zpowers (g * a * g⁻¹)) = (fixV (Subgroup.zpowers a)).map g.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj g a

theorem rkIdx_fixV_conj151b (g a : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (g * a * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers a)) := by
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers (g * a * g⁻¹)))
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  have h3 : rk (fixV (Subgroup.zpowers (g * a * g⁻¹))) = rk (fixV (Subgroup.zpowers a)) := by
    unfold rk
    rw [fixV_zpowers_conj151b]
    rw [Subgroup.card_map_of_injective g.injective]
  omega

theorem rkIdx_pos_of_ne_one151b (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} (ha : a ≠ 1) :
    0 < rkIdx (fixV (Subgroup.zpowers a)) := by
  by_contra h
  have h0 : rkIdx (fixV (Subgroup.zpowers a)) = 0 := by omega
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  rw [h0, add_zero] at h1
  have : fixV (Subgroup.zpowers a) = ⊤ :=
    eq_of_le_of_rk_le hW le_top (by rw [rk_top]; exact h1.ge)
  exact ha (eq_one_of_fixV_eq_top this)

end Generic

section GenericGroup

variable {Γ : Type*} [Group Γ]

theorem conj_mem_zpowers151b {a b f : Γ} (h : f * a * f⁻¹ ∈ Subgroup.zpowers b) :
    ∀ x ∈ Subgroup.zpowers a, f * x * f⁻¹ ∈ Subgroup.zpowers b := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ h k

end GenericGroup

section Dihedral

variable {p : ℕ}

theorem dih_gen151b (hp : p = 3 ∨ p = 5) :
    ∀ y : DihedralGroup p, ∃ k : ZMod p, y = DihedralGroup.r k ∨
      y = DihedralGroup.r k * DihedralGroup.sr 0 := by
  rcases hp with rfl | rfl <;> decide

theorem dih_cube151b (hp : p = 3 ∨ p = 5) :
    ∀ w : DihedralGroup p × DihedralGroup p, w ^ p = 1 →
      ∃ i j : ZMod p, w = (DihedralGroup.r i, DihedralGroup.r j) := by
  rcases hp with rfl | rfl <;> decide

theorem dih_cent151b (hp : p = 3 ∨ p = 5) :
    ∀ w : DihedralGroup p × DihedralGroup p,
      w * (DihedralGroup.r 1, 1) = (DihedralGroup.r 1, 1) * w →
      w * (1, DihedralGroup.r 1) = (1, DihedralGroup.r 1) * w →
        ∃ i j : ZMod p, w = (DihedralGroup.r i, DihedralGroup.r j) := by
  rcases hp with rfl | rfl <;> decide

theorem dih_center151b (hp : p = 3 ∨ p = 5) :
    ∀ w : DihedralGroup p × DihedralGroup p, (∀ v, w * v = v * w) → w = 1 := by
  rcases hp with rfl | rfl <;> decide

theorem dih_center_one151b (hp : p = 3 ∨ p = 5) :
    ∀ d : DihedralGroup p, (∀ d' : DihedralGroup p, d * d' = d' * d) → d = 1 := by
  rcases hp with rfl | rfl <;> decide

theorem dih_rot_gen151b (hp : p = 3 ∨ p = 5) :
    ∀ i : ZMod p, i ≠ 0 → ∃ n : Fin p, (DihedralGroup.r i : DihedralGroup p) ^ (n : ℕ) =
      DihedralGroup.r 1 := by
  rcases hp with rfl | rfl <;> decide

theorem dih_invol151b (hp : p = 3 ∨ p = 5) :
    ∀ w : DihedralGroup p × DihedralGroup p, w * w = 1 →
      w * (DihedralGroup.r 1, 1) * w⁻¹ = (DihedralGroup.r 1, 1)⁻¹ →
      w * (1, DihedralGroup.r 1) * w⁻¹ = (1, DihedralGroup.r 1) →
        ∃ k : ZMod p, w = (DihedralGroup.sr k, 1) := by
  rcases hp with rfl | rfl <;> decide

end Dihedral

structure SixData151b (W : Type*) [CommGroup W] (p : ℕ) where
  A₁ : Subgroup (MulAut W)
  A₂ : Subgroup (MulAut W)
  e₁ : A₁ ≃* DihedralGroup p
  e₂ : A₂ ≃* DihedralGroup p
  comm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a
  inf : A₁ ⊓ A₂ = ⊥
  winf : commSub (⊤ : Subgroup W) A₁ ⊓ commSub (⊤ : Subgroup W) A₂ = ⊥
  wsup : commSub (⊤ : Subgroup W) A₁ ⊔ commSub (⊤ : Subgroup W) A₂ = ⊤
  τ : MulAut W
  τ₁₂ : ∀ a ∈ A₁, τ * a * τ⁻¹ ∈ A₂
  τ₂₁ : ∀ b ∈ A₂, τ * b * τ⁻¹ ∈ A₁

namespace SixData151b

variable {W : Type*} [CommGroup W] {p : ℕ} (S : SixData151b W p)

@[expose] def ι₁ : DihedralGroup p →* MulAut W := S.A₁.subtype.comp S.e₁.symm.toMonoidHom

@[expose] def ι₂ : DihedralGroup p →* MulAut W := S.A₂.subtype.comp S.e₂.symm.toMonoidHom

theorem ι₁_mem (x : DihedralGroup p) : S.ι₁ x ∈ S.A₁ := (S.e₁.symm x).2

theorem ι₂_mem (x : DihedralGroup p) : S.ι₂ x ∈ S.A₂ := (S.e₂.symm x).2

theorem exists_ι₁ {z : MulAut W} (hz : z ∈ S.A₁) : ∃ x, S.ι₁ x = z :=
  ⟨S.e₁ ⟨z, hz⟩, by simp [ι₁]⟩

theorem exists_ι₂ {z : MulAut W} (hz : z ∈ S.A₂) : ∃ x, S.ι₂ x = z :=
  ⟨S.e₂ ⟨z, hz⟩, by simp [ι₂]⟩

theorem ι₁_injective : Function.Injective S.ι₁ := fun _ _ h =>
  S.e₁.symm.injective (Subtype.ext h)

theorem ι₂_injective : Function.Injective S.ι₂ := fun _ _ h =>
  S.e₂.symm.injective (Subtype.ext h)

theorem commute_ι (x y : DihedralGroup p) : Commute (S.ι₁ x) (S.ι₂ y) :=
  S.comm _ (S.ι₁_mem x) _ (S.ι₂_mem y)

@[expose] def ι : DihedralGroup p × DihedralGroup p →* MulAut W :=
  S.ι₁.noncommCoprod S.ι₂ S.commute_ι

theorem ι_apply (w : DihedralGroup p × DihedralGroup p) : S.ι w = S.ι₁ w.1 * S.ι₂ w.2 := rfl

theorem ι_injective : Function.Injective S.ι := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, y⟩ h
  have h' : S.ι₁ x * S.ι₂ y = 1 := (ι_apply S (x, y)).symm.trans h
  have h1 : S.ι₁ x = (S.ι₂ y)⁻¹ := eq_inv_of_mul_eq_one_left h'
  have hmem : S.ι₁ x ∈ S.A₁ ⊓ S.A₂ :=
    ⟨S.ι₁_mem x, by rw [h1]; exact S.A₂.inv_mem (S.ι₂_mem y)⟩
  rw [S.inf, Subgroup.mem_bot] at hmem
  have hx : x = 1 := S.ι₁_injective (by rw [hmem, map_one])
  rw [hx, map_one, one_mul] at h'
  exact Prod.ext hx (S.ι₂_injective (h'.trans (map_one _).symm))

theorem ι_inl (x : DihedralGroup p) : S.ι (x, 1) = S.ι₁ x := by
  rw [ι_apply]; simp

theorem ι_inr (y : DihedralGroup p) : S.ι (1, y) = S.ι₂ y := by
  rw [ι_apply]; simp

theorem ι_mul_inl_inr (x y : DihedralGroup p) : S.ι (x, y) = S.ι (x, 1) * S.ι (1, y) := by
  rw [← map_mul]; simp

theorem ι_inl_mem (x : DihedralGroup p) : S.ι (x, 1) ∈ S.A₁ := by
  rw [ι_inl]; exact S.ι₁_mem x

theorem ι_inr_mem (y : DihedralGroup p) : S.ι (1, y) ∈ S.A₂ := by
  rw [ι_inr]; exact S.ι₂_mem y


@[expose] def a₁ : MulAut W := S.ι (DihedralGroup.r 1, 1)

@[expose] def a₂ : MulAut W := S.ι (1, DihedralGroup.r 1)

@[expose] def s₁ : MulAut W := S.ι (DihedralGroup.sr 0, 1)

@[expose] def s₂ : MulAut W := S.ι (1, DihedralGroup.sr 0)

theorem a₁_mem : S.a₁ ∈ S.A₁ := S.ι_inl_mem _

theorem s₁_mem : S.s₁ ∈ S.A₁ := S.ι_inl_mem _

theorem a₂_mem : S.a₂ ∈ S.A₂ := S.ι_inr_mem _

theorem s₂_mem : S.s₂ ∈ S.A₂ := S.ι_inr_mem _

theorem a₁_pow (hp : p = 3 ∨ p = 5) : S.a₁ ^ p = 1 := by
  have h : ((DihedralGroup.r 1, 1) : DihedralGroup p × DihedralGroup p) ^ p = 1 := by
    rcases hp with rfl | rfl <;> decide
  rw [a₁, ← map_pow, h, map_one]

theorem a₂_pow (hp : p = 3 ∨ p = 5) : S.a₂ ^ p = 1 := by
  have h : ((1, DihedralGroup.r 1) : DihedralGroup p × DihedralGroup p) ^ p = 1 := by
    rcases hp with rfl | rfl <;> decide
  rw [a₂, ← map_pow, h, map_one]

theorem s₁_sq (hp : p = 3 ∨ p = 5) : S.s₁ ^ 2 = 1 := by
  have h : ((DihedralGroup.sr 0, 1) : DihedralGroup p × DihedralGroup p) ^ 2 = 1 := by
    rcases hp with rfl | rfl <;> decide
  rw [s₁, ← map_pow, h, map_one]

theorem s₂_sq (hp : p = 3 ∨ p = 5) : S.s₂ ^ 2 = 1 := by
  have h : ((1, DihedralGroup.sr 0) : DihedralGroup p × DihedralGroup p) ^ 2 = 1 := by
    rcases hp with rfl | rfl <;> decide
  rw [s₂, ← map_pow, h, map_one]

theorem s₁_a₁ (hp : p = 3 ∨ p = 5) : S.s₁ * S.a₁ * S.s₁⁻¹ = S.a₁⁻¹ := by
  have h : ((DihedralGroup.sr 0, 1) : DihedralGroup p × DihedralGroup p) *
      (DihedralGroup.r 1, 1) * ((DihedralGroup.sr 0, 1))⁻¹ = ((DihedralGroup.r 1, 1))⁻¹ := by
    rcases hp with rfl | rfl <;> decide
  rw [s₁, a₁, ← map_inv, ← map_inv, ← map_mul, ← map_mul, h]

theorem s₂_a₂ (hp : p = 3 ∨ p = 5) : S.s₂ * S.a₂ * S.s₂⁻¹ = S.a₂⁻¹ := by
  have h : ((1, DihedralGroup.sr 0) : DihedralGroup p × DihedralGroup p) *
      (1, DihedralGroup.r 1) * ((1, DihedralGroup.sr 0))⁻¹ = ((1, DihedralGroup.r 1))⁻¹ := by
    rcases hp with rfl | rfl <;> decide
  rw [s₂, a₂, ← map_inv, ← map_inv, ← map_mul, ← map_mul, h]

theorem a₁_ne_one (hp : p = 3 ∨ p = 5) : S.a₁ ≠ 1 := fun h => by
  have h1 : ((DihedralGroup.r 1, 1) : DihedralGroup p × DihedralGroup p) = 1 :=
    S.ι_injective (h.trans (map_one S.ι).symm)
  have h2 : ¬ (((DihedralGroup.r 1, 1) : DihedralGroup p × DihedralGroup p) = 1) := by
    rcases hp with rfl | rfl <;> decide
  exact h2 h1

theorem a₂_ne_one (hp : p = 3 ∨ p = 5) : S.a₂ ≠ 1 := fun h => by
  have h1 : ((1, DihedralGroup.r 1) : DihedralGroup p × DihedralGroup p) = 1 :=
    S.ι_injective (h.trans (map_one S.ι).symm)
  have h2 : ¬ (((1, DihedralGroup.r 1) : DihedralGroup p × DihedralGroup p) = 1) := by
    rcases hp with rfl | rfl <;> decide
  exact h2 h1

theorem s₁_ne_one (hp : p = 3 ∨ p = 5) : S.s₁ ≠ 1 := fun h => by
  have h1 : ((DihedralGroup.sr 0, 1) : DihedralGroup p × DihedralGroup p) = 1 :=
    S.ι_injective (h.trans (map_one S.ι).symm)
  have h2 : ¬ (((DihedralGroup.sr 0, 1) : DihedralGroup p × DihedralGroup p) = 1) := by
    rcases hp with rfl | rfl <;> decide
  exact h2 h1

theorem s₂_ne_one (hp : p = 3 ∨ p = 5) : S.s₂ ≠ 1 := fun h => by
  have h1 : ((1, DihedralGroup.sr 0) : DihedralGroup p × DihedralGroup p) = 1 :=
    S.ι_injective (h.trans (map_one S.ι).symm)
  have h2 : ¬ (((1, DihedralGroup.sr 0) : DihedralGroup p × DihedralGroup p) = 1) := by
    rcases hp with rfl | rfl <;> decide
  exact h2 h1

theorem range_ι : S.ι.range = S.A₁ ⊔ S.A₂ := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [ι_apply]
    exact Subgroup.mul_mem_sup (S.ι₁_mem _) (S.ι₂_mem _)
  · refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨x, rfl⟩ := S.exists_ι₁ hz
      exact ⟨(x, 1), S.ι_inl x⟩
    · obtain ⟨y, rfl⟩ := S.exists_ι₂ hz
      exact ⟨(1, y), S.ι_inr y⟩


@[expose] def swap : SixData151b W p where
  A₁ := S.A₂
  A₂ := S.A₁
  e₁ := S.e₂
  e₂ := S.e₁
  comm := fun a ha b hb => (S.comm b hb a ha).symm
  inf := by rw [inf_comm]; exact S.inf
  winf := by rw [inf_comm]; exact S.winf
  wsup := by rw [sup_comm]; exact S.wsup
  τ := S.τ
  τ₁₂ := S.τ₂₁
  τ₂₁ := S.τ₁₂

theorem swap_ι₁ : S.swap.ι₁ = S.ι₂ := rfl

theorem swap_ι₂ : S.swap.ι₂ = S.ι₁ := rfl

theorem swap_a₁ : S.swap.a₁ = S.a₂ := by
  rw [a₁, ι_inl, swap_ι₁, a₂, ι_inr]

theorem swap_a₂ : S.swap.a₂ = S.a₁ := by
  rw [a₂, ι_inr, swap_ι₂, a₁, ι_inl]

theorem swap_s₁ : S.swap.s₁ = S.s₂ := by
  rw [s₁, ι_inl, swap_ι₁, s₂, ι_inr]

theorem swap_s₂ : S.swap.s₂ = S.s₁ := by
  rw [s₂, ι_inr, swap_ι₂, s₁, ι_inl]

abbrev W₁ : Subgroup W := commSub (⊤ : Subgroup W) S.A₁

abbrev W₂ : Subgroup W := commSub (⊤ : Subgroup W) S.A₂

theorem swap_W₁ : S.swap.W₁ = S.W₂ := rfl

theorem swap_W₂ : S.swap.W₂ = S.W₁ := rfl

theorem ι₁_r (hp : p = 3 ∨ p = 5) (k : ZMod p) : S.ι₁ (DihedralGroup.r k) = S.a₁ ^ k.val := by
  have : NeZero p := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  rw [a₁, ← map_pow, ← ι_inl]
  congr 1
  refine Prod.ext ?_ (by simp)
  simp

section FiniteW

variable [Finite W]

omit [Finite W] in
theorem card_W₁_mul_card_W₂ (hcard : Nat.card W = 256) :
    Nat.card S.W₁ * Nat.card S.W₂ = 256 := by
  have h := card_sup_mul_card_inf S.W₁ S.W₂
  rw [S.wsup, S.winf, Subgroup.card_top, Subgroup.card_bot, mul_one, hcard] at h
  exact h.symm

theorem card_W₁_eq_card_W₂ : Nat.card S.W₁ = Nat.card S.W₂ := by
  have h12 : ∀ w ∈ S.W₁, S.τ w ∈ S.W₂ := commSub_top_map151b S.τ₁₂
  have h21 : ∀ w ∈ S.W₂, S.τ w ∈ S.W₁ := commSub_top_map151b S.τ₂₁
  apply le_antisymm
  · exact Nat.card_le_card_of_injective (fun w : S.W₁ => (⟨S.τ w, h12 w w.2⟩ : S.W₂))
      (fun a b h => Subtype.ext (S.τ.injective (congrArg Subtype.val h)))
  · exact Nat.card_le_card_of_injective (fun w : S.W₂ => (⟨S.τ w, h21 w w.2⟩ : S.W₁))
      (fun a b h => Subtype.ext (S.τ.injective (congrArg Subtype.val h)))

theorem card_W₁ (hcard : Nat.card W = 256) : Nat.card S.W₁ = 16 := by
  have h1 := S.card_W₁_mul_card_W₂ hcard
  rw [← S.card_W₁_eq_card_W₂] at h1
  have h3 : Nat.card S.W₁ * Nat.card S.W₁ = 16 * 16 := by omega
  exact Nat.mul_self_inj.mp h3

theorem card_W₂ (hcard : Nat.card W = 256) : Nat.card S.W₂ = 16 := by
  rw [← S.card_W₁_eq_card_W₂]; exact S.card_W₁ hcard

omit [Finite W] in
theorem commSub_W₁ :
    commSub S.W₁ S.A₁ = S.W₁ := by
  obtain ⟨s11, -, s12, -⟩ := six_module151b S.comm S.winf
  apply le_antisymm (commSub_le_of_invariant s11)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, -, rfl⟩
  have hw : w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top w
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
  have : x (u * v) * (u * v)⁻¹ = x u * u⁻¹ := by
    rw [map_mul, s12 x hx v hv]
    group
  rw [this]
  exact Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩

theorem fixV_inf_a₁ (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) :
    S.W₁ ⊓ fixV (Subgroup.zpowers S.a₁) = ⊥ := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨s11, -, -, -⟩ := six_module151b S.comm S.winf
  refine fixV_inf_eq_bot_of_commSub151b hW (a := S.a₁) (s := S.s₁) (A := S.A₁) ?_ (S.s₁_sq hp)
    (S.s₁_a₁ hp) ?_ S.a₁_mem s11 S.commSub_W₁
  · rw [orderOf_eq_prime (S.a₁_pow hp) (S.a₁_ne_one hp)]
    rcases hp with rfl | rfl <;> decide
  · intro x hx
    obtain ⟨y, rfl⟩ := S.exists_ι₁ hx
    obtain ⟨k, hk | hk⟩ := dih_gen151b hp y
    · exact ⟨k.val, Or.inl (by rw [hk, ι₁_r S hp])⟩
    · refine ⟨k.val, Or.inr ?_⟩
      rw [hk, map_mul, ι₁_r S hp, s₁, ι_inl]

theorem fixV_inf_a₂ (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) :
    S.W₂ ⊓ fixV (Subgroup.zpowers S.a₂) = ⊥ := by
  have := S.swap.fixV_inf_a₁ hp hW
  rwa [swap_a₁, swap_W₁] at this

omit [Finite W] in
theorem ι₂_r (hp : p = 3 ∨ p = 5) (k : ZMod p) : S.ι₂ (DihedralGroup.r k) = S.a₂ ^ k.val := by
  have := S.swap.ι₁_r hp k
  rwa [swap_ι₁, swap_a₁] at this

omit [Finite W] in
theorem a₁_eq_ι₁ : S.a₁ = S.ι₁ (DihedralGroup.r 1) := S.ι_inl _

omit [Finite W] in
theorem a₂_eq_ι₂ : S.a₂ = S.ι₂ (DihedralGroup.r 1) := S.ι_inr _

omit [Finite W] in
theorem zpowers_ι₁_r (hp : p = 3 ∨ p = 5) {i : ZMod p} (hi : i ≠ 0) :
    Subgroup.zpowers (S.ι₁ (DihedralGroup.r i)) = Subgroup.zpowers S.a₁ := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le, S.ι₁_r hp]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    obtain ⟨n, hn⟩ := dih_rot_gen151b hp i hi
    have : S.a₁ = S.ι₁ (DihedralGroup.r i) ^ (n : ℕ) := by
      rw [← map_pow, hn, a₁_eq_ι₁]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit [Finite W] in
theorem zpowers_ι₂_r (hp : p = 3 ∨ p = 5) {i : ZMod p} (hi : i ≠ 0) :
    Subgroup.zpowers (S.ι₂ (DihedralGroup.r i)) = Subgroup.zpowers S.a₂ := by
  have := S.swap.zpowers_ι₁_r hp hi
  rwa [swap_ι₁, swap_a₁] at this

omit [Finite W] in
theorem exists_ι_of_pow (hp : p = 3 ∨ p = 5) {y : MulAut W} (hy : y ∈ S.A₁ ⊔ S.A₂)
    (hyp : y ^ p = 1) : ∃ i j : ZMod p, y = S.ι₁ (DihedralGroup.r i) * S.ι₂ (DihedralGroup.r j) := by
  rw [← S.range_ι] at hy
  obtain ⟨w, rfl⟩ := hy
  have h : w ^ p = 1 := S.ι_injective (by rw [map_pow, hyp, map_one])
  obtain ⟨i, j, rfl⟩ := dih_cube151b hp w h
  exact ⟨i, j, rfl⟩

omit [Finite W] in
theorem not_conj_both_first (hp : p = 3 ∨ p = 5) {g : MulAut W} {k k' : ZMod p} (hk : k ≠ 0)
    (h₁ : g * S.a₁ * g⁻¹ = S.ι₁ (DihedralGroup.r k))
    (h₂ : g * S.a₂ * g⁻¹ = S.ι₁ (DihedralGroup.r k')) : False := by
  have hz : S.ι₁ (DihedralGroup.r k') ∈ Subgroup.zpowers (S.ι₁ (DihedralGroup.r k)) := by
    rw [S.zpowers_ι₁_r hp hk, S.ι₁_r hp]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← h₁, ← h₂, conj_zpow] at hm
  have h3 : S.a₁ ^ m = S.a₂ := mul_left_cancel (mul_right_cancel hm)
  have h4 : S.a₂ ∈ S.A₁ := by
    rw [← h3]; exact S.A₁.zpow_mem S.a₁_mem m
  have h5 : S.a₂ ∈ S.A₁ ⊓ S.A₂ := ⟨h4, S.a₂_mem⟩
  rw [S.inf, Subgroup.mem_bot] at h5
  exact S.a₂_ne_one hp h5

theorem perm (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : g * S.a₁ * g⁻¹ ∈ S.A₁ ⊔ S.A₂) :
    (∃ k : ZMod p, k ≠ 0 ∧ g * S.a₁ * g⁻¹ = S.ι₁ (DihedralGroup.r k)) ∨
      (∃ k : ZMod p, k ≠ 0 ∧ g * S.a₁ * g⁻¹ = S.ι₂ (DihedralGroup.r k)) := by
  have hy3 : (g * S.a₁ * g⁻¹) ^ p = 1 := by rw [conj_pow, S.a₁_pow hp]; simp
  obtain ⟨i, j, hij⟩ := S.exists_ι_of_pow hp hg hy3
  have hy1 : g * S.a₁ * g⁻¹ ≠ 1 := by
    intro h
    apply S.a₁_ne_one hp
    calc S.a₁ = g⁻¹ * (g * S.a₁ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  by_cases hi : i = 0
  · right
    refine ⟨j, fun hj => hy1 ?_, ?_⟩
    · rw [hij, hi, hj, DihedralGroup.r_zero, map_one, map_one, one_mul]
    · rw [hij, hi, DihedralGroup.r_zero, map_one, one_mul]
  by_cases hj : j = 0
  · left
    refine ⟨i, hi, ?_⟩
    rw [hij, hj, DihedralGroup.r_zero, map_one, mul_one]
  exfalso
  obtain ⟨s11, s22, s12, s21⟩ := six_module151b S.comm S.winf
  have hrk := rkIdx_fixV_mul151b S.wsup S.winf (a₁ := S.ι₁ (DihedralGroup.r i))
    (a₂ := S.ι₂ (DihedralGroup.r j)) (fun w hw => s11 _ (S.ι₁_mem _) w hw)
    (fun w hw => s22 _ (S.ι₂_mem _) w hw) (fun w hw => s12 _ (S.ι₁_mem _) w hw)
    (fun w hw => s21 _ (S.ι₂_mem _) w hw)
  rw [← hij, rkIdx_fixV_conj151b, S.zpowers_ι₁_r hp hi, S.zpowers_ι₂_r hp hj] at hrk
  have hpos := rkIdx_pos_of_ne_one151b hW (S.a₂_ne_one hp)
  omega

omit [Finite W] in
theorem not_conj_both_second (hp : p = 3 ∨ p = 5) {g : MulAut W} {k k' : ZMod p} (hk' : k' ≠ 0)
    (h₁ : g * S.a₁ * g⁻¹ = S.ι₂ (DihedralGroup.r k))
    (h₂ : g * S.a₂ * g⁻¹ = S.ι₂ (DihedralGroup.r k')) : False :=
  S.swap.not_conj_both_first hp (g := g) (k := k') (k' := k) hk'
    (by rw [swap_a₁, swap_ι₁]; exact h₂) (by rw [swap_a₂, swap_ι₁]; exact h₁)

@[expose] def TypeI (g : MulAut W) : Prop :=
  g * S.a₁ * g⁻¹ ∈ Subgroup.zpowers S.a₁ ∧ g * S.a₂ * g⁻¹ ∈ Subgroup.zpowers S.a₂

@[expose] def TypeII (g : MulAut W) : Prop :=
  g * S.a₁ * g⁻¹ ∈ Subgroup.zpowers S.a₂ ∧ g * S.a₂ * g⁻¹ ∈ Subgroup.zpowers S.a₁

omit [Finite W] in
theorem ι₁_r_mem (hp : p = 3 ∨ p = 5) (k : ZMod p) :
    S.ι₁ (DihedralGroup.r k) ∈ Subgroup.zpowers S.a₁ := by
  rw [S.ι₁_r hp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit [Finite W] in
theorem ι₂_r_mem (hp : p = 3 ∨ p = 5) (k : ZMod p) :
    S.ι₂ (DihedralGroup.r k) ∈ Subgroup.zpowers S.a₂ := by
  rw [S.ι₂_r hp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem typeI_or_typeII_exp (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) :
    (∃ k k' : ZMod p, k ≠ 0 ∧ k' ≠ 0 ∧ g * S.a₁ * g⁻¹ = S.ι₁ (DihedralGroup.r k) ∧
        g * S.a₂ * g⁻¹ = S.ι₂ (DihedralGroup.r k')) ∨
      (∃ k k' : ZMod p, k ≠ 0 ∧ k' ≠ 0 ∧ g * S.a₁ * g⁻¹ = S.ι₂ (DihedralGroup.r k) ∧
        g * S.a₂ * g⁻¹ = S.ι₁ (DihedralGroup.r k')) := by
  have h1 := S.perm hp hW (hg _ (Subgroup.mem_sup_left S.a₁_mem))
  have hg₂ : g * S.a₂ * g⁻¹ ∈ S.A₂ ⊔ S.A₁ := by
    rw [sup_comm]; exact hg _ (Subgroup.mem_sup_right S.a₂_mem)
  have h2 := S.swap.perm hp hW (g := g) (by rw [swap_a₁]; exact hg₂)
  rw [swap_a₁, swap_ι₁, swap_ι₂] at h2
  rcases h1 with ⟨k, hk, h1⟩ | ⟨k, hk, h1⟩ <;> rcases h2 with ⟨k', hk', h2⟩ | ⟨k', hk', h2⟩
  · exact Or.inl ⟨k, k', hk, hk', h1, h2⟩
  · exact absurd (S.not_conj_both_first hp hk h1 h2) id
  · exact absurd (S.not_conj_both_second hp hk' h1 h2) id
  · exact Or.inr ⟨k, k', hk, hk', h1, h2⟩

theorem typeI_or_typeII (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) : S.TypeI g ∨ S.TypeII g := by
  rcases S.typeI_or_typeII_exp hp hW hg with ⟨k, k', -, -, h1, h2⟩ | ⟨k, k', -, -, h1, h2⟩
  · exact Or.inl ⟨h1 ▸ S.ι₁_r_mem hp k, h2 ▸ S.ι₂_r_mem hp k'⟩
  · exact Or.inr ⟨h1 ▸ S.ι₂_r_mem hp k, h2 ▸ S.ι₁_r_mem hp k'⟩

theorem typeII_of_swap (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (h₁ : ∀ a ∈ S.A₁, g * a * g⁻¹ ∈ S.A₂) : S.TypeII g := by
  rcases S.typeI_or_typeII hp hW hg with hI | hII
  · exfalso
    have h1 : g * S.a₁ * g⁻¹ ∈ S.A₁ := Subgroup.zpowers_le.mpr S.a₁_mem hI.1
    have h3 : g * S.a₁ * g⁻¹ ∈ S.A₁ ⊓ S.A₂ := ⟨h1, h₁ S.a₁ S.a₁_mem⟩
    rw [S.inf, Subgroup.mem_bot] at h3
    apply S.a₁_ne_one hp
    calc S.a₁ = g⁻¹ * (g * S.a₁ * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  · exact hII

omit [Finite W] in
theorem typeI_mul_of_typeII {f g : MulAut W} (hf : S.TypeII f) (hg : S.TypeII g) :
    S.TypeI (f * g) := by
  refine ⟨?_, ?_⟩
  · have : f * g * S.a₁ * (f * g)⁻¹ = f * (g * S.a₁ * g⁻¹) * f⁻¹ := by group
    rw [this]
    exact conj_mem_zpowers151b hf.2 _ hg.1
  · have : f * g * S.a₂ * (f * g)⁻¹ = f * (g * S.a₂ * g⁻¹) * f⁻¹ := by group
    rw [this]
    exact conj_mem_zpowers151b hf.1 _ hg.2


theorem W₁_eq_commSub_a₁ (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1) :
    S.W₁ = commSub (⊤ : Subgroup W) (Subgroup.zpowers S.a₁) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers S.a₁)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (S.a₁_pow hp) (S.a₁_ne_one hp)]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨s11, -, -, -⟩ := six_module151b S.comm S.winf
  have hinv : ∀ g ∈ Subgroup.zpowers S.a₁, ∀ w ∈ S.W₁, g w ∈ S.W₁ := fun g hg w hw =>
    s11 g (Subgroup.zpowers_le.mpr S.a₁_mem hg) w hw
  have hdec := coprime_decomp hodd hW hinv
  apply le_antisymm
  · have h1 := hdec.1
    rw [S.fixV_inf_a₁ hp hW, sup_bot_eq] at h1
    rw [← h1]
    exact commSub_mono le_top le_rfl
  · exact commSub_mono le_top (Subgroup.zpowers_le.mpr S.a₁_mem)

theorem W₁_le_fixV_of_commute_involution (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    (hp5 : p = 5) {d : MulAut W} (hd2 : d ^ 2 = 1) (hd₁ : d * S.a₁ = S.a₁ * d) :
    S.W₁ ≤ fixV (Subgroup.zpowers d) := by
  have hp : p = 3 ∨ p = 5 := Or.inr hp5
  obtain ⟨s11, -, -, -⟩ := six_module151b S.comm S.winf
  have hda : d * S.a₁ * d⁻¹ = S.a₁ := by rw [hd₁]; group
  have hP : ∀ x ∈ Subgroup.zpowers S.a₁, d * x * d⁻¹ ∈ Subgroup.zpowers S.a₁ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hda]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hst : ∀ w ∈ S.W₁, d w ∈ S.W₁ := by
    intro w hw
    rw [S.W₁_eq_commSub_a₁ hp hW] at hw ⊢
    exact commSub_top_stable151b hP w hw
  have ha5 : S.a₁ ^ 5 = 1 := hp5 ▸ S.a₁_pow hp
  exact fixV_of_commute_involution151b hW (S.card_W₁ hcard) ha5 (S.fixV_inf_a₁ hp hW) hd2
    hd₁.symm (fun w hw => s11 _ S.a₁_mem w hw) hst

theorem eq_one_of_commute_involution (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    (hp5 : p = 5) {d : MulAut W} (hd2 : d ^ 2 = 1) (hd₁ : d * S.a₁ = S.a₁ * d)
    (hd₂ : d * S.a₂ = S.a₂ * d) : d = 1 := by
  have h1 := S.W₁_le_fixV_of_commute_involution hW hcard hp5 hd2 hd₁
  have h2 := S.swap.W₁_le_fixV_of_commute_involution hW hcard hp5 hd2
    (by rw [swap_a₁]; exact hd₂)
  rw [swap_W₁] at h2
  have : ⊤ ≤ fixV (Subgroup.zpowers d) := by rw [← S.wsup]; exact sup_le h1 h2
  exact eq_one_of_fixV_eq_top (top_le_iff.mp this)

theorem W₁_le_fixV_of_prime (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 256) {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {c : MulAut W} (hcq : c ^ q = 1)
    (hc₁ : ∀ x ∈ S.A₁, c * x = x * c) : S.W₁ ≤ fixV (Subgroup.zpowers c) := by
  obtain ⟨s11, -, s12, -⟩ := six_module151b S.comm S.winf
  refine fix_of_prime_ge_five151b hW (S.card_W₁ hcard) hq hcq ?_ ?_ ?_
  · intro w hw
    refine commSub_top_stable151b (X := S.A₁) (g := c) (fun x hx => ?_) w hw
    have h : c * x * c⁻¹ = x := by rw [hc₁ x hx]; group
    rw [h]
    exact hx
  · intro _
    refine ⟨S.s₁, S.s₁_sq hp, hc₁ _ S.s₁_mem, fun w hw => s11 _ S.s₁_mem w hw, ?_⟩
    intro hle
    apply S.s₁_ne_one hp
    have h2 : S.W₂ ≤ fixV (Subgroup.zpowers S.s₁) := fun w hw =>
      mem_fixV_zpowers_iff.mpr (s12 _ S.s₁_mem w hw)
    have : ⊤ ≤ fixV (Subgroup.zpowers S.s₁) := by rw [← S.wsup]; exact sup_le hle h2
    exact eq_one_of_fixV_eq_top (top_le_iff.mp this)
  · intro _
    exact ⟨S.a₁, hc₁ _ S.a₁_mem, fun w hw => s11 _ S.a₁_mem w hw, S.fixV_inf_a₁ hp hW⟩

theorem eq_one_of_prime_ge_five (hp : p = 3 ∨ p = 5) (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 256) {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {c : MulAut W} (hcq : c ^ q = 1)
    (hc₁ : ∀ x ∈ S.A₁, c * x = x * c) (hc₂ : ∀ x ∈ S.A₂, c * x = x * c) : c = 1 := by
  have h1 := S.W₁_le_fixV_of_prime hp hW hcard hq hcq hc₁
  have h2 := S.swap.W₁_le_fixV_of_prime hp hW hcard hq hcq hc₂
  rw [swap_W₁] at h2
  have : ⊤ ≤ fixV (Subgroup.zpowers c) := by rw [← S.wsup]; exact sup_le h1 h2
  exact eq_one_of_fixV_eq_top (top_le_iff.mp this)

end FiniteW

end SixData151b

end CFSG.Quasithin
