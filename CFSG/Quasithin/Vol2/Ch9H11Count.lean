module

public import CFSG.Quasithin.Vol2.Ch9H11Norm

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11P

open CFSG.Quasithin (fixV mem_fixV rk rkIdx)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def IsSemi (x : MulAut (VM K)) (σ : K ≃+* K) : Prop :=
  ∀ (l : K) (X : Mat K), addMap x (l • X) = σ l • addMap x X

theorem IsSemi.mul {x y : MulAut (VM K)} {σ τ : K ≃+* K} (hx : IsSemi x σ) (hy : IsSemi y τ) :
    IsSemi (x * y) (σ * τ) := fun l X => by
  rw [addMap_mul, hy, hx, addMap_mul]
  rfl

theorem IsSemi.inv {x : MulAut (VM K)} {σ : K ≃+* K} (hx : IsSemi x σ) : IsSemi x⁻¹ σ⁻¹ :=
  fun l X => by
    apply addMap_injective x
    rw [addMap_inv_apply, hx, addMap_inv_apply]
    show l • X = σ (σ.symm l) • X
    rw [RingEquiv.apply_symm_apply]

theorem IsSemi.unique {x : MulAut (VM K)} {σ τ : K ≃+* K} (hσ : IsSemi x σ) (hτ : IsSemi x τ) :
    σ = τ := by
  refine RingEquiv.ext fun l => ?_
  have h1 := (hσ l (E11 K)).symm.trans (hτ l (E11 K))
  have h0 : addMap x (E11 K) ≠ 0 := fun h0 =>
    E11_ne_zero (addMap_injective x (h0.trans (map_zero _).symm))
  have h2 : (σ l - τ l) • addMap x (E11 K) = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h h0

@[expose] def kLin (K : Type) [Field K] : Subgroup (MulAut (VM K)) where
  carrier := {x | IsSemi x 1}
  mul_mem' {x y} hx hy := by
    have := IsSemi.mul hx hy
    rwa [one_mul] at this
  one_mem' := fun l X => rfl
  inv_mem' {x} hx := by
    have := IsSemi.inv hx
    rwa [inv_one] at this

theorem rho_mem_kLin (p : SL₂ K × SL₂ K) : rho p ∈ kLin K := fun l X => by
  show (p.1 : Mat K) * (l • X) * (p.2 : Mat K)ᵀ = l • ((p.1 : Mat K) * X * (p.2 : Mat K)ᵀ)
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem Lm_le_kLin : Lm K ≤ kLin K := by
  rintro _ ⟨p, rfl⟩
  exact rho_mem_kLin p

abbrev MemM (Y : Subgroup (VM K)) (X : Mat K) : Prop := Multiplicative.ofAdd X ∈ Y

theorem card_eq_card_memM (Y : Subgroup (VM K)) :
    Nat.card Y = Nat.card {X : Mat K // MemM Y X} :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun v => by simp [MemM])

theorem memM_fixV {A : Subgroup (MulAut (VM K))} {X : Mat K} :
    MemM (fixV A) X ↔ ∀ a ∈ A, addMap a X = X := by
  constructor
  · intro h a ha
    exact congrArg Multiplicative.toAdd (h a ha)
  · intro h a ha
    exact congrArg Multiplicative.ofAdd (h a ha)

@[expose] def KClosed (Y : Subgroup (VM K)) : Prop :=
  ∀ (l : K) (X : Mat K), MemM Y X → MemM Y (l • X)

theorem kClosed_fixV {A : Subgroup (MulAut (VM K))} (hA : A ≤ kLin K) : KClosed (fixV A) := by
  intro l X hX
  rw [memM_fixV] at hX ⊢
  intro a ha
  rw [(hA ha) l X, hX a ha]
  rfl

@[expose] def toSub (Y : Subgroup (VM K)) (hY : KClosed Y) : Submodule K (Mat K) where
  carrier := {X | MemM Y X}
  add_mem' hX hZ := Y.mul_mem hX hZ
  zero_mem' := Y.one_mem
  smul_mem' l X hX := hY l X hX

theorem card_VM : Nat.card (VM K) = Nat.card K ^ 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : VM K ≃ Mat K)]
  show Nat.card (Fin 2 → Fin 2 → K) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]

variable [Finite K]

omit [Finite K] in
theorem card_kClosed {Y : Subgroup (VM K)} (hY : KClosed Y) :
    ∃ j ≤ 4, Nat.card Y = Nat.card K ^ j := by
  have hc : Nat.card Y = Nat.card (toSub Y hY) := by
    rw [card_eq_card_memM]
    rfl
  refine ⟨Module.finrank K (toSub Y hY), ?_, by
    rw [hc, Module.natCard_eq_pow_finrank (K := K) (V := toSub Y hY)]⟩
  have h1 := Submodule.finrank_le (toSub Y hY)
  rw [Module.finrank_matrix, Module.finrank_self] at h1
  simpa using h1

theorem card_lt_of_lt {G : Type*} [Group G] [Finite G] {Y Z : Subgroup G} (h : Y < Z) :
    Nat.card Y < Nat.card Z := by
  refine lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun hc => h.ne ?_
  exact Subgroup.eq_of_le_of_card_ge h.le hc.ge

theorem card_mul_le_of_lt {Y Z : Subgroup (VM K)} (hY : KClosed Y) (hZ : KClosed Z)
    (hYZ : Y < Z) : Nat.card K * Nat.card Y ≤ Nat.card Z := by
  obtain ⟨a, -, ha⟩ := card_kClosed hY
  obtain ⟨b, -, hb⟩ := card_kClosed hZ
  have hlt := card_lt_of_lt hYZ
  rw [ha, hb] at hlt
  rw [ha, hb]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hab : a < b := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  calc Nat.card K * Nat.card K ^ a = Nat.card K ^ (a + 1) := by ring
    _ ≤ Nat.card K ^ b := Nat.pow_le_pow_right (by omega) hab

theorem card_fix_sq [CharP K 2] {Y : Subgroup (VM K)} (hY : KClosed Y) {f : MulAut (VM K)}
    {σ : K ≃+* K} (hf : IsSemi f σ) (hσ : σ ≠ 1) (hff : f * f = 1)
    (hfY : ∀ X, MemM Y X → MemM Y (addMap f X)) :
    Nat.card {X : Mat K // MemM Y X ∧ addMap f X = X} *
      Nat.card {X : Mat K // MemM Y X ∧ addMap f X = X} = Nat.card {X : Mat K // MemM Y X} := by
  have hff' : ∀ X, addMap f (addMap f X) = X := fun X => by
    rw [← addMap_mul, hff, addMap_one]
  obtain ⟨θ, hθ⟩ : ∃ θ : K, σ θ ≠ θ := by
    by_contra h
    exact hσ (RingEquiv.ext fun θ => by_contra fun hθ => h ⟨θ, hθ⟩)
  have hne : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hD : θ + σ θ ≠ 0 := by
    intro h
    apply hθ
    have := h2 θ
    rw [← this] at h
    exact add_left_cancel h
  set C := {X : Mat K // MemM Y X ∧ addMap f X = X} with hC
  set W := {X : Mat K // MemM Y X} with hW
  have hmemY : ∀ (c₁ c₂ : C), MemM Y ((c₁ : Mat K) + θ • (c₂ : Mat K)) := fun c₁ c₂ =>
    Y.mul_mem c₁.2.1 (hY θ _ c₂.2.1)
  have hinj1 : Function.Injective (fun c : C × C =>
      (⟨(c.1 : Mat K) + θ • (c.2 : Mat K), hmemY c.1 c.2⟩ : W)) := by
    rintro ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ h
    have e : c₁ + θ • c₂ = d₁ + θ • d₂ := congrArg Subtype.val h
    have e' := congrArg (addMap f) e
    rw [map_add, map_add, hf, hf, hc₁.2, hc₂.2, hd₁.2, hd₂.2] at e'
    have e2 : (θ - σ θ) • c₂ = (θ - σ θ) • d₂ := by
      rw [sub_smul, sub_smul]
      have := congrArg₂ (· - ·) e e'
      rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub] at this
      exact this
    have hcd2 : c₂ = d₂ := smul_right_injective (Mat K) hne e2
    subst hcd2
    have hcd1 : c₁ = d₁ := add_right_cancel e
    subst hcd1
    rfl
  have hfix1 : ∀ y : W, MemM Y ((y : Mat K) + addMap f y) ∧
      addMap f ((y : Mat K) + addMap f y) = (y : Mat K) + addMap f y := fun y =>
    ⟨Y.mul_mem y.2 (hfY _ y.2), by rw [map_add, hff', add_comm]⟩
  have hfix2 : ∀ y : W, MemM Y (θ • (y : Mat K) + addMap f (θ • (y : Mat K))) ∧
      addMap f (θ • (y : Mat K) + addMap f (θ • (y : Mat K))) =
        θ • (y : Mat K) + addMap f (θ • (y : Mat K)) := fun y =>
    ⟨Y.mul_mem (hY θ _ y.2) (hfY _ (hY θ _ y.2)), by rw [map_add, hff', add_comm]⟩
  have hkey : ∀ y : Mat K, θ • y + addMap f (θ • y) + σ θ • (y + addMap f y) =
      (θ + σ θ) • y := by
    intro y
    rw [hf, smul_add, add_smul]
    have : σ θ • addMap f y + σ θ • addMap f y = 0 := by
      rw [← add_smul, h2, zero_smul]
    calc θ • y + σ θ • addMap f y + (σ θ • y + σ θ • addMap f y)
        = θ • y + σ θ • y + (σ θ • addMap f y + σ θ • addMap f y) := by abel
      _ = θ • y + σ θ • y := by rw [this, add_zero]
  have hinj2 : Function.Injective (fun y : W =>
      ((⟨(y : Mat K) + addMap f y, hfix1 y⟩ : C),
        (⟨θ • (y : Mat K) + addMap f (θ • (y : Mat K)), hfix2 y⟩ : C))) := by
    rintro ⟨y, hy⟩ ⟨z, hz⟩ h
    have e1 : y + addMap f y = z + addMap f z := congrArg (fun p : C × C => (p.1 : Mat K)) h
    have e2 : θ • y + addMap f (θ • y) = θ • z + addMap f (θ • z) :=
      congrArg (fun p : C × C => (p.2 : Mat K)) h
    have e3 : (θ + σ θ) • y = (θ + σ θ) • z := by rw [← hkey, ← hkey, e1, e2]
    exact Subtype.ext (smul_right_injective (Mat K) hD e3)
  have hfinW : Finite W := Subtype.finite
  have hfinC : Finite C := Subtype.finite
  have hle1 := Nat.card_le_card_of_injective _ hinj1
  have hle2 := Nat.card_le_card_of_injective _ hinj2
  rw [Nat.card_prod] at hle1 hle2
  exact le_antisymm hle1 hle2

theorem card_eq_two_mul {M : Type*} [Group M] {H G : Subgroup M} (hHG : H ≤ G) {a : M}
    (haG : a ∈ G) (haH : a ∉ H) (hcomm : ∀ g ∈ G, a * g = g * a)
    (hout : ∀ g ∈ G, g ∉ H → a * g ∈ H) : Nat.card G = 2 * Nat.card H := by
  have hidx : (H.subgroupOf G).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haG⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : M) ∈ H
    · refine Or.inr ⟨hb, fun h => haH ?_⟩
      have := H.mul_mem (H.inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hb⟩
      rw [← hcomm b b.2]
      exact hout b b.2 hb
  have h := (H.subgroupOf G).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG).toEquiv] at h
  rw [← h, mul_comm]

theorem rk_eq_of_card {W : Type*} [Group W] {r : ℕ} (h : Nat.card W = 2 ^ r) : rk W = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem rkIdx_eq_of_card {G : Type*} [Group G] {H : Subgroup G} {k m : ℕ}
    (hH : Nat.card H = 2 ^ k) (hG : Nat.card G = 2 ^ m) : rkIdx H = m - k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := H.card_mul_index
  rw [hH, hG] at h
  have hkm : k ≤ m := by
    by_contra hkm
    have : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hi : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at h
      exact pow_ne_zero m (by norm_num : (2 : ℕ) ≠ 0) h.symm
    nlinarith
  have hidx : H.index = 2 ^ (m - k) := by
    have h2 : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hkm]
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  unfold rkIdx
  rw [hidx, padicValNat.prime_pow]

end CFSG.Quasithin.H13.H11P

end
