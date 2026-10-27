module

public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Quasithin.H13.KG68

section Singer

variable {S : Type} [Group S]

structure SingerHyp (B W : Subgroup S) (x : S) : Prop where
  mem : x ∈ B
  inv : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W
  comm : ∀ a ∈ B, ∀ b ∈ B, ∀ w ∈ W, (a * b * a⁻¹ * b⁻¹) * w = w * (a * b * a⁻¹ * b⁻¹)
  trans : ∀ z ∈ W, z ≠ 1 → ∀ w ∈ W, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w

variable {B W : Subgroup S} {x : S}

theorem mem_normalizer_of_conj_le [Finite S] {Y : Subgroup S} {g : S}
    (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : g ∈ Subgroup.normalizer (Y : Set S) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨h p, fun hp => ?_⟩
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hp' : g * p * g⁻¹ ∈ Y.map (MulAut.conj g).toMonoidHom := by
    rw [heq]
    exact hp
  obtain ⟨y, hy, hyp⟩ := hp'
  have : y = p := by
    have hyp' : g * y * g⁻¹ = g * p * g⁻¹ := hyp
    exact mul_left_cancel (mul_right_cancel hyp')
  rw [← this]
  exact hy

theorem SingerHyp.exists_pow (h : SingerHyp B W x) {b : S} (hb : b ∈ B) :
    ∃ j : ℕ, ∀ w ∈ W, b * w * b⁻¹ = x ^ j * w * (x ^ j)⁻¹ := by
  by_cases hW : ∀ w ∈ W, w = 1
  · exact ⟨0, fun w hw => by rw [hW w hw]; simp⟩
  push Not at hW
  obtain ⟨z₀, hz₀, hz₀1⟩ := hW
  have hbz : b * z₀ * b⁻¹ ∈ W := h.inv b hb z₀ hz₀
  have hbz1 : b * z₀ * b⁻¹ ≠ 1 := by
    intro h1
    apply hz₀1
    have := congrArg (fun t => b⁻¹ * t * b) h1
    simpa [mul_assoc] using this
  obtain ⟨j, hj⟩ := h.trans z₀ hz₀ hz₀1 _ hbz hbz1
  refine ⟨j, fun w hw => ?_⟩
  set y : S := (x ^ j)⁻¹ * b with hy
  have hyB : y ∈ B := B.mul_mem (B.inv_mem (B.pow_mem h.mem j)) hb
  have hyz : y * z₀ * y⁻¹ = z₀ := by
    have e : y * z₀ * y⁻¹ = (x ^ j)⁻¹ * (b * z₀ * b⁻¹) * x ^ j := by rw [hy]; group
    rw [e, ← hj]
    group
  have hyw : y * w * y⁻¹ = w := by
    by_cases hw1 : w = 1
    · rw [hw1]; simp
    obtain ⟨i, hi⟩ := h.trans z₀ hz₀ hz₀1 w hw hw1
    set κ : S := y * x ^ i * y⁻¹ * (x ^ i)⁻¹ with hκ
    have hκc : κ * w = w * κ := by
      have := h.comm y hyB (x ^ i) (B.pow_mem h.mem i) w hw
      have e : y * x ^ i * y⁻¹ * (x ^ i)⁻¹ = κ := by rw [hκ]
      rw [e] at this
      exact this
    have e1 : y * x ^ i = κ * x ^ i * y := by rw [hκ]; group
    calc y * w * y⁻¹ = y * (x ^ i * z₀ * (x ^ i)⁻¹) * y⁻¹ := by rw [hi]
      _ = (y * x ^ i) * z₀ * (y * x ^ i)⁻¹ := by group
      _ = (κ * x ^ i * y) * z₀ * (κ * x ^ i * y)⁻¹ := by rw [e1]
      _ = κ * (x ^ i * (y * z₀ * y⁻¹) * (x ^ i)⁻¹) * κ⁻¹ := by group
      _ = κ * w * κ⁻¹ := by rw [hyz, hi]
      _ = w := by rw [hκc]; group
  have e2 : b = x ^ j * y := by rw [hy]; group
  rw [e2]
  calc x ^ j * y * w * (x ^ j * y)⁻¹ = x ^ j * (y * w * y⁻¹) * (x ^ j)⁻¹ := by group
    _ = x ^ j * w * (x ^ j)⁻¹ := by rw [hyw]

theorem SingerHyp.eq_of_invariant (h : SingerHyp B W x) {W' : Subgroup S} (hW'W : W' ≤ W)
    (hx : ∀ w ∈ W', x * w * x⁻¹ ∈ W') (hne : W' ≠ ⊥) : W' = W := by
  refine le_antisymm hW'W fun w hw => ?_
  by_cases hw1 : w = 1
  · rw [hw1]
    exact W'.one_mem
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ W', z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall W').2 hcon)
  obtain ⟨j, hj⟩ := h.trans z (hW'W hz) hz1 w hw hw1
  rw [← hj]
  have hall : ∀ (k : ℕ) (u : S), u ∈ W' → x ^ k * u * (x ^ k)⁻¹ ∈ W' := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      have := hx _ (ih u hu)
      have e : x * (x ^ k * u * (x ^ k)⁻¹) * x⁻¹ = x ^ (k + 1) * u * (x ^ (k + 1))⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rwa [e] at this
  exact hall j z hz

theorem card_subtype_ne_one (X : Type) [Group X] [Finite X] :
    Nat.card {x : X // x ≠ 1} = Nat.card X - 1 := by
  classical
  have := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun x : X => x = 1)
  rw [Fintype.card_subtype_eq] at h
  simp

theorem SingerHyp.eq_one_of_fixed [Finite S] (h : SingerHyp B W x) (h3 : 3 ≤ Nat.card W) {w : S}
    (hw : w ∈ W) (hfix : x * w * x⁻¹ = w) : w = 1 := by
  by_contra hw1
  have hc : Commute x w := by
    have : x * w = w * x := by
      calc x * w = (x * w * x⁻¹) * x := by group
        _ = w * x := by rw [hfix]
    exact this
  have hsub : (W : Set S) ⊆ ({1, w} : Set S) := by
    intro u hu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · right
      obtain ⟨j, hj⟩ := h.trans w hw hw1 u hu hu1
      have hcj : Commute (x ^ j) w := hc.pow_left j
      have : x ^ j * w * (x ^ j)⁻¹ = w := by
        calc x ^ j * w * (x ^ j)⁻¹ = (w * x ^ j) * (x ^ j)⁻¹ := by rw [hcj.eq]
          _ = w := by group
      rw [← hj, this]
      exact Set.mem_singleton w
  have h1 : Set.ncard (W : Set S) ≤ Set.ncard ({1, w} : Set S) :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Set.ncard ({1, w} : Set S) ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  have h3' : Nat.card W = Set.ncard (W : Set S) := Nat.card_coe_set_eq (W : Set S)
  omega

theorem SingerHyp.orderOf_actHom [Finite S] (h : SingerHyp B W x) (hW : W ≠ ⊥)
    (hBW : B ≤ Subgroup.normalizer (W : Set S)) :
    orderOf (actHom W B hBW ⟨x, h.mem⟩) = Nat.card W - 1 := by
  classical
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ W, z ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hW ((Subgroup.eq_bot_iff_forall W).2 hc)
  set ρ := actHom W B hBW with hρ
  set r : MulAut ↥W := ρ ⟨x, h.mem⟩ with hr
  have hrpow : ∀ (k : ℕ) (w : ↥W), (((r ^ k) w : ↥W) : S) = x ^ k * w * (x ^ k)⁻¹ := by
    intro k w
    have hk : r ^ k = ρ (⟨x, h.mem⟩ ^ k) := by rw [hr, map_pow]
    rw [hk, hρ, actHom_apply, conjOn_coe]
    rfl
  set z₀' : ↥W := ⟨z₀, hz₀⟩ with hz₀'
  have hz₀'1 : z₀' ≠ 1 := fun h1 => hz₀1 (congrArg Subtype.val h1)
  have hcomm : ∀ i k : ℕ, ∀ w : ↥W, (r ^ i) ((r ^ k) w) = (r ^ k) ((r ^ i) w) := by
    intro i k w
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]
  have hnat : ∀ φ ∈ Subgroup.zpowers r, ∃ k : ℕ, r ^ k = φ := fun φ hφ =>
    (mem_powers_iff_mem_zpowers).2 hφ
  have hreach : ∀ w : ↥W, w ≠ 1 → ∃ i : ℕ, (r ^ i) z₀' = w := by
    intro w hw
    obtain ⟨i, hi⟩ := h.trans z₀ hz₀ hz₀1 w w.2 (fun h1 => hw (Subtype.ext h1))
    exact ⟨i, Subtype.ext (by rw [hrpow]; exact hi)⟩
  let f : Subgroup.zpowers r → {w : ↥W // w ≠ 1} := fun φ =>
    ⟨(φ : MulAut ↥W) z₀', fun h1 =>
      hz₀'1 ((map_eq_one_iff (φ : MulAut ↥W) (EquivLike.injective _)).1 h1)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨i, hi⟩ := hreach w hw
    exact ⟨⟨r ^ i, Subgroup.pow_mem _ (Subgroup.mem_zpowers r) i⟩, Subtype.ext hi⟩
  have hinj : Function.Injective f := by
    rintro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩ h12
    have h12' : φ₁ z₀' = φ₂ z₀' := congrArg (fun t => (t : {w : ↥W // w ≠ 1}).1) h12
    obtain ⟨k₁, rfl⟩ := hnat φ₁ hφ₁
    obtain ⟨k₂, rfl⟩ := hnat φ₂ hφ₂
    refine Subtype.ext (MulEquiv.ext fun w => ?_)
    by_cases hw : w = 1
    · rw [hw, map_one, map_one]
    obtain ⟨i, rfl⟩ := hreach w hw
    show (r ^ k₁) ((r ^ i) z₀') = (r ^ k₂) ((r ^ i) z₀')
    rw [hcomm k₁ i, hcomm k₂ i, h12']
  have hcard : Nat.card (Subgroup.zpowers r) = Nat.card W - 1 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
    exact card_subtype_ne_one ↥W
  rw [← Nat.card_zpowers, hcard]

end Singer

end E68Proof

end E6

end CFSG.Quasithin
