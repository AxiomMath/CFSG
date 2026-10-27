module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

namespace Item211Res5Proof

open Item211Res4Proof

section SL2

variable {F : Type} [Field F]

theorem eq_one_or_eq_of_commute_of_cube (h3 : (3 : F) ≠ 0) {X B : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) (hB3 : B ^ 3 = 1) (hBX : B * X = X * B) : B = 1 ∨ B = X ∨ B = X * X := by
  have hsum := sq_add_self_add_one hX3 hX1
  have hcube : ∀ W : SL(2, F), W ^ 3 = 1 →
      W = 1 ∨ (W : Matrix (Fin 2) (Fin 2) F).trace = -1 := by
    intro W hW
    rcases Item211Lie3Proof.eq_one_or_trace_eq_neg_one W.2 (mat_cube_eq_one hW) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  have hc : Commute B X := hBX
  have hBX3 : (B * X) ^ 3 = 1 := by rw [hc.mul_pow, hB3, hX3, one_mul]
  have hBXX3 : (B * (X * X)) ^ 3 = 1 := by
    rw [(hc.mul_right hc).mul_pow, hB3, ← sq, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hX3,
      one_pow, one_mul]
  have hX3' : X * X * X = 1 := by rw [← pow_three', hX3]
  have htr : (B : Matrix (Fin 2) (Fin 2) F).trace +
      ((B * X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace +
      ((B * (X * X) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [← Matrix.trace_add, ← Matrix.trace_add]
    have e : (B : Matrix (Fin 2) (Fin 2) F) + B * X + B * (X * X) =
        B * ((X : Matrix (Fin 2) (Fin 2) F) * X + X + 1) := by
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
      abel
    rw [e, hsum, Matrix.mul_zero, Matrix.trace_zero]
  rcases hcube B hB3 with h1 | h1
  · exact Or.inl h1
  rcases hcube _ hBX3 with h2 | h2
  · right; right
    calc B = B * X * (X * X) := by rw [mul_assoc, ← mul_assoc X, hX3', mul_one]
      _ = X * X := by rw [h2, one_mul]
  rcases hcube _ hBXX3 with h3' | h3'
  · right; left
    calc B = B * (X * X) * X := by rw [mul_assoc, hX3', mul_one]
      _ = X := by rw [h3', one_mul]
  exfalso
  apply h3
  rw [h1, h2, h3'] at htr
  linear_combination -htr

theorem neg_one_ne_one_sl2 (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e' : (-1 : F) = 1 := by simpa using e
  apply h2
  linear_combination -e'

theorem neg_one_mul_pow_three (B : SL(2, F)) : (-1 * B) ^ 3 = -1 * B ^ 3 := by
  rw [(show Commute (-1 : SL(2, F)) B from neg_one_mul_comm B).mul_pow, neg_one_pow_three]

theorem neg_one_mul_neg_one_sl2 : (-1 : SL(2, F)) * -1 = 1 := by
  apply Subtype.ext
  simp

end SL2

section Blocks

variable {G : Type} [Group G] {F : Type} [Field F] {κ₁ κ₂ : SL(2, F) →* G} {z : G}

structure BlockPair (κ₁ κ₂ : SL(2, F) →* G) (z : G) : Prop where
  inj₁ : Function.Injective κ₁
  inj₂ : Function.Injective κ₂
  comm : ∀ a b, κ₁ a * κ₂ b = κ₂ b * κ₁ a
  neg₁ : κ₁ (-1) = z
  neg₂ : κ₂ (-1) = z
  norm₁ : ∀ h : G, h * z = z * h → ∀ c, h * κ₁ c * h⁻¹ ∈ κ₁.range
  norm₂ : ∀ h : G, h * z = z * h → ∀ c, h * κ₂ c * h⁻¹ ∈ κ₂.range
  decomp : ∀ x : G, x * z = z * x → x ^ 3 = 1 → ∃ a b, x = κ₁ a * κ₂ b

theorem BlockPair.symm (hB : BlockPair κ₁ κ₂ z) : BlockPair κ₂ κ₁ z where
  inj₁ := hB.inj₂
  inj₂ := hB.inj₁
  comm a b := (hB.comm b a).symm
  neg₁ := hB.neg₂
  neg₂ := hB.neg₁
  norm₁ := hB.norm₂
  norm₂ := hB.norm₁
  decomp x hx hx3 := by
    obtain ⟨a, b, rfl⟩ := hB.decomp x hx hx3
    exact ⟨b, a, (hB.comm a b)⟩

theorem BlockPair.mul_z₁ (hB : BlockPair κ₁ κ₂ z) (c : SL(2, F)) : κ₁ c * z = z * κ₁ c := by
  rw [← hB.neg₂]
  exact hB.comm c (-1)

theorem BlockPair.z_mul_z (hB : BlockPair κ₁ κ₂ z) : z * z = 1 := by
  rw [← hB.neg₁, ← map_mul, neg_one_mul_neg_one_sl2, map_one]

theorem BlockPair.eq_one_or_neg_of_eq (hB : BlockPair κ₁ κ₂ z) {a b : SL(2, F)}
    (h : κ₁ a = κ₂ b) : a = 1 ∨ a = -1 := by
  apply Item211Lie2Proof.eq_one_or_eq_neg_one_of_mem_center
  rw [Subgroup.mem_center_iff]
  intro c
  apply hB.inj₁
  rw [map_mul, map_mul, h]
  exact hB.comm c b

theorem BlockPair.cube_decomp (hB : BlockPair κ₁ κ₂ z) {x : G} (hxz : x * z = z * x)
    (hx3 : x ^ 3 = 1) : ∃ a b : SL(2, F), x = κ₁ a * κ₂ b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 := by
  obtain ⟨a, b, rfl⟩ := hB.decomp x hxz hx3
  have hc : Commute (κ₁ a) (κ₂ b) := hB.comm a b
  have h1 : κ₁ (a ^ 3) * κ₂ (b ^ 3) = 1 := by rw [map_pow, map_pow, ← hc.mul_pow, hx3]
  have h2 : κ₁ (a ^ 3) = (κ₂ (b ^ 3))⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [← map_inv] at h2
  rcases hB.eq_one_or_neg_of_eq h2 with ha | ha
  · refine ⟨a, b, rfl, ha, hB.inj₂ ?_⟩
    rw [ha, map_one, one_mul] at h1
    rw [h1, map_one]
  · have hb : b ^ 3 = -1 := by
      apply hB.inj₂
      rw [hB.neg₂, ← hB.neg₁, ← ha]
      have h3 : κ₂ (b ^ 3) = (κ₁ (a ^ 3))⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3, ha, ← map_inv, show (-1 : SL(2, F))⁻¹ = -1 from
        inv_eq_of_mul_eq_one_left neg_one_mul_neg_one_sl2]
    refine ⟨-1 * a, -1 * b, ?_, ?_, ?_⟩
    · rw [map_mul, map_mul, hB.neg₁, hB.neg₂]
      calc κ₁ a * κ₂ b = κ₁ a * (z * z) * κ₂ b := by rw [hB.z_mul_z, mul_one]
        _ = z * κ₁ a * (z * κ₂ b) := by rw [← hB.mul_z₁ a]; group
    · rw [neg_one_mul_pow_three, ha, neg_one_mul_neg_one_sl2]
    · rw [neg_one_mul_pow_three, hb, neg_one_mul_neg_one_sl2]

theorem BlockPair.commute_parts (hB : BlockPair κ₁ κ₂ z) (h2 : (2 : F) ≠ 0) {h : G}
    (hn₁ : ∀ c, h * κ₁ c * h⁻¹ ∈ κ₁.range) (hn₂ : ∀ c, h * κ₂ c * h⁻¹ ∈ κ₂.range)
    {a b : SL(2, F)} (ha3 : a ^ 3 = 1)
    (hx : h * (κ₁ a * κ₂ b) * h⁻¹ = κ₁ a * κ₂ b) :
    h * κ₁ a * h⁻¹ = κ₁ a ∧ h * κ₂ b * h⁻¹ = κ₂ b := by
  obtain ⟨a₁, ha₁⟩ := hn₁ a
  obtain ⟨b₁, hb₁⟩ := hn₂ b
  have e : κ₁ a₁ * κ₂ b₁ = κ₁ a * κ₂ b := by
    rw [ha₁, hb₁, ← hx]
    group
  have e' : κ₁ (a⁻¹ * a₁) = κ₂ (b * b₁⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (κ₁ a)⁻¹ * κ₁ a₁ = (κ₁ a)⁻¹ * (κ₁ a₁ * κ₂ b₁) * (κ₂ b₁)⁻¹ := by group
      _ = κ₂ b * (κ₂ b₁)⁻¹ := by rw [e]; group
  have ha₁3 : a₁ ^ 3 = 1 := by
    apply hB.inj₁
    rw [map_pow, ha₁, conj_pow, ← map_pow, ha3, map_one, mul_one, mul_inv_cancel]
  have haa : a₁ = a := by
    rcases hB.eq_one_or_neg_of_eq e' with h1 | h1
    · calc a₁ = a * (a⁻¹ * a₁) := by group
        _ = a := by rw [h1, mul_one]
    · exfalso
      have e1 : a₁ = -1 * a := by
        calc a₁ = a * (a⁻¹ * a₁) := by group
          _ = a * -1 := by rw [h1]
          _ = -1 * a := (neg_one_mul_comm a).symm
      rw [e1, neg_one_mul_pow_three, ha3, mul_one] at ha₁3
      exact neg_one_ne_one_sl2 h2 ha₁3
  have hbb : κ₂ b₁ = κ₂ b := by
    rw [haa] at e
    exact mul_left_cancel e
  exact ⟨by rw [← ha₁, haa], by rw [← hb₁, hbb]⟩

end Blocks

section Conj

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {κ : SL(2, F) →* G}

theorem commute_of_fixed_of_moves {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (hinj : Function.Injective κ) {t : G} (ht : ∀ c, t * κ c * t⁻¹ ∈ κ.range)
    (ht' : ∀ c, t⁻¹ * κ c * t ∈ κ.range) (hmove : ∃ c, t * κ c * t⁻¹ ≠ κ c) {a a' : SL(2, F)}
    (ha : t * κ a * t⁻¹ = κ a) (ha' : t * κ a' * t⁻¹ = κ a') : a * a' = a' * a := by
  have hr := map_conj_range_eq κ ht ht'
  set α := inducedAut κ hinj t hr with hα
  have hfix : ∀ c, t * κ c * t⁻¹ = κ c → α c = c := fun c hc =>
    hinj (by rw [hα, apply_inducedAut, hc])
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hmove
    apply hc
    rw [← apply_inducedAut κ hinj t hr, ← hα, h1, MulAut.one_apply]
  exact commute_of_fix_of_ne_one hp hp5 hF hα1 (hfix a ha) (hfix a' ha')

theorem commute_of_mem_two (hF4 : 4 ≤ Nat.card F) (hinj : Function.Injective κ)
    {H Q : Subgroup G} (hκH : ∀ c, κ c ∈ H) (hQ2 : IsPGroup 2 Q)
    (hQH : H ≤ Subgroup.normalizer (Q : Set G)) {q : G} (hq : q ∈ Q)
    (hqn : ∀ c, q * κ c * q⁻¹ ∈ κ.range) (hqn' : ∀ c, q⁻¹ * κ c * q ∈ κ.range)
    (c : SL(2, F)) : q * κ c = κ c * q := by
  have hr := map_conj_range_eq κ hqn hqn'
  refine centralizes_of_sl2_normal hF4 κ hκH
    (fun B hB => Or.inl (hinj (hB.trans (map_one κ).symm))) hQ2 hQH hq (inducedAut κ hinj q hr)
    (fun B => apply_inducedAut κ hinj q hr B) c

theorem conj_commute_of_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (hinj : Function.Injective κ) {H Q T : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hHn : ∀ h ∈ H, ∀ c, h * κ c * h⁻¹ ∈ κ.range)
    (hTn : ∀ t ∈ T, ∀ c, t * κ c * t⁻¹ ∈ κ.range)
    (hHT : H ≤ Subgroup.centralizer (T : Set G)) {a : SL(2, F)}
    (haT : ∀ t ∈ T, t * κ a * t⁻¹ = κ a)
    (hcase : (∀ h ∈ H, h * κ a = κ a * h) ∨ (∃ t ∈ T, ∃ c, t * κ c * t⁻¹ ≠ κ c) ∨
      (∀ c, κ c ∈ H))
    {q : G} (hq : q ∈ Q) : ∃ a₁ : SL(2, F), q * κ a * q⁻¹ = κ a₁ ∧ a₁ * a = a * a₁ := by
  have hqH := hQH hq
  obtain ⟨a₁, ha₁⟩ := hHn q hqH a
  refine ⟨a₁, ha₁.symm, ?_⟩
  rcases hcase with hc | ⟨t, htT, hmove⟩ | hc
  · have : κ a₁ = κ a := by rw [ha₁, hc q hqH, mul_inv_cancel_right]
    rw [hinj this]
  · have hqt : q * t = t * q := (Subgroup.mem_centralizer_iff.mp (hHT hqH) t htT).symm
    have hfix : t * κ a₁ * t⁻¹ = κ a₁ := by
      have e : t * κ a₁ * t⁻¹ = q * (t * κ a * t⁻¹) * q⁻¹ := by
        rw [ha₁]
        have hqt' : t⁻¹ * q⁻¹ = q⁻¹ * t⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hqt]
        calc t * (q * κ a * q⁻¹) * t⁻¹ = (t * q) * κ a * (q⁻¹ * t⁻¹) := by group
          _ = (q * t) * κ a * (t⁻¹ * q⁻¹) := by rw [hqt, hqt']
          _ = q * (t * κ a * t⁻¹) * q⁻¹ := by group
      rw [e, haT t htT, ha₁]
    exact commute_of_fixed_of_moves hp hp5 hF hinj (hTn t htT)
      (fun c => by simpa using hTn t⁻¹ (T.inv_mem htT) c) hmove hfix (haT t htT)
  · have hF4 : 4 ≤ Nat.card F := by omega
    have h1 := commute_of_mem_two hF4 hinj hc hQ2 hHQ hq (hHn q hqH)
      (fun c => by simpa using hHn q⁻¹ (H.inv_mem hqH) c) a
    have : κ a₁ = κ a := by rw [ha₁, h1, mul_inv_cancel_right]
    rw [hinj this]

end Conj

section Combine

variable {G : Type} [Group G] {F : Type} [Field F] {κ₁ κ₂ : SL(2, F) →* G} {z : G}

theorem commute_of_parts (hB : BlockPair κ₁ κ₂ z) {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) {q x : G}
    (hq : q ∈ Q) (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) {a b a₁ b₁ : SL(2, F)}
    (hx : x = κ₁ a * κ₂ b) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha₁ : q * κ₁ a * q⁻¹ = κ₁ a₁) (hb₁ : q * κ₂ b * q⁻¹ = κ₂ b₁)
    (haa : a₁ * a = a * a₁) (hbb : b₁ * b = b * b₁) : q * x = x * q := by
  have hcQ : q * x * q⁻¹ * x⁻¹ ∈ Q := by
    have h1 : x * q⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ _).mp (Q.inv_mem hq)
    have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq h1
  have hc : q * x * q⁻¹ * x⁻¹ = κ₁ (a₁ * a⁻¹) * κ₂ (b₁ * b⁻¹) := by
    rw [hx, map_mul, map_mul, map_inv, map_inv, ← ha₁, ← hb₁]
    have hxinv : (κ₁ a * κ₂ b)⁻¹ = (κ₁ a)⁻¹ * (κ₂ b)⁻¹ := by rw [hB.comm a b, mul_inv_rev]
    have e2 : q * κ₂ b * q⁻¹ * (κ₁ a)⁻¹ = (κ₁ a)⁻¹ * (q * κ₂ b * q⁻¹) := by
      rw [hb₁]
      have := hB.comm a⁻¹ b₁
      rw [map_inv] at this
      exact this.symm
    calc q * (κ₁ a * κ₂ b) * q⁻¹ * (κ₁ a * κ₂ b)⁻¹ =
        (q * κ₁ a * q⁻¹) * ((q * κ₂ b * q⁻¹) * (κ₁ a)⁻¹) * (κ₂ b)⁻¹ := by rw [hxinv]; group
      _ = (q * κ₁ a * q⁻¹) * ((κ₁ a)⁻¹ * (q * κ₂ b * q⁻¹)) * (κ₂ b)⁻¹ := by rw [e2]
      _ = q * κ₁ a * q⁻¹ * (κ₁ a)⁻¹ * (q * κ₂ b * q⁻¹ * (κ₂ b)⁻¹) := by group
  have ha₁3 : κ₁ a₁ ^ 3 = 1 := by
    rw [← ha₁, conj_pow, ← map_pow, ha3, map_one, mul_one, mul_inv_cancel]
  have hb₁3 : κ₂ b₁ ^ 3 = 1 := by
    rw [← hb₁, conj_pow, ← map_pow, hb3, map_one, mul_one, mul_inv_cancel]
  have hu3 : κ₁ (a₁ * a⁻¹) ^ 3 = 1 := by
    have hc' : Commute (κ₁ a₁) (κ₁ a⁻¹) := by
      show κ₁ a₁ * κ₁ a⁻¹ = κ₁ a⁻¹ * κ₁ a₁
      rw [← map_mul, ← map_mul]
      congr 1
      calc a₁ * a⁻¹ = a⁻¹ * (a * a₁) * a⁻¹ := by group
        _ = a⁻¹ * (a₁ * a) * a⁻¹ := by rw [haa]
        _ = a⁻¹ * a₁ := by group
    rw [map_mul, hc'.mul_pow, ha₁3, ← map_pow, inv_pow, ha3, inv_one, map_one, one_mul]
  have hv3 : κ₂ (b₁ * b⁻¹) ^ 3 = 1 := by
    have hc' : Commute (κ₂ b₁) (κ₂ b⁻¹) := by
      show κ₂ b₁ * κ₂ b⁻¹ = κ₂ b⁻¹ * κ₂ b₁
      rw [← map_mul, ← map_mul]
      congr 1
      calc b₁ * b⁻¹ = b⁻¹ * (b * b₁) * b⁻¹ := by group
        _ = b⁻¹ * (b₁ * b) * b⁻¹ := by rw [hbb]
        _ = b⁻¹ * b₁ := by group
    rw [map_mul, hc'.mul_pow, hb₁3, ← map_pow, inv_pow, hb3, inv_one, map_one, one_mul]
  have h3 : (q * x * q⁻¹ * x⁻¹) ^ 3 = 1 := by
    rw [hc, (show Commute (κ₁ (a₁ * a⁻¹)) (κ₂ (b₁ * b⁻¹)) from
      hB.comm (a₁ * a⁻¹) (b₁ * b⁻¹)).mul_pow, hu3, hv3, one_mul]
  have h1 := eq_one_of_mem_two_of_cube hQ2 hcQ h3
  calc q * x = q * x * q⁻¹ * x⁻¹ * (x * q) := by group
    _ = x * q := by rw [h1, one_mul]

end Combine

end Item211Res5Proof

end CFSG.RankThree.PartTwo.Sec21
