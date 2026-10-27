module

public import CFSG.Quasithin.EmptyFaithful.S153E58D
public import CFSG.Quasithin.EmptyFaithful.S153E57A

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

section Proj

variable {W : Type} [CommGroup W]

theorem exists_proj {W₁ W₂ : Subgroup W} (h : IsIntDirect W₁ W₂ ⊤) :
    ∃ p : W →* ↥W₁, ∀ (x : ↥W₁) (w : W), (x : W)⁻¹ * w ∈ W₂ ↔ p w = x := by
  have hexu : ∀ w : W, ∃! x : ↥W₁, (x : W)⁻¹ * w ∈ W₂ := by
    intro w
    have hw : w ∈ W₁ ⊔ W₂ := h.1 ▸ Subgroup.mem_top w
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
    refine ⟨⟨x, hx⟩, by simpa using hy, fun x' hx' => ?_⟩
    have h1 : (x' : W)⁻¹ * (x * y) ∈ W₂ := hx'
    have h2 : ((x' : W)⁻¹ * x) ∈ W₂ := by
      have := W₂.mul_mem h1 (W₂.inv_mem hy)
      simpa [mul_assoc] using this
    have h3 : ((x' : W)⁻¹ * x) ∈ W₁ ⊓ W₂ := ⟨W₁.mul_mem (W₁.inv_mem x'.2) hx, h2⟩
    rw [h.2, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  choose p hp huniq using hexu
  have hiff : ∀ (x : ↥W₁) (w : W), (x : W)⁻¹ * w ∈ W₂ ↔ p w = x := fun x w =>
    ⟨fun hx => (huniq w x hx).symm, fun hx => hx ▸ hp w⟩
  refine ⟨{ toFun := p, map_one' := ?_, map_mul' := ?_ }, hiff⟩
  · have := (hiff 1 1).1 (by simp)
    exact this.symm ▸ rfl
  · intro w w'
    apply (hiff _ _).1
    have e : ((p w * p w' : ↥W₁) : W)⁻¹ * (w * w') = ((p w : W)⁻¹ * w) * ((p w' : W)⁻¹ * w') := by
      rw [Subgroup.coe_mul, mul_inv, mul_mul_mul_comm]
    rw [e]
    exact W₂.mul_mem (hp w) (hp w')

theorem proj_equivariant {W₁ W₂ : Subgroup W} {p : W →* ↥W₁}
    (hp : ∀ (x : ↥W₁) (w : W), (x : W)⁻¹ * w ∈ W₂ ↔ p w = x) {k : MulAut W}
    (hk₁ : ∀ u ∈ W₁, k u ∈ W₁) (hk₂ : ∀ u ∈ W₂, k u ∈ W₂) (w : W) :
    ((p (k w) : ↥W₁) : W) = k (p w) := by
  have h1 : (p w : W)⁻¹ * w ∈ W₂ := (hp (p w) w).2 rfl
  have h2 : ((⟨k (p w), hk₁ _ (p w).2⟩ : ↥W₁) : W)⁻¹ * k w ∈ W₂ := by
    have := hk₂ _ h1
    simpa [map_mul, map_inv] using this
  have := (hp ⟨k (p w), hk₁ _ (p w).2⟩ (k w)).1 h2
  exact congrArg Subtype.val this

end Proj

section Setup

variable {W : Type} [CommGroup W]

structure Setup58 (H K : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (bil : W → W → ZMod 2) : Prop where
  KH : K ≤ H
  Kn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  K1 : K ≠ ⊥
  dir : IsIntDirect W₁ W₂ ⊤
  irr₁ : IsIrrOn153 K W₁
  irr₂ : IsIrrOn153 K W₂
  Hirr : IsIrrOn153 H ⊤
  card₁ : Nat.card ↥W₁ = 8
  card₂ : Nat.card ↥W₂ = 8
  bil_left : ∀ a b c, bil (a * b) c = bil a c + bil b c
  bil_right : ∀ a b c, bil a (b * c) = bil a b + bil a c
  bil_symm : ∀ a b, bil a b = bil b a
  bil_nondeg : ∀ a, (∀ b, bil a b = 0) → a = 1
  bil_inv : ∀ h ∈ H, ∀ a b, bil (h a) (h b) = bil a b

variable {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {bil : W → W → ZMod 2}

theorem Setup58.bil_one_right (hS : Setup58 H K W₁ W₂ bil) (a : W) : bil a 1 = 0 := by
  have := hS.bil_right a 1 1
  rw [mul_one] at this
  have h2 : bil a 1 + bil a 1 = bil a 1 + 0 := by rw [← this, add_zero]
  exact add_left_cancel h2

theorem Setup58.bil_inv_right (hS : Setup58 H K W₁ W₂ bil) (a c : W) : bil a c⁻¹ = bil a c := by
  have := hS.bil_right a c c⁻¹
  rw [mul_inv_cancel, hS.bil_one_right] at this
  have key : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  exact key _ _ this

theorem Setup58.bil_inv_K (hS : Setup58 H K W₁ W₂ bil) {k : MulAut W} (hk : k ∈ K) (a b : W) :
    bil (k a) (k b) = bil a b := hS.bil_inv k (hS.KH hk) a b

theorem Setup58.inv₁ (hS : Setup58 H K W₁ W₂ bil) : ∀ k ∈ K, ∀ u ∈ W₁, k u ∈ W₁ := hS.irr₁.2.1

theorem Setup58.inv₂ (hS : Setup58 H K W₁ W₂ bil) : ∀ k ∈ K, ∀ u ∈ W₂, k u ∈ W₂ := hS.irr₂.2.1

theorem Setup58.W₁_ne_bot (hS : Setup58 H K W₁ W₂ bil) : W₁ ≠ ⊥ := by
  intro h
  have := hS.card₁
  rw [h, Subgroup.card_bot] at this
  omega

theorem Setup58.bil_zero_W₁ (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e) :
    ∀ a ∈ W₁, ∀ b ∈ W₁, bil a b = 0 :=
  form_zero_of_transv hT hS.inv₁ bil hS.bil_right fun _ hk a _ b _ => hS.bil_inv_K hk a b

theorem Setup58.eq_one_of_orth (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e) :
    ∀ y ∈ W₂, (∀ x ∈ W₁, bil x y = 0) → y = 1 := by
  have h0 := hS.bil_zero_W₁ hT
  let R : Subgroup W :=
    { carrier := {y | y ∈ W₂ ∧ ∀ x ∈ W₁, bil x y = 0}
      one_mem' := ⟨W₂.one_mem, fun x _ => hS.bil_one_right x⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨W₂.mul_mem ha hb, fun x hx => by rw [hS.bil_right, ha' x hx, hb' x hx, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨W₂.inv_mem ha, fun x hx => by rw [hS.bil_inv_right, ha' x hx]⟩ }
  have hRle : R ≤ W₂ := fun y hy => hy.1
  have hRinv : ∀ k ∈ K, ∀ y ∈ R, k y ∈ R := by
    rintro k hk y ⟨hy, hy'⟩
    refine ⟨hS.inv₂ k hk y hy, fun x hx => ?_⟩
    have hk' : k⁻¹ ∈ K := K.inv_mem hk
    have h1 := hS.bil_inv_K hk (k⁻¹ x) y
    have h2 : k (k⁻¹ x) = x := by simp
    rw [h2] at h1
    rw [h1]
    exact hy' _ (hS.inv₁ k⁻¹ hk' x hx)
  rcases hS.irr₂.2.2 R hRle hRinv with hR | hR
  · intro y hy hy'
    have : y ∈ R := ⟨hy, hy'⟩
    rw [hR, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hS.W₁_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply hS.bil_nondeg
    intro b
    have hb : b ∈ W₁ ⊔ W₂ := hS.dir.1 ▸ Subgroup.mem_top b
    obtain ⟨x', hx', y', hy', rfl⟩ := Subgroup.mem_sup.1 hb
    have hy'R : y' ∈ R := hR ▸ hy'
    rw [hS.bil_right, h0 x hx x' hx', hy'R.2 x hx, add_zero]

end Setup

end S153E58

end CFSG.Quasithin
