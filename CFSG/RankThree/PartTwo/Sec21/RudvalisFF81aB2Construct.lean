module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aB2Elem

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.B2Construct

open CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem (Setup exists_of_mem_A exists_pow_eq_zpow)

variable {G : Type*} [Group G]

structure Hyp (A B₁ : Subgroup G) (b τ : G) : Prop where
  B₁A : B₁ ≤ A
  bA : b ∈ A
  B₁n : ∀ x ∈ A, ∀ y ∈ B₁, x * y * x⁻¹ ∈ B₁
  Aab : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ B₁
  A3 : ∀ x ∈ A, x ^ 3 ∈ B₁
  B₁3 : ∀ y ∈ B₁, y ^ 3 = 1
  b3 : b ^ 3 = 1
  bB₁ : b ∉ B₁
  τ2 : ∀ x ∈ A, τ * (τ * x * τ⁻¹) * τ⁻¹ = x
  τA : ∀ x ∈ A, τ * x * τ⁻¹ ∈ A
  τB₁ : ∀ y ∈ B₁, τ * y * τ⁻¹ = y⁻¹
  τb : τ * b * τ⁻¹ = b
  fix : ∀ x ∈ A, τ * x * τ⁻¹ * x⁻¹ ∈ B₁ → x ∈ Subgroup.zpowers b ⊔ B₁

namespace Hyp

variable {A B₁ : Subgroup G} {b τ : G} (h : Hyp A B₁ b τ)
include h

@[expose] def B₂ : Subgroup G where
  carrier := {x | x ∈ A ∧ τ * x * τ⁻¹ * x ∈ B₁}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {x y} hx hy => by
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have hk : (τ * y * τ⁻¹)⁻¹ * x⁻¹ * (τ * y * τ⁻¹) * x ∈ B₁ := by
      have := h.Aab _ (inv_mem (h.τA y hy.1)) _ (inv_mem hx.1)
      simpa only [inv_inv] using this
    have h3 := h.B₁n _ (inv_mem hy.1) _ hk
    have e : τ * (x * y) * τ⁻¹ * (x * y) =
        (τ * x * τ⁻¹ * x) * (τ * y * τ⁻¹ * y) *
          (y⁻¹ * ((τ * y * τ⁻¹)⁻¹ * x⁻¹ * (τ * y * τ⁻¹) * x) * y⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem hx.2 hy.2) h3
  inv_mem' := fun {x} hx => by
    refine ⟨inv_mem hx.1, ?_⟩
    have h1 := h.B₁n x hx.1 _ hx.2
    have e : τ * x⁻¹ * τ⁻¹ * x⁻¹ = (x * (τ * x * τ⁻¹ * x) * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

theorem mem_B₂ {x : G} : x ∈ h.B₂ ↔ x ∈ A ∧ τ * x * τ⁻¹ * x ∈ B₁ := Iff.rfl

theorem B₁_le : B₁ ≤ h.B₂ := fun y hy =>
  ⟨h.B₁A hy, by rw [h.τB₁ y hy, inv_mul_cancel]; exact one_mem _⟩

theorem le_A : h.B₂ ≤ A := fun _ hx => hx.1

theorem conj_conj {x : G} (hx : x ∈ A) : τ * (τ * x * τ⁻¹) * τ⁻¹ = x := h.τ2 x hx

theorem τ_mem {x : G} (hx : x ∈ h.B₂) : τ * x * τ⁻¹ ∈ h.B₂ := by
  refine ⟨h.τA x hx.1, ?_⟩
  rw [h.conj_conj hx.1]
  have e : x * (τ * x * τ⁻¹) = x * (τ * x * τ⁻¹ * x) * x⁻¹ := by group
  rw [e]
  exact h.B₁n x hx.1 _ hx.2

theorem fixed {x : G} (hx : x ∈ h.B₂) (hfx : τ * x * τ⁻¹ = x) : x = 1 := by
  have hxx : x * x ∈ B₁ := by
    have := hx.2
    rwa [hfx] at this
  have hxB₁ : x ∈ B₁ := by
    have := mul_mem (h.A3 x hx.1) (inv_mem hxx)
    rwa [show x ^ 3 * (x * x)⁻¹ = x by group] at this
  have hinv : x⁻¹ = x := (h.τB₁ x hxB₁).symm.trans hfx
  have hsq : x * x = 1 := by
    calc x * x = x⁻¹ * x := by rw [hinv]
      _ = 1 := inv_mul_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h.B₁3 x hxB₁, hsq, inv_one, one_mul]

theorem inv_comm [Finite G] : (∀ x ∈ h.B₂, τ * x * τ⁻¹ = x⁻¹) ∧
    ∀ x ∈ h.B₂, ∀ y ∈ h.B₂, x * y = y * x := by
  let φ : ↥h.B₂ →* ↥h.B₂ :=
    { toFun := fun x => ⟨τ * x * τ⁻¹, h.τ_mem x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfpf : MonoidHom.FixedPointFree φ := fun x hx =>
    Subtype.ext (h.fixed x.2 (congrArg Subtype.val hx))
  have hinvol : Function.Involutive φ := fun x => Subtype.ext (h.conj_conj x.2.1)
  have hφ := hfpf.coe_eq_inv_of_involutive hinvol
  refine ⟨fun x hx => congrArg Subtype.val (congrFun hφ ⟨x, hx⟩), fun x hx y hy => ?_⟩
  exact congrArg Subtype.val (hfpf.commute_all_of_involutive hinvol ⟨x, hx⟩ ⟨y, hy⟩).eq

theorem B₂3 {x : G} (hx : x ∈ h.B₂) : x ^ 3 ∈ B₁ := h.A3 x hx.1

theorem bB₂ {x : G} (hx : x ∈ h.B₂) : b * x * b⁻¹ * x⁻¹ ∈ B₁ := h.Aab b h.bA x hx.1

theorem conj_mem {g : G} (hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hgB₁ : ∀ y ∈ B₁, g * y * g⁻¹ ∈ B₁)
    (hgτ : ∀ x ∈ A, (g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹ * (τ * x * τ⁻¹)⁻¹ ∈ B₁) {x : G}
    (hx : x ∈ h.B₂) : g * x * g⁻¹ ∈ h.B₂ := by
  refine ⟨hgA x hx.1, ?_⟩
  have e : τ * (g * x * g⁻¹) * τ⁻¹ * (g * x * g⁻¹) =
      g * (((g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹ * (τ * x * τ⁻¹)⁻¹) * (τ * x * τ⁻¹ * x)) * g⁻¹ := by
    group
  rw [e]
  exact hgB₁ _ (mul_mem (hgτ x hx.1) hx.2)

theorem conj_mem_of_commute {g : G} (hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hgB₁ : ∀ y ∈ B₁, g * y * g⁻¹ ∈ B₁) (hgτ : g * τ = τ * g) {x : G} (hx : x ∈ h.B₂) :
    g * x * g⁻¹ ∈ h.B₂ := by
  refine h.conj_mem hgA hgB₁ (fun y _ => ?_) hx
  have e : g⁻¹ * τ * g = τ := by rw [mul_assoc, ← hgτ, inv_mul_cancel_left]
  rw [e, mul_inv_cancel]
  exact one_mem _

theorem mem_sup {x : G} (hx : x ∈ A) : x ∈ Subgroup.zpowers b ⊔ h.B₂ := by
  set y := τ * x * τ⁻¹ with hydef
  have hyA : y ∈ A := h.τA x hx
  have hτy : τ * y * τ⁻¹ = x := h.conj_conj hx
  have hu : y * x⁻¹ ∈ h.B₂ := by
    refine ⟨mul_mem hyA (inv_mem hx), ?_⟩
    have e : τ * (y * x⁻¹) * τ⁻¹ * (y * x⁻¹) = (τ * y * τ⁻¹) * (τ * x * τ⁻¹)⁻¹ * (y * x⁻¹) := by
      group
    rw [e, hτy, ← hydef, show x * y⁻¹ * (y * x⁻¹) = 1 by group]
    exact one_mem _
  have hv : (x * y)⁻¹ ∈ Subgroup.zpowers b ⊔ B₁ := by
    refine h.fix _ (inv_mem (mul_mem hx hyA)) ?_
    have e : τ * (x * y)⁻¹ * τ⁻¹ * (x * y)⁻¹⁻¹ =
        ((τ * x * τ⁻¹) * (τ * y * τ⁻¹))⁻¹ * (x * y) := by group
    rw [e, hτy, ← hydef]
    have := h.Aab _ (inv_mem hx) _ (inv_mem hyA)
    rwa [show x⁻¹ * y⁻¹ * x⁻¹⁻¹ * y⁻¹⁻¹ = (y * x)⁻¹ * (x * y) by group] at this
  have hw : (y * x⁻¹ * (x * y)⁻¹)⁻¹ * x ∈ B₁ := by
    have hk : y * x * y⁻¹ * x⁻¹ ∈ B₁ := h.Aab y hyA x hx
    have := mul_mem (h.B₁n x hx _ hk) (h.A3 x hx)
    rwa [show x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ * x ^ 3 = (y * x⁻¹ * (x * y)⁻¹)⁻¹ * x by group] at this
  have hvle : Subgroup.zpowers b ⊔ B₁ ≤ Subgroup.zpowers b ⊔ h.B₂ := sup_le_sup_left h.B₁_le _
  have hxe : x = (y * x⁻¹) * (x * y)⁻¹ * ((y * x⁻¹ * (x * y)⁻¹)⁻¹ * x) := by group
  rw [hxe]
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hu) (hvle hv))
    (Subgroup.mem_sup_right (h.B₁_le hw))

theorem sup_eq : Subgroup.zpowers b ⊔ h.B₂ = A :=
  le_antisymm (sup_le ((Subgroup.zpowers_le).2 h.bA) h.le_A) fun _ hx => h.mem_sup hx

theorem b_conj_mem {x : G} (hx : x ∈ h.B₂) : b * x * b⁻¹ ∈ h.B₂ := by
  refine h.conj_mem_of_commute (fun y hy => mul_mem (mul_mem h.bA hy) (inv_mem h.bA))
    (fun y hy => h.B₁n b h.bA y hy) ?_ hx
  have := h.τb
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem pow_not_mem {n : ℕ} (hn0 : 0 < n) (hn3 : n < 3) : b ^ n ∉ h.B₂ := by
  intro hmem
  have h2 : b ^ n * b ^ n ∈ B₁ := by
    have := hmem.2
    rwa [show τ * b ^ n * τ⁻¹ = (τ * b * τ⁻¹) ^ n by rw [conj_pow], h.τb] at this
  apply h.bB₁
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
  · have := mul_mem h2 h2
    rwa [show b ^ 1 * b ^ 1 * (b ^ 1 * b ^ 1) = b * b ^ 3 by group, h.b3, mul_one] at this
  · rwa [show b ^ 2 * b ^ 2 = b * b ^ 3 by group, h.b3, mul_one] at h2

theorem mem_B₁_of_mem_sup [Finite G] {x : G} (hx : x ∈ Subgroup.zpowers b ⊔ B₁) (hx2 : x ∈ h.B₂) :
    x ∈ B₁ := by
  obtain ⟨n, hn, y, hy, rfl⟩ := exists_of_mem_A h.b3 (fun z hz => h.B₁n b h.bA z hz) hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rwa [pow_zero, one_mul]
  · exfalso
    have hbn : b ^ n ∈ h.B₂ := by
      have := mul_mem hx2 (inv_mem (h.B₁_le hy))
      rwa [mul_inv_cancel_right] at this
    exact h.pow_not_mem hpos hn hbn

theorem card_A [Finite G] : Nat.card A = 3 * Nat.card h.B₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := fun e => h.bB₁ (e ▸ one_mem _)
  have hord : orderOf b = 3 := orderOf_eq_prime h.b3 hb1
  have hinf : ∀ u ∈ Subgroup.zpowers b, u ∈ h.B₂ → u = 1 := by
    intro u hu huB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, hn, hbn⟩ := exists_pow_eq_zpow h.b3 k
    rw [hbn] at huB ⊢
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact pow_zero b
    · exact absurd huB (h.pow_not_mem hpos hn)
  let ψ : ↥(Subgroup.zpowers b) × ↥h.B₂ → ↥A := fun p =>
    ⟨p.1 * p.2, mul_mem ((Subgroup.zpowers_le).2 h.bA p.1.2) (h.le_A p.2.2)⟩
  have hinj : Function.Injective ψ := by
    rintro ⟨u, x⟩ ⟨u', x'⟩ e
    have e' : (u : G) * x = u' * x' := congrArg Subtype.val e
    have h1 : (u' : G)⁻¹ * u = x' * (x : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e', mul_inv_cancel_right]
    have hm : (u' : G)⁻¹ * u = 1 :=
      hinf _ (mul_mem (inv_mem u'.2) u.2) (h1 ▸ mul_mem x'.2 (inv_mem x.2))
    have huu : (u : G) = u' := by
      rw [inv_mul_eq_one] at hm
      exact hm.symm
    have hxx : (x : G) = x' := by
      rw [huu] at e'
      exact mul_left_cancel e'
    exact Prod.ext (Subtype.ext huu) (Subtype.ext hxx)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Subgroup.zpowers b ⊔ h.B₂ := h.mem_sup hy
    obtain ⟨n, -, x, hx, rfl⟩ := exists_of_mem_A h.b3 (fun z hz => h.b_conj_mem hz) hy'
    exact ⟨(⟨b ^ n, Subgroup.npow_mem_zpowers b n⟩, ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zpowers,
    hord]

theorem toSetup [Finite G] {b₁ b₂ b₃ c : G} (hB₁ : B₁ = Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hBab : ∀ x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G),
      ∀ y ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G), x * y = y * x)
    (hB3 : ∀ x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G), x ^ 3 = 1)
    (hBcard : Nat.card (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) = 81)
    (hB₁card : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27)
    (hAN : A ≤ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))
    (hcN : c ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))
    (hcb : c * b * c⁻¹ = b) (hc₁ : c * b₁ * c⁻¹ = b₂) (hc₂ : c * b₂ * c⁻¹ = b₃)
    (hc₃ : c * b₃ * c⁻¹ = b₁) (hcB₂ : ∀ x ∈ h.B₂, c * x * c⁻¹ ∈ h.B₂)
    (hc3 : c ^ 3 ∈ Subgroup.zpowers b ⊔ h.B₂)
    (hPmax : ∀ R : Subgroup G,
      R ≤ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) →
      IsPGroup 3 R → Subgroup.zpowers b ⊔ h.B₂ ⊔ Subgroup.zpowers c ≤ R →
      R = Subgroup.zpowers b ⊔ h.B₂ ⊔ Subgroup.zpowers c) :
    Setup b b₁ b₂ b₃ c h.B₂ := by
  subst hB₁
  exact
    { Bab := hBab
      B3 := hB3
      Bcard := hBcard
      B₁card := hB₁card
      B₁B₂ := h.B₁_le
      B₂ab := h.inv_comm.2
      B₂3 := fun x hx => h.B₂3 hx
      B₂N := h.le_A.trans hAN
      bB₂ := fun x hx => h.bB₂ hx
      cN := hcN
      cb := hcb
      c₁ := hc₁
      c₂ := hc₂
      c₃ := hc₃
      cB₂ := hcB₂
      c3 := hc3
      Pmax := hPmax }

end Hyp

end CFSG.RankThree.PartTwo.Sec21.FF81.B2Construct
