module

public import Mathlib.GroupTheory.PGroup

public section

universe u

namespace CFSG.Sporadic.Recognition.JankoWong

namespace KleinOrder

section Defs

variable {G : Type*} [Group G]

@[expose] def fixedSub (σ : G →* G) : Subgroup G := σ.eqLocus (MonoidHom.id G)

theorem mem_fixedSub {σ : G →* G} {g : G} : g ∈ fixedSub σ ↔ σ g = g := Iff.rfl

@[expose] def resEnd (σ : G →* G) (N : Subgroup G) (hN : N ≤ N.comap σ) : N →* N :=
  (σ.comp N.subtype).codRestrict N fun n => hN n.2

@[simp] theorem coe_resEnd {σ : G →* G} {N : Subgroup G} {hN : N ≤ N.comap σ} (n : N) :
    ((resEnd σ N hN n : N) : G) = σ n := rfl

theorem involutive_of_prod {σ₁ σ₂ σ₃ : G →* G} (h₁ : ∀ g, σ₁ (σ₁ g) = g)
    (h₂ : ∀ g, σ₂ (σ₂ g) = g) (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g))
    (h₃ : ∀ g, σ₃ g = σ₁ (σ₂ g)) : ∀ g, σ₃ (σ₃ g) = g := by
  intro g
  rw [h₃ (σ₃ g), h₃ g, ← hc (σ₂ g), h₂, h₁]

theorem eq_one_of_eq_inv (hodd : Odd (Nat.card G)) {g : G} (h : g = g⁻¹) : g = 1 := by
  have hsq : g ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h2 : orderOf g ∣ Nat.card G := orderOf_dvd_natCard g
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)

end Defs

section Abelian

variable {B : Type*} [CommGroup B]

def normHom (σ : B →* B) (hσ : ∀ b, σ (σ b) = b) : B →* fixedSub σ where
  toFun z := ⟨z * σ z, by
    show σ (z * σ z) = z * σ z
    rw [map_mul, hσ, mul_comm]⟩
  map_one' := by
    apply Subtype.ext
    show 1 * σ 1 = 1
    rw [map_one, mul_one]
  map_mul' z w := by
    apply Subtype.ext
    show z * w * σ (z * w) = z * σ z * (w * σ w)
    rw [map_mul]
    exact mul_mul_mul_comm z w (σ z) (σ w)

theorem map_eq_inv_of_fixed {σ τ : B →* B} (hσ : ∀ b, σ (σ b) = b)
    (hc : ∀ b, σ (τ b) = τ (σ b)) (hfix : ∀ b, σ b = b → τ b = b → b = 1) {z : B}
    (hz : τ z = z) : σ z = z⁻¹ := by
  have hw : z * σ z = 1 := by
    apply hfix
    · rw [map_mul, hσ, mul_comm]
    · rw [map_mul, ← hc, hz]
  exact eq_inv_of_mul_eq_one_right hw

theorem map_eq_inv_of_prod_fixed {σ₁ σ₂ σ₃ : B →* B} (h₁ : ∀ b, σ₁ (σ₁ b) = b)
    (hc : ∀ b, σ₁ (σ₂ b) = σ₂ (σ₁ b)) (h₃ : ∀ b, σ₃ b = σ₁ (σ₂ b))
    (hfix : ∀ b, σ₁ b = b → σ₂ b = b → b = 1) {c : B} (hc₃ : σ₃ c = c) :
    σ₁ c = c⁻¹ ∧ σ₂ c = c⁻¹ := by
  have e : σ₂ c = σ₁ c := by
    have h : σ₁ (σ₂ c) = c := by rw [← h₃]; exact hc₃
    have h' := congrArg σ₁ h
    rwa [h₁] at h'
  have hw : c * σ₁ c = 1 := by
    apply hfix
    · rw [map_mul, h₁, mul_comm]
    · rw [map_mul, ← hc, e, h₁, mul_comm]
  have hi : σ₁ c = c⁻¹ := eq_inv_of_mul_eq_one_right hw
  exact ⟨hi, e.trans hi⟩

theorem card_eq_prod_fixedSub_of_commGroup [Finite B] (hodd : Odd (Nat.card B))
    {σ₁ σ₂ σ₃ : B →* B} (h₁ : ∀ b, σ₁ (σ₁ b) = b) (h₂ : ∀ b, σ₂ (σ₂ b) = b)
    (hc : ∀ b, σ₁ (σ₂ b) = σ₂ (σ₁ b)) (h₃ : ∀ b, σ₃ b = σ₁ (σ₂ b))
    (hfix : ∀ b, σ₁ b = b → σ₂ b = b → b = 1) :
    Nat.card B = Nat.card (fixedSub σ₁) * Nat.card (fixedSub σ₂) * Nat.card (fixedSub σ₃) := by
  have hσ₃ := involutive_of_prod h₁ h₂ hc h₃
  let ψ : B →* fixedSub σ₁ × fixedSub σ₂ × fixedSub σ₃ :=
    (normHom σ₁ h₁).prod ((normHom σ₂ h₂).prod (normHom σ₃ hσ₃))
  let ρ : fixedSub σ₁ × fixedSub σ₂ × fixedSub σ₃ →* B :=
    (fixedSub σ₁).subtype.coprod ((fixedSub σ₂).subtype.coprod (fixedSub σ₃).subtype)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have e1 : z * σ₁ z = 1 := congrArg (fun x => (x.1 : B)) hz
    have e2 : z * σ₂ z = 1 := congrArg (fun x => (x.2.1 : B)) hz
    have e3 : z * σ₃ z = 1 := congrArg (fun x => (x.2.2 : B)) hz
    have i1 : σ₁ z = z⁻¹ := eq_inv_of_mul_eq_one_right e1
    have i2 : σ₂ z = z⁻¹ := eq_inv_of_mul_eq_one_right e2
    have i3 : σ₃ z = z⁻¹ := eq_inv_of_mul_eq_one_right e3
    have h4 : σ₃ z = z := by rw [h₃, i2, map_inv, i1, inv_inv]
    exact eq_one_of_eq_inv hodd (h4.symm.trans i3)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩⟩ h
    have h' : a * (b * c) = 1 := h
    have ha' : σ₁ a = a := ha
    have hb' : σ₂ b = b := hb
    have hc'' : σ₃ c = c := hc'
    have hb₁ : σ₁ b = b⁻¹ := map_eq_inv_of_fixed h₁ hc hfix hb'
    obtain ⟨hc₁, hc₂⟩ := map_eq_inv_of_prod_fixed h₁ hc h₃ hfix hc''
    have h'' : a * (b⁻¹ * c⁻¹) = 1 := by
      have := congrArg σ₁ h'
      rwa [map_mul, map_mul, ha', hb₁, hc₁, map_one] at this
    rw [← mul_inv, mul_inv_eq_one] at h''
    have h4 : a = (b * c)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hbc : b * c = 1 := eq_one_of_eq_inv hodd (h''.symm.trans h4)
    have ha1 : a = 1 := by rw [h'', hbc]
    have hbc₂ : b * c⁻¹ = 1 := by
      have := congrArg σ₂ hbc
      rwa [map_mul, hb', hc₂, map_one] at this
    have hbc₃ : b = c := mul_inv_eq_one.mp hbc₂
    have hb1 : b = 1 := by
      subst hbc₃
      exact eq_one_of_eq_inv hodd (mul_eq_one_iff_eq_inv.mp hbc)
    have hc1 : c = 1 := by rw [← hbc₃, hb1]
    subst ha1 hb1 hc1
    rfl
  have h1 : Nat.card B ≤ Nat.card (fixedSub σ₁ × fixedSub σ₂ × fixedSub σ₃) :=
    Nat.card_le_card_of_injective ψ hψ
  have h2 : Nat.card (fixedSub σ₁ × fixedSub σ₂ × fixedSub σ₃) ≤ Nat.card B :=
    Nat.card_le_card_of_injective ρ hρ
  rw [le_antisymm h1 h2, Nat.card_prod, Nat.card_prod, mul_assoc]

end Abelian

section Quotient

variable {G : Type*} [Group G]

theorem fixed_mul_pow {N : Subgroup G} {σ : G →* G} (hσ : ∀ g, σ (σ g) = g) {k : ℕ}
    (hk : Nat.card N = 2 * k + 1) {g : G} (hg : g⁻¹ * σ g ∈ N) :
    σ (g * (g⁻¹ * σ g) ^ (k + 1)) = g * (g⁻¹ * σ g) ^ (k + 1) := by
  have hnN : (g⁻¹ * σ g) ^ (2 * k + 1) = 1 := by
    have h := pow_card_eq_one' (G := N) (x := ⟨g⁻¹ * σ g, hg⟩)
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have hσn : σ (g⁻¹ * σ g) = (g⁻¹ * σ g)⁻¹ := by
    rw [map_mul, map_inv, hσ, mul_inv_rev, inv_inv]
  have hσg : σ g = g * (g⁻¹ * σ g) := by group
  generalize g⁻¹ * σ g = n at hnN hσn hσg ⊢
  have key : n ^ (k + 1) * n ^ (k + 1) = n := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by omega, pow_succ, hnN, one_mul]
  rw [map_mul, map_pow, hσn, hσg, inv_pow, mul_assoc]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  exact key.symm

theorem exists_fixed_lift {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N)) {σ : G →* G}
    (hσ : ∀ g, σ (σ g) = g) (hN : N ≤ N.comap σ) {x : G ⧸ N}
    (hx : QuotientGroup.map N N σ hN x = x) : ∃ g : G, σ g = g ∧ (g : G ⧸ N) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hodd
  have hg : g⁻¹ * σ g ∈ N := by
    rw [QuotientGroup.map_mk] at hx
    exact QuotientGroup.eq.mp hx.symm
  refine ⟨g * (g⁻¹ * σ g) ^ (k + 1), fixed_mul_pow hσ hk hg, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (N.pow_mem hg _), mul_one]

theorem quotient_fixed_eq_one {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    {σ₁ σ₂ : G →* G} (h₁ : ∀ g, σ₁ (σ₁ g) = g) (h₂ : ∀ g, σ₂ (σ₂ g) = g)
    (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g)) (hfix : ∀ g, σ₁ g = g → σ₂ g = g → g ∈ N)
    (hN₁ : N ≤ N.comap σ₁) (hN₂ : N ≤ N.comap σ₂) {x : G ⧸ N}
    (hx₁ : QuotientGroup.map N N σ₁ hN₁ x = x) (hx₂ : QuotientGroup.map N N σ₂ hN₂ x = x) :
    x = 1 := by
  obtain ⟨g, hg₁, rfl⟩ := exists_fixed_lift hodd h₁ hN₁ hx₁
  obtain ⟨k, hk⟩ := hodd
  have hn : g⁻¹ * σ₂ g ∈ N := by
    rw [QuotientGroup.map_mk] at hx₂
    exact QuotientGroup.eq.mp hx₂.symm
  have hn₁ : σ₁ (g⁻¹ * σ₂ g) = g⁻¹ * σ₂ g := by
    rw [map_mul, map_inv, hg₁, hc, hg₁]
  have hg'₂ := fixed_mul_pow h₂ hk hn
  have hg'₁ : σ₁ (g * (g⁻¹ * σ₂ g) ^ (k + 1)) = g * (g⁻¹ * σ₂ g) ^ (k + 1) := by
    rw [map_mul, map_pow, hg₁, hn₁]
  have hmem := hfix _ hg'₁ hg'₂
  have hg : g ∈ N := by
    have := N.mul_mem hmem (N.inv_mem (N.pow_mem hn (k + 1)))
    simpa using this
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem card_fixedSub_eq_mul {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    {σ : G →* G} (hσ : ∀ g, σ (σ g) = g) (hN : N ≤ N.comap σ) :
    Nat.card (fixedSub σ) =
      Nat.card (fixedSub (resEnd σ N hN)) * Nat.card (fixedSub (QuotientGroup.map N N σ hN)) := by
  let φ : fixedSub σ →* G ⧸ N := (QuotientGroup.mk' N).comp (fixedSub σ).subtype
  have hrange : φ.range = fixedSub (QuotientGroup.map N N σ hN) := by
    ext x
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      show QuotientGroup.map N N σ hN (g : G ⧸ N) = (g : G ⧸ N)
      rw [QuotientGroup.map_mk, show σ g = g from hg]
    · intro hx
      obtain ⟨g, hg, rfl⟩ := exists_fixed_lift hodd hσ hN hx
      exact ⟨⟨g, hg⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card (fixedSub (resEnd σ N hN)) := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨⟨g.1.1, (QuotientGroup.eq_one_iff _).mp g.2⟩, Subtype.ext g.1.2⟩
        invFun := fun n =>
          ⟨⟨n.1.1, congrArg Subtype.val n.2⟩, (QuotientGroup.eq_one_iff _).mpr n.1.2⟩
        left_inv := fun g => rfl
        right_inv := fun n => rfl }
  rw [← Subgroup.card_ker_mul_card_range φ, hker, hrange]

theorem quotient_klein {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    {σ₁ σ₂ σ₃ : G →* G} (h₁ : ∀ g, σ₁ (σ₁ g) = g) (h₂ : ∀ g, σ₂ (σ₂ g) = g)
    (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g)) (h₃ : ∀ g, σ₃ g = σ₁ (σ₂ g))
    (hfix : ∀ g, σ₁ g = g → σ₂ g = g → g ∈ N)
    (hN₁ : N ≤ N.comap σ₁) (hN₂ : N ≤ N.comap σ₂) (hN₃ : N ≤ N.comap σ₃) :
    (∀ x, QuotientGroup.map N N σ₁ hN₁ (QuotientGroup.map N N σ₁ hN₁ x) = x) ∧
    (∀ x, QuotientGroup.map N N σ₂ hN₂ (QuotientGroup.map N N σ₂ hN₂ x) = x) ∧
    (∀ x, QuotientGroup.map N N σ₁ hN₁ (QuotientGroup.map N N σ₂ hN₂ x) =
      QuotientGroup.map N N σ₂ hN₂ (QuotientGroup.map N N σ₁ hN₁ x)) ∧
    (∀ x, QuotientGroup.map N N σ₃ hN₃ x =
      QuotientGroup.map N N σ₁ hN₁ (QuotientGroup.map N N σ₂ hN₂ x)) ∧
    (∀ x, QuotientGroup.map N N σ₁ hN₁ x = x → QuotientGroup.map N N σ₂ hN₂ x = x → x = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [QuotientGroup.map_mk, h₁]
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [QuotientGroup.map_mk, h₂]
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [QuotientGroup.map_mk, hc]
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [QuotientGroup.map_mk, h₃]
  · intro x hx₁ hx₂
    exact quotient_fixed_eq_one hodd h₁ h₂ hc hfix hN₁ hN₂ hx₁ hx₂

theorem card_mul_eq_of_quotient {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    {σ₁ σ₂ σ₃ : G →* G} (h₁ : ∀ g, σ₁ (σ₁ g) = g) (h₂ : ∀ g, σ₂ (σ₂ g) = g)
    (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g)) (h₃ : ∀ g, σ₃ g = σ₁ (σ₂ g))
    (hN₁ : N ≤ N.comap σ₁) (hN₂ : N ≤ N.comap σ₂) (hN₃ : N ≤ N.comap σ₃)
    (hT : Nat.card (G ⧸ N) = Nat.card (fixedSub (QuotientGroup.map N N σ₁ hN₁)) *
      Nat.card (fixedSub (QuotientGroup.map N N σ₂ hN₂)) *
      Nat.card (fixedSub (QuotientGroup.map N N σ₃ hN₃))) :
    Nat.card G * (Nat.card (fixedSub (resEnd σ₁ N hN₁)) * Nat.card (fixedSub (resEnd σ₂ N hN₂)) *
      Nat.card (fixedSub (resEnd σ₃ N hN₃))) =
      Nat.card N * (Nat.card (fixedSub σ₁) * Nat.card (fixedSub σ₂) * Nat.card (fixedSub σ₃)) := by
  have hσ₃ := involutive_of_prod h₁ h₂ hc h₃
  rw [card_fixedSub_eq_mul hodd h₁ hN₁, card_fixedSub_eq_mul hodd h₂ hN₂,
    card_fixedSub_eq_mul hodd hσ₃ hN₃, Subgroup.card_eq_card_quotient_mul_card_subgroup N, hT]
  ring

end Quotient

section Induction

open scoped IsMulCommutative

theorem card_eq_prod_fixedSub_of_isPGroup {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G = n → IsPGroup p G →
      ∀ (σ₁ σ₂ σ₃ : G →* G), (∀ g, σ₁ (σ₁ g) = g) → (∀ g, σ₂ (σ₂ g) = g) →
        (∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g)) → (∀ g, σ₃ g = σ₁ (σ₂ g)) →
        (∀ g, σ₁ g = g → σ₂ g = g → g = 1) →
        Nat.card G = Nat.card (fixedSub σ₁) * Nat.card (fixedSub σ₂) *
          Nat.card (fixedSub σ₃) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hG σ₁ σ₂ σ₃ h₁ h₂ hc h₃ hfix
  rcases subsingleton_or_nontrivial G with hsub | hnt
  · have h1 : ∀ σ : G →* G, Nat.card (fixedSub σ) = 1 := fun σ =>
      Nat.card_of_subsingleton (1 : fixedSub σ)
    rw [Nat.card_of_subsingleton (1 : G), h1, h1, h1]
  · have hodd_p : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
    have : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    have hZodd : Odd (Nat.card (Subgroup.center G)) := by
      obtain ⟨m, hm⟩ := (hG.to_subgroup (Subgroup.center G)).exists_card_eq
      rw [hm]
      exact hodd_p.pow
    have hinv : ∀ σ : G →* G, (∀ g, σ (σ g) = g) →
        Subgroup.center G ≤ (Subgroup.center G).comap σ := by
      intro σ hσ z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro g
      have hz' := Subgroup.mem_center_iff.mp hz (σ g)
      calc g * σ z = σ (σ g) * σ z := by rw [hσ]
        _ = σ (σ g * z) := (map_mul σ _ _).symm
        _ = σ (z * σ g) := by rw [hz']
        _ = σ z * σ (σ g) := map_mul σ _ _
        _ = σ z * g := by rw [hσ]
    have hσ₃ := involutive_of_prod h₁ h₂ hc h₃
    have hZ₁ := hinv σ₁ h₁
    have hZ₂ := hinv σ₂ h₂
    have hZ₃ := hinv σ₃ hσ₃
    obtain ⟨q₁, q₂, qc, q₃, qf⟩ := quotient_klein hZodd h₁ h₂ hc h₃
      (fun g hg₁ hg₂ => by rw [hfix g hg₁ hg₂]; exact one_mem _) hZ₁ hZ₂ hZ₃
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    have hpos : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
    have hZ1 : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
    have hlt : Nat.card (G ⧸ Subgroup.center G) < n := by
      rw [← hn, hlag]
      exact lt_mul_of_one_lt_right hpos hZ1
    have hT := ih _ hlt (G ⧸ Subgroup.center G) rfl (hG.to_quotient _) _ _ _ q₁ q₂ qc q₃
      (fun x hx₁ hx₂ => qf x hx₁ hx₂)
    have hR := card_mul_eq_of_quotient hZodd h₁ h₂ hc h₃ hZ₁ hZ₂ hZ₃ hT
    have hA := card_eq_prod_fixedSub_of_commGroup (B := Subgroup.center G) hZodd
      (σ₁ := resEnd σ₁ _ hZ₁) (σ₂ := resEnd σ₂ _ hZ₂) (σ₃ := resEnd σ₃ _ hZ₃)
      (fun b => Subtype.ext (h₁ b)) (fun b => Subtype.ext (h₂ b)) (fun b => Subtype.ext (hc b))
      (fun b => Subtype.ext (h₃ b))
      (fun b hb₁ hb₂ => Subtype.ext (hfix b (congrArg Subtype.val hb₁)
        (congrArg Subtype.val hb₂)))
    rw [← hA] at hR
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [mul_comm]; exact hR)

theorem card_eq_prod_fixedSub {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {G : Type u} [Group G]
    [Finite G] (hG : IsPGroup p G) {σ₁ σ₂ σ₃ : G →* G} (h₁ : ∀ g, σ₁ (σ₁ g) = g)
    (h₂ : ∀ g, σ₂ (σ₂ g) = g) (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g))
    (h₃ : ∀ g, σ₃ g = σ₁ (σ₂ g)) (hfix : ∀ g, σ₁ g = g → σ₂ g = g → g = 1) :
    Nat.card G = Nat.card (fixedSub σ₁) * Nat.card (fixedSub σ₂) * Nat.card (fixedSub σ₃) :=
  card_eq_prod_fixedSub_of_isPGroup hp _ G rfl hG σ₁ σ₂ σ₃ h₁ h₂ hc h₃ hfix

theorem card_mul_sq_eq_prod_fixedSub {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {G : Type u} [Group G]
    [Finite G] (hG : IsPGroup p G) {N : Subgroup G} [N.Normal] {σ₁ σ₂ σ₃ : G →* G}
    (h₁ : ∀ g, σ₁ (σ₁ g) = g) (h₂ : ∀ g, σ₂ (σ₂ g) = g) (hc : ∀ g, σ₁ (σ₂ g) = σ₂ (σ₁ g))
    (h₃ : ∀ g, σ₃ g = σ₁ (σ₂ g)) (hN₁ : ∀ n ∈ N, σ₁ n = n) (hN₂ : ∀ n ∈ N, σ₂ n = n)
    (hfix : ∀ g, σ₁ g = g → σ₂ g = g → g ∈ N) :
    Nat.card G * Nat.card N ^ 2 =
      Nat.card (fixedSub σ₁) * Nat.card (fixedSub σ₂) * Nat.card (fixedSub σ₃) := by
  have hodd_p : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hNodd : Odd (Nat.card N) := by
    obtain ⟨m, hm⟩ := (hG.to_subgroup N).exists_card_eq
    rw [hm]
    exact hodd_p.pow
  have hN₃ : ∀ n ∈ N, σ₃ n = n := fun n hn => by rw [h₃, hN₂ n hn, hN₁ n hn]
  have hM₁ : N ≤ N.comap σ₁ := fun n hn => by rw [Subgroup.mem_comap, hN₁ n hn]; exact hn
  have hM₂ : N ≤ N.comap σ₂ := fun n hn => by rw [Subgroup.mem_comap, hN₂ n hn]; exact hn
  have hM₃ : N ≤ N.comap σ₃ := fun n hn => by rw [Subgroup.mem_comap, hN₃ n hn]; exact hn
  obtain ⟨q₁, q₂, qc, q₃, qf⟩ := quotient_klein hNodd h₁ h₂ hc h₃ hfix hM₁ hM₂ hM₃
  have hT := card_eq_prod_fixedSub hp (hG.to_quotient N) q₁ q₂ qc q₃
    (fun x hx₁ hx₂ => qf x hx₁ hx₂)
  have hR := card_mul_eq_of_quotient hNodd h₁ h₂ hc h₃ hM₁ hM₂ hM₃ hT
  have htop : ∀ (σ : G →* G) (hσ : ∀ n ∈ N, σ n = n) (hM : N ≤ N.comap σ),
      Nat.card (fixedSub (resEnd σ N hM)) = Nat.card N := by
    intro σ hσ hM
    have : fixedSub (resEnd σ N hM) = ⊤ := eq_top_iff.mpr fun n _ => Subtype.ext (hσ n n.2)
    rw [this, Subgroup.card_top]
  rw [htop σ₁ hN₁ hM₁, htop σ₂ hN₂ hM₂, htop σ₃ hN₃ hM₃] at hR
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [← hR]; ring)

end Induction

section Conj

variable {C : Type*} [Group C]

def conjEnd (A : Subgroup C) (u : C) (h : ∀ y ∈ A, u * y * u⁻¹ ∈ A) : A →* A where
  toFun y := ⟨u * y * u⁻¹, h y y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjEnd_eq_self_iff {A : Subgroup C} {u : C} {h : ∀ y ∈ A, u * y * u⁻¹ ∈ A} {y : A} :
    conjEnd A u h y = y ↔ (y : C) * u = u * y := by
  rw [Subtype.ext_iff]
  show u * (y : C) * u⁻¹ = y ↔ _
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem conjEnd_involutive {A : Subgroup C} {u : C} (hu : u ^ 2 = 1)
    (h : ∀ y ∈ A, u * y * u⁻¹ ∈ A) : ∀ y, conjEnd A u h (conjEnd A u h y) = y := by
  intro y
  apply Subtype.ext
  show u * (u * (y : C) * u⁻¹) * u⁻¹ = y
  have hu' : u * u = 1 := by rwa [← pow_two]
  calc u * (u * (y : C) * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ := by group
    _ = y := by rw [hu']; group

theorem card_fixedSub_conjEnd (A : Subgroup C) (u : C) (h : ∀ y ∈ A, u * y * u⁻¹ ∈ A) :
    Nat.card (fixedSub (conjEnd A u h)) =
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u} : Set C)) := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨y.1.1, y.1.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (conjEnd_eq_self_iff.mp y.2)⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, conjEnd_eq_self_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2)⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }

theorem conj_mul_mem {A : Subgroup C} {u₁ u₂ : C} (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) : ∀ y ∈ A, u₁ * u₂ * y * (u₁ * u₂)⁻¹ ∈ A := by
  intro y hy
  have e : u₁ * u₂ * y * (u₁ * u₂)⁻¹ = u₁ * (u₂ * y * u₂⁻¹) * u₁⁻¹ := by group
  rw [e]
  exact h₁ _ (h₂ y hy)

theorem conjEnd_comm {A : Subgroup C} {u₁ u₂ : C} (hc : u₁ * u₂ = u₂ * u₁)
    (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A) (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) (y : A) :
    conjEnd A u₁ h₁ (conjEnd A u₂ h₂ y) = conjEnd A u₂ h₂ (conjEnd A u₁ h₁ y) := by
  apply Subtype.ext
  show u₁ * (u₂ * (y : C) * u₂⁻¹) * u₁⁻¹ = u₂ * (u₁ * (y : C) * u₁⁻¹) * u₂⁻¹
  calc u₁ * (u₂ * (y : C) * u₂⁻¹) * u₁⁻¹ = (u₁ * u₂) * y * (u₁ * u₂)⁻¹ := by group
    _ = (u₂ * u₁) * y * (u₂ * u₁)⁻¹ := by rw [hc]
    _ = u₂ * (u₁ * (y : C) * u₁⁻¹) * u₂⁻¹ := by group

theorem conjEnd_mul {A : Subgroup C} {u₁ u₂ : C} (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) (h₃ : ∀ y ∈ A, u₁ * u₂ * y * (u₁ * u₂)⁻¹ ∈ A) (y : A) :
    conjEnd A (u₁ * u₂) h₃ y = conjEnd A u₁ h₁ (conjEnd A u₂ h₂ y) := by
  apply Subtype.ext
  show u₁ * u₂ * (y : C) * (u₁ * u₂)⁻¹ = u₁ * (u₂ * (y : C) * u₂⁻¹) * u₁⁻¹
  group

end Conj

end KleinOrder

open KleinOrder

variable {C : Type*} [Group C] [Finite C]

theorem card_eq_prod_centralizers_of_klein_of_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {A : Subgroup C} (hA : IsPGroup p A) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A)
    (hfix : ∀ y ∈ A, u₁ * y = y * u₁ → u₂ * y = y * u₂ → y = 1) :
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₂} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) := by
  have h₃ := conj_mul_mem h₁ h₂
  have key := card_eq_prod_fixedSub hp hA (σ₁ := conjEnd A u₁ h₁) (σ₂ := conjEnd A u₂ h₂)
    (σ₃ := conjEnd A (u₁ * u₂) h₃) (conjEnd_involutive hu₁ h₁) (conjEnd_involutive hu₂ h₂)
    (conjEnd_comm hc h₁ h₂) (conjEnd_mul h₁ h₂ h₃)
    (fun y hy₁ hy₂ => Subtype.ext (hfix y y.2 (conjEnd_eq_self_iff.mp hy₁).symm
      (conjEnd_eq_self_iff.mp hy₂).symm))
  rw [key, card_fixedSub_conjEnd, card_fixedSub_conjEnd, card_fixedSub_conjEnd]

theorem card_eq_prod_centralizers_of_klein {A : Subgroup C} (hA : IsPGroup 3 A) {u₁ u₂ : C}
    (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A) (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A)
    (hfix : ∀ y ∈ A, u₁ * y = y * u₁ → u₂ * y = y * u₂ → y = 1) :
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₂} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  card_eq_prod_centralizers_of_klein_of_ne_two (by norm_num) hA hu₁ hu₂ hc h₁ h₂ hfix

theorem card_mul_sq_eq_prod_centralizers_of_klein_of_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {A Z : Subgroup C} (hA : IsPGroup p A) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) (hZA : Z ≤ A) (hZc : ∀ z ∈ Z, ∀ y ∈ A, z * y = y * z)
    (hZfix : ∀ z ∈ Z, u₁ * z = z * u₁ ∧ u₂ * z = z * u₂)
    (hfix : ∀ y ∈ A, u₁ * y = y * u₁ → u₂ * y = y * u₂ → y ∈ Z) :
    Nat.card A * Nat.card Z ^ 2 = Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₂} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) := by
  have h₃ := conj_mul_mem h₁ h₂
  have hnorm : (Z.subgroupOf A).Normal := ⟨fun n hn g => by
    have hn' : (n : C) ∈ Z := hn
    have hcomm := hZc _ hn' _ g.2
    show (g : C) * n * (g : C)⁻¹ ∈ Z
    have e : (g : C) * n * (g : C)⁻¹ = n := by
      calc (g : C) * n * (g : C)⁻¹ = (n : C) * g * (g : C)⁻¹ := by rw [← hcomm]
        _ = n := by group
    rw [e]
    exact hn'⟩
  have hfix₁ : ∀ n ∈ Z.subgroupOf A, conjEnd A u₁ h₁ n = n := fun n hn =>
    conjEnd_eq_self_iff.mpr (hZfix _ hn).1.symm
  have hfix₂ : ∀ n ∈ Z.subgroupOf A, conjEnd A u₂ h₂ n = n := fun n hn =>
    conjEnd_eq_self_iff.mpr (hZfix _ hn).2.symm
  have key := card_mul_sq_eq_prod_fixedSub hp hA (N := Z.subgroupOf A)
    (σ₁ := conjEnd A u₁ h₁) (σ₂ := conjEnd A u₂ h₂) (σ₃ := conjEnd A (u₁ * u₂) h₃)
    (conjEnd_involutive hu₁ h₁) (conjEnd_involutive hu₂ h₂) (conjEnd_comm hc h₁ h₂)
    (conjEnd_mul h₁ h₂ h₃) hfix₁ hfix₂
    (fun y hy₁ hy₂ => hfix y y.2 (conjEnd_eq_self_iff.mp hy₁).symm
      (conjEnd_eq_self_iff.mp hy₂).symm)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv] at key
  rw [key, card_fixedSub_conjEnd, card_fixedSub_conjEnd, card_fixedSub_conjEnd]

theorem card_mul_sq_eq_prod_centralizers_of_klein {A Z : Subgroup C} (hA : IsPGroup 3 A)
    {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A) (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) (hZA : Z ≤ A)
    (hZc : ∀ z ∈ Z, ∀ y ∈ A, z * y = y * z)
    (hZfix : ∀ z ∈ Z, u₁ * z = z * u₁ ∧ u₂ * z = z * u₂)
    (hfix : ∀ y ∈ A, u₁ * y = y * u₁ → u₂ * y = y * u₂ → y ∈ Z) :
    Nat.card A * Nat.card Z ^ 2 = Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₂} : Set C)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  card_mul_sq_eq_prod_centralizers_of_klein_of_ne_two (by norm_num) hA hu₁ hu₂ hc h₁ h₂ hZA hZc
    hZfix hfix

end CFSG.Sporadic.Recognition.JankoWong
