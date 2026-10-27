module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

theorem odd_conj_mem_of_mem_pGroup {x : G} (hx : Odd (orderOf x)) {Z₀ L : Subgroup G}
    (hZL : Z₀ ≤ L) (hL : IsPGroup 2 L) (hxL : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Z₀) {a : G}
    (ha : x * a * x⁻¹ * a⁻¹ ∈ L) : x * a * x⁻¹ * a⁻¹ ∈ Z₀ := by
  set c : G := x * a * x⁻¹ * a⁻¹ with hc
  have key : ∀ j : ℕ, ∃ z ∈ Z₀, x ^ j * a * (x ^ j)⁻¹ * a⁻¹ = z * c ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, Z₀.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨z, hz, hj⟩ := ih
      have hsj : x ^ j * a * (x ^ j)⁻¹ = z * c ^ j * a := by
        calc x ^ j * a * (x ^ j)⁻¹ = (x ^ j * a * (x ^ j)⁻¹ * a⁻¹) * a := by group
          _ = z * c ^ j * a := by rw [hj]
      have hw : z * c ^ j ∈ L := L.mul_mem (hZL hz) (L.pow_mem ha j)
      have hxa : x * a * x⁻¹ = c * a := by rw [hc]; group
      have hz' := hxL _ hw
      refine ⟨(x * (z * c ^ j) * x⁻¹ * (z * c ^ j)⁻¹) * z, Z₀.mul_mem hz' hz, ?_⟩
      calc x ^ (j + 1) * a * (x ^ (j + 1))⁻¹ * a⁻¹
          = x * (x ^ j * a * (x ^ j)⁻¹) * x⁻¹ * a⁻¹ := by group
        _ = x * (z * c ^ j * a) * x⁻¹ * a⁻¹ := by rw [hsj]
        _ = (x * (z * c ^ j) * x⁻¹) * (x * a * x⁻¹) * a⁻¹ := by group
        _ = (x * (z * c ^ j) * x⁻¹) * (c * a) * a⁻¹ := by rw [hxa]
        _ = (x * (z * c ^ j) * x⁻¹ * (z * c ^ j)⁻¹) * z * c ^ (j + 1) := by group
  obtain ⟨z, hz, hk⟩ := key (orderOf x)
  have hck : c ^ orderOf x ∈ Z₀ := by
    have h1 : z * c ^ orderOf x = 1 := by
      rw [← hk, pow_orderOf_eq_one]; group
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Z₀.inv_mem hz
  obtain ⟨n, hn⟩ := hL ⟨c, ha⟩
  have hcn : c ^ 2 ^ n = 1 := by
    have := congrArg (fun y : L => (y : G)) hn
    simpa using this
  have hcop : Nat.Coprime (orderOf x) (orderOf c) := by
    have h2 : Nat.Coprime (2 ^ n) (orderOf x) := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hx)
    exact (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcn) h2).symm
  have hmem := A4.mem_zpowers_pow_of_coprime (x := c) (n := orderOf x) hcop
  exact (Subgroup.zpowers_le.mpr hck) hmem

theorem isPGroup_two_of_forall_odd_eq_one [Finite G] {X : Subgroup G}
    (h : ∀ y ∈ X, Odd (orderOf y) → y = 1) : IsPGroup 2 X := by
  intro g
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hpos : 0 < 2 ^ a := by positivity
  have hgb : orderOf ((g : G) ^ 2 ^ a) = b := by
    rw [orderOf_pow' _ (pow_ne_zero a two_ne_zero), hab, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ hpos]
  have h1 : (g : G) ^ 2 ^ a = 1 := h _ (X.pow_mem g.2 _) (hgb ▸ hb)
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

theorem eq_one_of_odd_of_mem_pGroup {X : Subgroup G} (hX : IsPGroup 2 X) {y : G} (hy : y ∈ X)
    (ho : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := hX ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg (fun z : X => (z : G)) hk
    simpa using this
  have hcop : Nat.Coprime (orderOf y) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho)
  have h1 : orderOf y = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk')
  exact orderOf_eq_one_iff.mp h1

theorem mem_pCoreOf_of_comm_mod_central [Finite G] {Mc Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hZc : ∀ g ∈ Mc, ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hchar : Mc ⊓ Subgroup.centralizer (pCoreOf 2 Mc : Set G) ≤ pCoreOf 2 Mc)
    {x : G} (hx : x ∈ Mc) (hxq : ∀ q ∈ pCoreOf 2 Mc, x * q * x⁻¹ * q⁻¹ ∈ Z) :
    x ∈ pCoreOf 2 Mc := by
  set Q := pCoreOf 2 Mc with hQ
  have hQn : ∀ g ∈ Mc, ∀ q, q ∈ Q ↔ g * q * g⁻¹ ∈ Q := fun g hg q =>
    Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc hg) q
  let X : Subgroup G :=
    { carrier := {y | y ∈ Mc ∧ ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ Z}
      one_mem' := ⟨Mc.one_mem, fun q _ => by simp [Z.one_mem]⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨Mc.mul_mem hy₁ hy₂, fun q hq => ?_⟩
        have hc := h₂ q hq
        have e : y₁ * y₂ * q * (y₁ * y₂)⁻¹ * q⁻¹ =
            (y₁ * (y₂ * q * y₂⁻¹ * q⁻¹) * y₁⁻¹) * (y₁ * q * y₁⁻¹ * q⁻¹) := by group
        rw [e, hZc y₁ hy₁ _ hc]
        exact Z.mul_mem hc (h₁ q hq)
      inv_mem' := by
        rintro y ⟨hy, h⟩
        refine ⟨Mc.inv_mem hy, fun q hq => ?_⟩
        have hq' : y⁻¹ * q * y ∈ Q := by
          have := (hQn y⁻¹ (Mc.inv_mem hy) q).mp hq
          simpa using this
        have hu := h _ hq'
        have e : y⁻¹ * q * y⁻¹⁻¹ * q⁻¹ =
            (y * (y⁻¹ * q * y) * y⁻¹ * (y⁻¹ * q * y)⁻¹)⁻¹ := by group
        rw [e]
        exact Z.inv_mem hu }
  have hXMc : X ≤ Mc := fun y hy => hy.1
  have key : ∀ g ∈ Mc, ∀ y ∈ X, g * y * g⁻¹ ∈ X := by
    intro g hg y
    rintro ⟨hy, h⟩
    refine ⟨Mc.mul_mem (Mc.mul_mem hg hy) (Mc.inv_mem hg), fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (hQn g⁻¹ (Mc.inv_mem hg) q).mp hq
      simpa using this
    have hc := h _ hq'
    have e : g * y * g⁻¹ * q * (g * y * g⁻¹)⁻¹ * q⁻¹ =
        g * (y * (g⁻¹ * q * g) * y⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
    rw [e, hZc g hg _ hc]
    exact hc
  have hXn : Mc ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (Mc.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have h2 : IsPGroup 2 X := by
    refine isPGroup_two_of_forall_odd_eq_one fun y hy ho => ?_
    have hcomm : ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) := fun q hq =>
      odd_conj_mem_of_mem_pGroup ho (Z₀ := ⊥) (L := Z) bot_le hZ
        (fun l hl => by rw [hZc y hy.1 l hl]; simp) (hy.2 q hq)
    have hyc : y ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := Subgroup.mem_bot.mp (hcomm q hq)
      calc q * y = (y * q * y⁻¹ * q⁻¹) * (q * y) := by rw [this]; simp
        _ = y * q := by group
    exact eq_one_of_odd_of_mem_pGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc)
      (hchar ⟨hy.1, hyc⟩) ho
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXMc hXn h2 ⟨hx, hxq⟩

end CFSG.Quasithin
