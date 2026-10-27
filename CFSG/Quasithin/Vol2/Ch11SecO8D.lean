module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.E3Defs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin

namespace O8S

variable {W : Type} [CommGroup W]

theorem mem_fixV_zpowers {x : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fix_comm_elt (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W} (hz : z * z = 1) (w : W) :
    z (z w * w⁻¹) = z w * w⁻¹ := by
  have hzz : z (z w) = w := by rw [← MulAut.mul_apply, hz, MulAut.one_apply]
  have hinv : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hW v)
  rw [map_mul, map_inv, hzz, hinv (z w), hinv w, mul_comm]

theorem commute_of_fix_iff (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : ∀ w, x w = w ↔ y w = w) : x * y = y * x := by
  ext w
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have hcx := fix_comm_elt hW hx w
  have hdy := fix_comm_elt hW hy w
  have hcy := (hxy _).mp hcx
  have hdx := (hxy _).mpr hdy
  set a := x w * w⁻¹ with ha
  set b := y w * w⁻¹ with hb
  have hxw : x w = a * w := by rw [ha]; group
  have hyw : y w = b * w := by rw [hb]; group
  rw [hyw, map_mul, hdx, hxw, map_mul, hcy, hyw]
  exact mul_left_comm b a w

theorem conj_fix_iff (k u : MulAut W) (w : W) : (k * u * k⁻¹) w = w ↔ u (k⁻¹ w) = k⁻¹ w := by
  simp only [MulAut.mul_apply]
  constructor
  · intro h
    have := congrArg (k⁻¹ : MulAut W) h
    rwa [MulAut.inv_apply_self] at this
  · intro h
    rw [h, MulAut.apply_inv_self]

theorem fix_conj_iff {k u t : MulAut W} (hkt : k * t = t * k)
    (hut : ∀ w, u w = w ↔ t w = w) (w : W) : (k * u * k⁻¹) w = w ↔ t w = w := by
  have hkt' : k * t * k⁻¹ = t := by rw [hkt, mul_inv_cancel_right]
  rw [conj_fix_iff, hut, ← conj_fix_iff, hkt']

theorem isElementaryAbelian_of {G : Type*} [Group G] {B : Subgroup G}
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hs : ∀ a ∈ B, a ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_forall hc hs

theorem isPGroup_of_isElemAbelian2 {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) :
    IsPGroup 2 ↥A :=
  fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩

variable [Finite W]

theorem two_pow_le_card {n : ℕ} {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet n X) :
    2 ^ n ≤ Nat.card ↥A := by
  obtain ⟨-, hA1, hA2, hfix⟩ := hA
  have hP := isPGroup_of_isElemAbelian2 hA2
  have hcard := E3.card_eq_two_pow_mul hP (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
  rw [Subgroup.card_bot, mul_one] at hcard
  rw [hcard]
  refine Nat.pow_le_pow_right (by norm_num) (not_lt.mp fun hlt => hA1 ?_)
  have h1 := hfix ⊥ bot_le hlt
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ fixV (⊥ : Subgroup (MulAut W)) := fun x hx => by
    rw [Subgroup.mem_bot.mp hx]
    rfl
  rw [h1] at hw
  exact hw a ha

theorem fixV_zpowers_eq {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X)
    (h4 : Nat.card ↥A = 4) {u : MulAut W} (hu : u ∈ A) (hu1 : u ≠ 1) :
    fixV (Subgroup.zpowers u) = fixV A := by
  obtain ⟨-, -, hA2, hfix⟩ := hA
  have hle : Subgroup.zpowers u ≤ A := Subgroup.zpowers_le.mpr hu
  have hord : orderOf u = 2 := orderOf_eq_prime (hA2.2 u hu) hu1
  have hcard := E3.card_eq_two_pow_mul (isPGroup_of_isElemAbelian2 hA2) hle
  rw [h4, Nat.card_zpowers, hord] at hcard
  refine hfix _ hle ?_
  have h2 : 2 ^ E3.mQuot A (Subgroup.zpowers u) = 2 ^ 1 := by omega
  have := Nat.pow_right_injective le_rfl h2
  omega

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC
