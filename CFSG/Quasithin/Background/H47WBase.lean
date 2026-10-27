module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.ConjTransport

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin

theorem rk_fixV_zpowers_conj {V : Type*} [CommGroup V] (h g : MulAut V) :
    rk ↥(fixV (Subgroup.zpowers (h * g * h⁻¹))) = rk ↥(fixV (Subgroup.zpowers g)) := by
  have hz : Subgroup.zpowers (h * g * h⁻¹) =
      (Subgroup.zpowers g).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hz]
  unfold rk
  rw [ConjTransport.card_fixV_map_conj]

theorem rk_fixV_zpowers_congr {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (g : MulAut V) :
    rk ↥(fixV (Subgroup.zpowers (MulAut.congr e g))) = rk ↥(fixV (Subgroup.zpowers g)) := by
  have hz : Subgroup.zpowers (MulAut.congr e g) =
      (Subgroup.zpowers g).map (MulAut.congr e).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hz, fixV_map_congr_equiv]
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

theorem sq_zpow_of_sq_eq_one {G : Type*} [Group G] {t : G} (ht : t * t = 1) (k : ℤ) :
    (t ^ k) * (t ^ k) = 1 := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul, h2, one_zpow]

theorem isPGroup_two_zpowers {G : Type*} [Group G] {t : G} (ht : t * t = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  refine isPGroup_two_of_sq_eq_one fun x => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
  rw [sq]
  apply Subtype.ext
  show (x : G) * (x : G) = 1
  rw [← hk]
  exact sq_zpow_of_sq_eq_one ht k

theorem isPGroup_two_sub {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (F : Subgroup V) :
    IsPGroup 2 F :=
  isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by simpa using hV x.1)

theorem rk_le_of_card_le {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (F : Subgroup V) {k : ℕ} (h : Nat.card F ≤ 2 ^ k) : rk ↥F ≤ k := by
  have e := card_eq_two_pow_of_isPGroup (isPGroup_two_sub hV F)
  rw [e] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem le_rk_of_pow_le {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (F : Subgroup V) {k : ℕ} (h : 2 ^ k ≤ Nat.card F) : k ≤ rk ↥F := by
  have e := card_eq_two_pow_of_isPGroup (isPGroup_two_sub hV F)
  rw [e] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem rk_commV_zpowers_eq_sub {V : Type*} [CommGroup V] [Finite V] (g : MulAut V) :
    rk ↥(commV (Subgroup.zpowers g)) + rk ↥(fixV (Subgroup.zpowers g)) = rk V :=
  rk_commV_add_rk_fixV g

end CFSG.Quasithin.H47W
