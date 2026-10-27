module

public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin.SteinbergBS

open CFSG.Open CFSG.Quasithin

universe u v

section Weak

variable {G : Type u} [Group G]

variable [Finite G]

theorem wClos_le_wClos {V : Subgroup G} (hV : IsElemAbelian 2 V) {d : ℕ}
    (hd : Nat.card V = 2 ^ d) {i j : ℕ} (hij : i ≤ j) (hjd : j < d) (Y : Subgroup G) :
    E3.wClos V i Y ≤ E3.wClos V j Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine E3.wClos_le_of_forall fun A hA a ha => ?_
  obtain ⟨hAY, g, hAVg, hAi⟩ := hA
  have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
    (B2F.isPGroup_of_isElemAbelian hV).map _
  have hVgcard : Nat.card (conjSubgroup V g) = 2 ^ d := by
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hd]
  have hAcard : Nat.card A = 2 ^ (d - i) := by
    have h := E3.card_eq_two_pow_mul hVg2 hAVg
    rw [hVgcard, hAi] at h
    have hid : i ≤ d := hij.trans hjd.le
    rw [show d = i + (d - i) by omega, pow_add] at h
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
  have ha2 : a ^ 2 = 1 := by
    have hg := mem_conjSubgroup_iff.1 (hAVg ha)
    have h1 : (g * a * g⁻¹) ^ 2 = 1 := hV.2 _ hg
    have h2 : (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
    rw [h2] at h1
    have h3 : a ^ 2 = g⁻¹ * (g * a ^ 2 * g⁻¹) * g := by group
    rw [h3, h1]
    group
  obtain ⟨B, hBcard, haB, hBA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := d - j) (H := Subgroup.zpowers a) (L := A)
    ((Nat.card_zpowers a).symm ▸ (orderOf_dvd_of_pow_eq_one ha2).trans
      (dvd_pow_self 2 (by omega)))
    (hAcard ▸ pow_dvd_pow 2 (by omega)) ((Subgroup.zpowers_le).2 ha)
  have hBj : E3.mQuot (conjSubgroup V g) B = j := by
    have h := E3.card_eq_two_pow_mul hVg2 (hBA.trans hAVg)
    rw [hVgcard, hBcard, ← pow_add] at h
    have h' := Nat.pow_right_injective (le_refl 2) h
    omega
  exact E3.le_wClos ⟨hBA.trans hAY, g, hBA.trans hAVg, hBj⟩ (haB (Subgroup.mem_zpowers a))

end Weak

end CFSG.Quasithin.SteinbergBS
