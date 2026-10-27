module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.LargeExtraspecial.AS62F431
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

theorem card_mul_dvd_of_a6Config {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (h : A6Config Y F) : Nat.card ↥F * 360 ∣ Nat.card X := by
  obtain ⟨-, ⟨φ, hφs, hφk⟩, hFQ, -, -, -⟩ := h
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hY : Nat.card ↥Y = Nat.card ↥(pCore 2 ↥Y) * 360 := by
    rw [← hA6, ← hφk, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker)
  have hQ : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(pCore 2 ↥Y) := by
    rw [pCoreOf]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  have hFdvd : Nat.card ↥F ∣ Nat.card ↥(pCore 2 ↥Y) := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le hFQ
  calc Nat.card ↥F * 360 ∣ Nat.card ↥(pCore 2 ↥Y) * 360 := Nat.mul_dvd_mul_right hFdvd 360
    _ = Nat.card ↥Y := hY.symm
    _ ∣ Nat.card X := Subgroup.card_subgroup_dvd_card Y

theorem isPGroup_of_a6Config {X : Type} [Group X] {Y F : Subgroup X} (h : A6Config Y F) :
    IsPGroup 2 ↥F :=
  (CFSG.LargeExtraspecial.AS62.isPGroup_pCoreOf 2 Y).to_le h.2.2.1

private theorem le_sixteen_of_dvd {F : Type} [Group F] [Finite F] (hF : IsPGroup 2 F) {m : ℕ}
    (hm : Odd m) (h : Nat.card F * 360 ∣ 2 ^ 7 * m) : Nat.card F ≤ 16 := by
  obtain ⟨k, hk⟩ := hF.exists_card_eq
  rw [hk] at h ⊢
  have h2 : 2 ^ k * 8 ∣ 2 ^ 7 * m := (Nat.mul_dvd_mul_left _ (by norm_num : (8 : ℕ) ∣ 360)).trans h
  rw [show 2 ^ k * 8 = 2 ^ (k + 3) by ring] at h2
  have hcop : Nat.Coprime (2 ^ (k + 3)) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h3 : 2 ^ (k + 3) ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_right h2
  have hk4 : k + 3 ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 := by norm_num

theorem a6LocM22_holds : A6LocM22 := by
  intro X _ _ ⟨e⟩ Y F h
  have hX : Nat.card X = 2 ^ 7 * 3465 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m22_card]; norm_num
  have hd := card_mul_dvd_of_a6Config h
  rw [hX] at hd
  exact le_sixteen_of_dvd (isPGroup_of_a6Config h) (by decide) hd

theorem a6LocM23_holds : A6LocM23 := by
  intro X _ _ ⟨e⟩ Y F h
  have hX : Nat.card X = 2 ^ 7 * 79695 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m23_card]; norm_num
  have hd := card_mul_dvd_of_a6Config h
  rw [hX] at hd
  exact le_sixteen_of_dvd (isPGroup_of_a6Config h) (by decide) hd

end CFSG.Quasithin.H13.K1262Two
