module

public import CFSG.Quasithin.Vol2.GoldschmidtH11FixCard
public import CFSG.Quasithin.Background.D2Basic

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

omit [Finite F] in
theorem sq_HV (v : HV F a) : v ^ 2 = 1 := by
  apply hm_injective a
  rw [pow_two, hm_mul, hm_one]
  ext i j
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [Matrix.add_apply, Matrix.zero_apply]
  linear_combination hm a v i j * h2

@[expose] noncomputable def hvEquiv (h : Nat.card F = 2 ^ (2 * a)) :
    HV F a ≃ ((Kf a : Subfield F) : Set F) × F × ((Kf a : Subfield F) : Set F) where
  toFun v := (⟨hm a v 0 0, (mem_Kf a).mpr (hm_entry a v 0 0)⟩, hm a v 0 1,
    ⟨hm a v 1 1, (mem_Kf a).mpr (hm_entry a v 1 1)⟩)
  invFun p := hermV a h p.1.1 p.2.1 p.2.2.1 ((mem_Kf a).mp p.1.2) ((mem_Kf a).mp p.2.2.2)
  left_inv v := by
    apply hm_injective a
    rw [hm_hermV, hm_eq a v]
  right_inv p := by simp [hm_hermV]

theorem card_HV (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) : Nat.card (HV F a) = 2 ^ (4 * a) := by
  rw [Nat.card_congr (hvEquiv h), Nat.card_prod, Nat.card_prod, card_Kf a ha h, h,
    ← pow_add, ← pow_add]
  congr 1
  ring

theorem rk_HV (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) : rk (HV F a) = 4 * a := by
  rw [rk, card_HV ha h, padicValNat.prime_pow]

theorem rkIdx_add_rk (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) (C : Subgroup (HV F a)) :
    rkIdx C + rk C = 4 * a := by
  have := rk_add_rkIdx C
  rw [rk_HV ha h] at this
  omega

theorem card_two_pow_rk (C : Subgroup (HV F a)) : Nat.card C = 2 ^ rk C :=
  card_eq_two_pow sq_HV C

omit [Finite F] in
theorem isPGroup_of_isElemAbelian2 {A : Subgroup (MulAut (HV F a))} (hA : IsElemAbelian2 A) :
    IsPGroup 2 A := fun x => ⟨1, by
  apply Subtype.ext
  simpa using hA.2 x.1 x.2⟩

theorem inner_rank {A : Subgroup (MulAut (HV F a))} (hU : UType a h A) (hA1 : A ≠ ⊥)
    (hel : IsElemAbelian2 A) (ha : 0 < a) : rk A + a ≤ rkIdx (fixV A) := by
  obtain ⟨d₀, hd₀, hd₀0⟩ := exists_ne_zero_of_ne_bot hU hA1
  have h1 := card_fixV_le hU hA1
  have h2 := card_mul_card_perp_le a ha h (Tset a h A) hd₀ hd₀0
  have hK := card_Kf a ha h
  have hA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hel)
  have hC := card_two_pow_rk (fixV A)
  have hmul : 2 ^ (rk A + rk (fixV A)) ≤ 2 ^ (3 * a) := by
    rw [pow_add, ← hA, ← hC, card_eq_card_Tset hU]
    calc Nat.card (Tset a h A) * Nat.card (fixV A)
        ≤ Nat.card (Tset a h A) * (Nat.card ((Kf a : Subfield F) : Set F) *
            Nat.card (perp a (Tset a h A))) := Nat.mul_le_mul_left _ h1
      _ = Nat.card ((Kf a : Subfield F) : Set F) *
            (Nat.card (Tset a h A) * Nat.card (perp a (Tset a h A))) := by ring
      _ ≤ 2 ^ a * 2 ^ (2 * a) := by rw [hK, ← h]; exact Nat.mul_le_mul_left _ h2
      _ = 2 ^ (3 * a) := by rw [← pow_add]; ring_nf
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hmul
  have := rkIdx_add_rk ha h (fixV A)
  omega

theorem outer_rank {A : Subgroup (MulAut (HV F a))} (hU : UType a h A) (hA1 : A ≠ ⊥)
    (hel : IsElemAbelian2 A) (ha : 0 < a) (hK : Tset a h A ⊆ ((Kf a : Subfield F) : Set F)) :
    rk A ≤ a ∧ 2 * a ≤ rkIdx (fixV A) := by
  have hKc := card_Kf a ha h
  have hA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hel)
  have hC := card_two_pow_rk (fixV A)
  have h1 : Nat.card A ≤ 2 ^ a := by
    rw [card_eq_card_Tset hU, ← hKc]
    exact Nat.card_mono (Set.toFinite _) hK
  have h2 : Nat.card (fixV A) ≤ 2 ^ a * 2 ^ a := by
    rw [← hKc]; exact card_fixV_le_of_sub hU hA1 hK
  rw [hA] at h1
  rw [hC, ← pow_add] at h2
  have e1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have e2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have := rkIdx_add_rk ha h (fixV A)
  omega

end CFSG.Quasithin.H11
