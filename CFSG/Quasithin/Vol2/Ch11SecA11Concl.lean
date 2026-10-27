module

public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Blueprint

@[expose] def Concl1111 (X : Type) [Group X] (n : ℕ) : Prop :=
  List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X)

section Three

variable {X : Type} [Group X]

theorem three_alt7 (h : IsAlt 7 X) : List11_1_1Three X := Or.inl h

theorem three_hat7 (h : IsHat X (alternatingGroup (Fin 7))) : List11_1_1Three X :=
  Or.inr (Or.inl h)

theorem three_psl2p {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 1 ∨ p % 5 = 4)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (h : IsPSL 2 p 1 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inl ⟨p, hp, h5, h8, h⟩))

theorem three_psl225 (h : IsPSL 2 5 2 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem three_sl35 {s : Bool} (h : IsSLEps3 s 5 X ∨ IsPSLEps3 s 5 1 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, h⟩))))

theorem three_M22 (h : IsSporadic .M22 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem three_hatM22 (h : IsHat X (NativeSporadic.Carrier .M22)) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem three_M23 (h : IsSporadic .M23 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem three_J1 (h : IsSporadic .J1 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem three_J2 (h : IsSporadic .J2 X) : List11_1_1Three X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem three_J4 (h : IsSporadic .J4 X) : List11_1_1Three X := by
  iterate 10 right
  exact Or.inl h

theorem three_HS (h : IsSporadic .HS X) : List11_1_1Three X := by
  iterate 11 right
  exact Or.inl h

theorem three_Ru (h : IsSporadic .Ru X) : List11_1_1Three X := by
  iterate 12 right
  exact Or.inl h

theorem three_case4 (h : A36Case4 X) : List11_1_1Three X := by
  iterate 13 right
  exact Or.inl h

end Three

theorem mod_five_of_sq {p : ℕ} (h : p ^ 2 % 5 = 1) : p % 5 = 1 ∨ p % 5 = 4 := by
  rw [Nat.pow_mod] at h
  have hr : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize p % 5 = r at h hr ⊢
  interval_cases r <;> simp_all

theorem oSL2_ne_21 {n : ℕ} : oSL2 n ≠ 21 := oSL2_ne (k := 3) (by decide) (by decide)

theorem oSL2_ne_45 {n : ℕ} : oSL2 n ≠ 45 := oSL2_ne (k := 3) (by decide) (by decide)

theorem oSL2_ne_135 {n : ℕ} : oSL2 n ≠ 135 := oSL2_ne (k := 4) (by decide) (by decide)

theorem oSL2_ne_315 {n : ℕ} : oSL2 n ≠ 315 := oSL2_ne (k := 5) (by decide) (by decide)

theorem card_ext_eq {N k c d o : ℕ} (hN : N = 2 ^ k * c) (hc : c = 2 ^ d * o) :
    N = 2 ^ (k + d) * o := by
  rw [hN, hc, pow_add, mul_assoc]

namespace BarData

variable {Q : Type} [Group Q] {B : Subgroup Q} {n : ℕ}

theorem oSL2_eq (hD : BarData B n) {d o : ℕ} (ho : Odd o) (h : Nat.card ↥B = 2 ^ d * o) :
    oSL2 n = o := by
  obtain ⟨a, ha⟩ := hD.card
  exact eq_of_two_pow_mul_eq (odd_oSL2 (by have := hD.two_le; omega)) ho (ha.symm.trans h)

theorem oSL2_eq' (hD : BarData B n) {d o : ℕ} (ho : Odd o)
    (h : Nat.card (ModO2 B) = 2 ^ d * o) : oSL2 n = o :=
  eq_of_two_pow_mul_eq (odd_oSL2 (by have := hD.two_le; omega)) ho (hD.cardQ.symm.trans h)

theorem eq_two (hD : BarData B n) {d : ℕ} (h : Nat.card ↥B = 2 ^ d * 15) : n = 2 :=
  oSL2_eq_fifteen (hD.oSL2_eq (by decide) h)

theorem eq_two' (hD : BarData B n) {d : ℕ} (h : Nat.card (ModO2 B) = 2 ^ d * 15) : n = 2 :=
  oSL2_eq_fifteen (hD.oSL2_eq' (by decide) h)

theorem false_of_M22 (hD : BarData B n) {k m : ℕ} (hm : m ∣ 3)
    (h : Nat.card ↥B = 2 ^ k * (m * Nat.card ↥NativeSporadic.M22)) : False := by
  obtain ⟨a, ha⟩ := hD.card
  have hodd := odd_oSL2 (m := n) (by have := hD.two_le; omega)
  have h11 : 11 ∣ oSL2 n := by
    have h1 : 11 ∣ 2 ^ (a + n) * oSL2 n := by
      rw [← ha, h]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right eleven_dvd_card_M22 _) _
    exact ((Nat.coprime_primes (by norm_num) Nat.prime_two).mpr (by norm_num)).pow_right _
      |>.dvd_of_dvd_mul_left h1
  have hdvd : oSL2 n ∣ 3 * Nat.factorial 22 := by
    have h1 : oSL2 n ∣ 2 ^ k * (m * Nat.card ↥NativeSporadic.M22) := by
      rw [← h, ha]
      exact dvd_mul_left _ _
    have h2 := ((Nat.coprime_two_left.mpr hodd).symm.pow_right k).dvd_of_dvd_mul_left h1
    exact h2.trans (mul_dvd_mul hm card_M22_dvd)
  exact false_of_eleven_dvd h11 hdvd

theorem false_of_M24 (hD : BarData B n) {k : ℕ}
    (h : Nat.card ↥B = 2 ^ k * Nat.card ↥NativeSporadic.M24) : False := by
  obtain ⟨a, ha⟩ := hD.card
  have hodd := odd_oSL2 (m := n) (by have := hD.two_le; omega)
  have h23 : 23 ∣ oSL2 n := by
    have h1 : 23 ∣ 2 ^ (a + n) * oSL2 n := by
      rw [← ha, h]
      exact dvd_mul_of_dvd_right twentythree_dvd_card_M24 _
    exact ((Nat.coprime_primes (by norm_num) Nat.prime_two).mpr (by norm_num)).pow_right _
      |>.dvd_of_dvd_mul_left h1
  have hdvd : oSL2 n ∣ Nat.factorial 24 := by
    have h1 : oSL2 n ∣ 2 ^ k * Nat.card ↥NativeSporadic.M24 := by
      rw [← h, ha]
      exact dvd_mul_left _ _
    exact (((Nat.coprime_two_left.mpr hodd).symm.pow_right k).dvd_of_dvd_mul_left h1).trans
      card_M24_dvd
  exact false_of_twentythree_dvd h23 hdvd

end BarData

end CFSG.Quasithin.Vol2.Ch11.SecA
