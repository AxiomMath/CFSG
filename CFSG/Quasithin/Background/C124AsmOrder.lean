module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Vol2.KGNatG2Order

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch10.SecA

theorem card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [card_alt 5 (by norm_num)]
  decide

theorem card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [card_alt 6 (by norm_num)]
  decide

theorem card_alt_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [card_alt 7 (by norm_num)]
  decide

theorem card_alt_cases {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    (m = 5 ∧ Nat.card ↥(alternatingGroup (Fin m)) = 60) ∨
      (m = 6 ∧ Nat.card ↥(alternatingGroup (Fin m)) = 360) ∨
      (m = 7 ∧ Nat.card ↥(alternatingGroup (Fin m)) = 2520) := by
  rcases hm with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, card_alt_five⟩
  · exact Or.inr (Or.inl ⟨rfl, card_alt_six⟩)
  · exact Or.inr (Or.inr ⟨rfl, card_alt_seven⟩)

theorem sixty_dvd_not_sixteen_dvd {m z N : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) (hz : Odd z)
    (hN : N = Nat.card ↥(alternatingGroup (Fin m)) * z) : 60 ∣ N ∧ ¬ 16 ∣ N := by
  obtain ⟨k, rfl⟩ := hz
  rcases card_alt_cases hm with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hN <;> subst hN <;> omega

theorem sl_two_aux (q : ℕ) (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 2 - q) / (q - 1) = q * (q ^ 2 - 1) := by
  have hpos : 0 < q - 1 := by omega
  have e1 : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, ← sq]
  rw [e1, show (q ^ 2 - 1) * (q * (q - 1)) = (q * (q ^ 2 - 1)) * (q - 1) by ring,
    Nat.mul_div_cancel _ hpos]

theorem card_statedSL_two_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSL 2 K) = 2 ^ n * (2 ^ (2 * n) - 1) := by
  rw [card_statedSL]
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← Nat.card_eq_fintype_card, hK]
  have h2 : 2 ≤ 2 ^ n := by
    have h := Finite.one_lt_card (α := K)
    rw [hK] at h
    omega
  rw [sl_two_aux _ h2, ← pow_mul, mul_comm n 2]

theorem sixty_four_dvd_card_G2 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : 64 ∣ Nat.card ↥(CFSG.Open.quasithinG2 K) := by
  have hcp : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    Vol2.KGNat.card_cayleyGroup, hK, ← pow_mul]
  exact Dvd.dvd.mul_right ((show (64 : ℕ) = 2 ^ 6 by norm_num) ▸
    pow_dvd_pow 2 (by nlinarith)) _

theorem card_G2_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(CFSG.Open.quasithinG2 K) = 12096 := by
  have hcp : CharP K 2 := Vol2.KGNat.charP_two_of_card (n := 1) (by norm_num) (by rw [hK]; rfl)
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    Vol2.KGNat.card_cayleyGroup, hK]
  norm_num

theorem eq_of_surjective_alt {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m)
    (f : ↥(alternatingGroup (Fin n)) →* ↥(alternatingGroup (Fin m))) (hf : Function.Surjective f) :
    n = m := by
  have hsn := isSimpleGroup_alt hn
  have hsm := isSimpleGroup_alt hm
  have hinj : Function.Injective f := by
    rcases hsn.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).1 h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin m)))
      obtain ⟨g, rfl⟩ := hf x
      exact hx (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
  have hcard := Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hf⟩).toEquiv
  rw [card_alt n (by omega), card_alt m (by omega)] at hcard
  have h2 : n.factorial = m.factorial := by
    have h2n : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  exact (Nat.factorial_inj (by omega)).1 h2

end CFSG.Quasithin.C124
