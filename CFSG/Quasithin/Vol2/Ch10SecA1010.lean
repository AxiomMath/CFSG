module

public import CFSG.Quasithin.Vol2.Ch10SecAModels
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem eq_of_two_pow_mul_odd {k l A B : ℕ} (hA : Odd A) (hB : Odd B)
    (h : 2 ^ k * A = 2 ^ l * B) : k = l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hA.pos.ne', padicValNat.mul (by positivity) hB.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hA; omega),
    padicValNat.eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hB; omega)] at h1
  simpa using h1

theorem odd_two_pow_sub_one_of_pos {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) :=
  Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' (by omega)).mpr even_two) odd_one

theorem omegaPlus_orth_card_ne {n a : ℕ} (hn : 2 ≤ n) (ha : 1 ≤ a) :
    (2 ^ n * ((2 ^ n) ^ 2 - 1)) ^ 2 ≠ 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by
  intro h
  have hx : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hodd1 : Odd ((2 ^ (2 * n) - 1) ^ 2) := (odd_two_pow_sub_one_of_pos (by omega)).pow
  have hodd2 : Odd ((2 ^ (2 * a)) ^ 2 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one_of_pos (by omega)
  have h' : 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2 = 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by
    rw [← h, hx]
    ring
  have hna : n = a := by have := eq_of_two_pow_mul_odd hodd1 hodd2 h'; omega
  subst hna
  have h2 : (2 ^ (2 * n) - 1) ^ 2 = (2 ^ (2 * n)) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have hx2 : 2 ≤ 2 ^ (2 * n) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set x := 2 ^ (2 * n)
  have h1x : 1 ≤ x := by omega
  have h1x2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1x, h1x2] at h2
  nlinarith

theorem l3Wreath_orth_card_ne {a : ℕ} (ha : 1 < a) :
    168 ^ 2 ≠ 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by
  intro h
  have hodd2 : Odd ((2 ^ (2 * a)) ^ 2 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one_of_pos (by omega)
  have h' : 2 ^ 6 * 441 = 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by rw [← h]; norm_num
  have h3 : a = 3 := by have := eq_of_two_pow_mul_odd (by decide) hodd2 h'; omega
  subst h3
  norm_num at h

variable {G : Type} [Group G] {T L I : Subgroup G}

theorem card_fsuV_of_omegaPlus [IsMulCommutative ↥(fsuV T I)] {n : ℕ}
    (h : Row711OmegaPlus T L I n) : Nat.card ↥(fsuV T I) = 2 ^ (4 * n) := by
  obtain ⟨-, -, K, _, _, hK, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_tensorPair hπ, hK, Fintype.card_fin, ← pow_mul]
  ring_nf

theorem card_fsuV_of_l3Wreath [IsMulCommutative ↥(fsuV T I)] (h : Row711L3Wreath T L I) :
    Nat.card ↥(fsuV T I) = 2 ^ 9 := by
  obtain ⟨-, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_tensorPair hπ, Nat.card_zmod, Fintype.card_fin]

theorem card_autOn_of_omegaPlus [IsMulCommutative ↥(fsuV T I)] {n : ℕ}
    (h : Row711OmegaPlus T L I n) :
    Nat.card ↥(autOn (fsuL0 T L) (fsuV T I)) = (2 ^ n * ((2 ^ n) ^ 2 - 1)) ^ 2 := by
  obtain ⟨-, -, K, _, _, hK, π, hπ⟩ := h
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  rw [card_eq_of_realizesVia_faithful (tensorPair_faithful _ _ scalar_statedSL_two) hπ]
  change Nat.card (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = _
  rw [Nat.card_prod, card_statedSL_two, hK', ← sq]

theorem card_autOn_of_l3Wreath [IsMulCommutative ↥(fsuV T I)] (h : Row711L3Wreath T L I) :
    Nat.card ↥(autOn (fsuL0 T L) (fsuV T I)) = 168 ^ 2 := by
  obtain ⟨-, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_faithful (tensorPair_faithful _ _ scalar_statedSL_three_two) hπ]
  change Nat.card (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) = _
  rw [Nat.card_prod, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv,
    Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem card_autOn_of_orth [IsMulCommutative ↥(fsuV T I)] {a : ℕ}
    (h : BinaryOrthogonalFour (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ a) :
    Nat.card ↥(autOn (fsuL0 T L) (fsuV T I)) = 2 ^ (2 * a) * ((2 ^ (2 * a)) ^ 2 - 1) := by
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := h
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card, hK]
  rw [card_eq_of_realizesVia_faithful (twistTensor_faithful a) hπ]
  change Nat.card ↥(StatedSL 2 K) = _
  rw [card_statedSL_two, hK']

theorem stmt10_1_0_of (h326 : TmpL6_3_2_6) (hnFF : AS_p696_notFF) :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
      ∀ _ : IsMulCommutative ↥(fsuV T I),
        Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I → Concl326Three T L I := by
  intro G _ _ T L I hfsu hlt hc hconcl
  obtain ⟨-, -, hcase⟩ := h326 G T L I hfsu hlt
  rcases hcase with ⟨_, -, -, hrow⟩ | h3
  · exfalso
    rcases hconcl with hFF | hJ4 | ⟨a, ha, hOrth⟩
    · exact hnFF G T L I hfsu hlt hc hrow hFF
    · have hV := hJ4.2.2.1
      rcases hrow with ⟨n, hn⟩ | hw
      · rw [card_fsuV_of_omegaPlus hn] at hV
        have := Nat.pow_right_injective (le_refl 2) hV
        omega
      · rw [card_fsuV_of_l3Wreath hw] at hV
        norm_num at hV
    · have hA := card_autOn_of_orth hOrth
      rcases hrow with ⟨n, hn⟩ | hw
      · rw [card_autOn_of_omegaPlus hn] at hA
        exact omegaPlus_orth_card_ne hn.2.1 (by omega) hA
      · rw [card_autOn_of_l3Wreath hw] at hA
        exact l3Wreath_orth_card_ne ha hA
  · exact h3

end CFSG.Quasithin.Vol2.Ch10.SecA
