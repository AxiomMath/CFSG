module

public import CFSG.Quasithin.Vol2.Ch10SecC3R
public import CFSG.Quasithin.Vol2.Ch10SecC3N
public import CFSG.Quasithin.Vol2.Ch10SecC3Q

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

omit [CharP K 2] [Finite K] in
theorem card_ringAut {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card (K ≃+* K) = n := by
  obtain ⟨Fr, -, hord, hzp⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data hn hK
  rw [← hord, ← Nat.card_zpowers, hzp]
  exact Subgroup.card_top.symm

omit [CharP K 2] [Finite K] in
theorem fixV_anti {A B : Subgroup (MulAut (WM K))} (h : B ≤ A) : fixV A ≤ fixV B :=
  fun _ hv x hx => hv x (h hx)

theorem card_mul_card_fixV_lt {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (WM K))} (hAN : A ≤ norm K) (hA : IsElemAbelian2 A) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card ↥(fixV A) < Nat.card K ^ 4 := by
  set q := Nat.card K with hqdef
  have hq4 : 4 ≤ q := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnq : n < q := by rw [hK]; exact Nat.lt_two_pow_self
  have haut : Nat.card (K ≃+* K) = n := card_ringAut (by omega) hK
  have h1 := card_le_card_inf_linSub_mul hq4 hAN
  have h2 := card_inf_linSub_le hq4 hAN hA
  rw [haut] at h1
  set B := A ⊓ img K with hBdef
  have hBel : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hA.1 a ha.1 b hb.1, fun a ha => hA.2 a ha.1⟩
  have hfixAB : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV B) :=
    Subgroup.card_le_of_le (fixV_anti inf_le_left)
  have hq3 : 2 * q ^ 3 < q ^ 4 := by
    calc 2 * q ^ 3 < q * q ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = q ^ 4 := by ring
  by_cases hlin : A ≤ linSub K
  ·
    have hAK : A ⊓ linSub K = A := inf_eq_left.mpr hlin
    rw [hAK] at h2
    by_cases hB : B = ⊥
    · rw [hB, Subgroup.card_bot, mul_one] at h2
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hcl : IsKClosed (fixV (Subgroup.zpowers (a : MulAut (WM K)))) :=
        isKClosed_fixV (Subgroup.zpowers_le.mpr (hlin a.2))
      have hne' : fixV (Subgroup.zpowers (a : MulAut (WM K))) ≠ ⊤ := by
        intro h
        apply ha1
        apply Subtype.ext
        refine MulEquiv.ext fun X => ?_
        have hX : X ∈ fixV (Subgroup.zpowers (a : MulAut (WM K))) := by
          rw [h]
          exact Subgroup.mem_top X
        exact hX _ (Subgroup.mem_zpowers _)
      have hC := card_mul_le_of_ne_top hcl hne'
      have hC' : Nat.card ↥(fixV A) ≤ q ^ 3 := by
        have hle : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut (WM K)))) :=
          Subgroup.card_le_of_le (fixV_anti (Subgroup.zpowers_le.mpr a.2))
        have h3 : Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut (WM K)))) * q ≤ q ^ 3 * q := by
          rw [← pow_succ]
          exact hC
        exact hle.trans (Nat.le_of_mul_le_mul_right h3 (by omega))
      calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * q ^ 3 := Nat.mul_le_mul h2 hC'
        _ < q ^ 4 := hq3
    · have hBq := card_mul_card_fixV_le_of_le_img inf_le_right hBel hB
      calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * Nat.card B * Nat.card ↥(fixV B) :=
            Nat.mul_le_mul h2 hfixAB
        _ = 2 * (Nat.card B * Nat.card ↥(fixV B)) := by ring
        _ ≤ 2 * q ^ 3 := Nat.mul_le_mul_left _ hBq
        _ < q ^ 4 := hq3
  obtain ⟨a, haA, halin⟩ := Set.not_subset.mp hlin
  obtain ⟨σ, hσ⟩ := exists_isSemilin hq4 (hAN haA)
  have hσ1 : σ ≠ 1 := fun h => halin (mem_linSub.mpr (by rw [← h]; exact hσ))
  set W := fixV (A ⊓ linSub K) with hWdef
  have hW : IsKClosed W := isKClosed_fixV inf_le_right
  have hsub : fixV A ≤ W ⊓ fixV (Subgroup.zpowers a) :=
    le_inf (fixV_anti inf_le_left) (fixV_anti (Subgroup.zpowers_le.mpr haA))
  have hfix2 : Nat.card ↥(fixV A) ^ 2 ≤ Nat.card W :=
    (Nat.pow_le_pow_left (Subgroup.card_le_of_le hsub) 2).trans (card_sq_le hW hσ hσ1)
  have hA' : Nat.card A ≤ 2 * Nat.card B * n :=
    h1.trans (Nat.mul_le_mul_right _ h2)
  by_cases hB : B = ⊥
  · rw [hB, Subgroup.card_bot, mul_one] at hA'
    have hWq : Nat.card W ≤ (q ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 4 from rfl, hqdef, ← card_WM]
      exact Subgroup.card_le_card_group W
    have hCq : Nat.card ↥(fixV A) ≤ q ^ 2 :=
      (Nat.pow_le_pow_iff_left (by norm_num)).mp (hfix2.trans hWq)
    have h2n : 2 * n < q ^ 2 := by
      calc 2 * n < 2 * q := by omega
        _ ≤ q * q := Nat.mul_le_mul_right _ (by omega)
        _ = q ^ 2 := by ring
    calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * n * q ^ 2 := Nat.mul_le_mul hA' hCq
      _ < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right h2n (by positivity)
      _ = q ^ 4 := by ring
  have hBq := card_mul_card_fixV_le_of_le_img inf_le_right hBel hB
  have hBq2 := card_le_of_le_img inf_le_right hBel
  have hBlin : B ≤ A ⊓ linSub K := fun x hx => ⟨hx.1, by
    obtain ⟨g, rfl⟩ := hx.2
    exact isSemilin_rho g⟩
  have hWB : Nat.card W ≤ Nat.card ↥(fixV B) := Subgroup.card_le_of_le (fixV_anti hBlin)
  have h4n : 4 * n ^ 2 < q ^ 3 := by
    have hn2 : n ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hnq (by norm_num)
    calc 4 * n ^ 2 < 4 * q ^ 2 := Nat.mul_lt_mul_of_pos_left hn2 (by norm_num)
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq4
      _ = q ^ 3 := by ring
  have key : (Nat.card A * Nat.card ↥(fixV A)) ^ 2 < (q ^ 4) ^ 2 := by
    calc (Nat.card A * Nat.card ↥(fixV A)) ^ 2 =
          Nat.card A ^ 2 * Nat.card ↥(fixV A) ^ 2 := by ring
      _ ≤ (2 * Nat.card B * n) ^ 2 * Nat.card W :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hA' 2) hfix2
      _ ≤ (2 * Nat.card B * n) ^ 2 * Nat.card ↥(fixV B) := Nat.mul_le_mul_left _ hWB
      _ = 4 * n ^ 2 * Nat.card B * (Nat.card B * Nat.card ↥(fixV B)) := by ring
      _ ≤ 4 * n ^ 2 * q ^ 2 * q ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hBq2) hBq
      _ = 4 * n ^ 2 * (q ^ 2 * q ^ 3) := by ring
      _ < q ^ 3 * (q ^ 2 * q ^ 3) := Nat.mul_lt_mul_of_pos_right h4n (by positivity)
      _ = (q ^ 4) ^ 2 := by ring
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp key

end CFSG.Quasithin.Vol2.Ch10.C3.Om
