module

public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenNum
public import CFSG.Quasithin.Vol2.GoldschmidtSevenKernel
public import CFSG.Quasithin.Vol2.GoldschmidtSevenFrattini
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.Quasithin.J4Seven

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem not_inverting_pow
    (hM : MatFacts) {k : ℕ} (hk : k ∈ List.range' 1 6) {g : J} (hg : g ∈ Hj) :
    g * sevenElt ^ k * g⁻¹ ≠ (sevenElt ^ k)⁻¹ := by
  intro hinv
  have hnorm : ∀ e ∈ Eg uJ 11, g * e * g⁻¹ ∈ Eg uJ 11 := Hj_normalizes_Eg hM g hg
  have hnorm' : ∀ e ∈ Eg uJ 11, g⁻¹ * e * g ∈ Eg uJ 11 := fun e he => by
    simpa using Hj_normalizes_Eg hM g⁻¹ (Hj.inv_mem hg) e he
  have hcomm : ∀ a ∈ Eg uJ 11, ∀ b ∈ Eg uJ 11, a * b = b * a := fun a ha b hb =>
    Eg_comm (elem_uJ hM) ha hb
  have hB : ∀ n : ℕ, ∀ e ∈ Eg uJ 11, (sevenElt ^ k) ^ n * e * ((sevenElt ^ k) ^ n)⁻¹ ∈
      Eg uJ 11 := by
    intro n e he
    rw [← pow_mul]
    exact sevenElt_pow_mem hM (k * n) he
  have h := CFSG.Quasithin.H13.Seven.ncard_kernel_eq (E := Eg uJ 11) hcomm hB hnorm hnorm' hinv
  simp only [← pow_mul] at h
  rw [ncard_kerSet hM (k * 3) k, ncard_kerSet hM (k * 3) (k * 2)] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11⟩ := chkSeven_parts
  exact h11 k hk h

theorem Hj_not_real
    (hM : MatFacts) (h49 : ¬ 49 ∣ Nat.card J) {y g : J} (hy : y ∈ Hj) (hg : g ∈ Hj)
    (hord : orderOf y = 7) : g * y * g⁻¹ ≠ y⁻¹ := by
  intro hinv
  have hx7 : orderOf sevenElt = 7 := orderOf_sevenElt hM
  obtain ⟨h, hh, hconj⟩ := CFSG.Quasithin.H13.Seven.exists_conj_of_card_seven h49
    (M := Hj) (S := Subgroup.zpowers sevenElt) (S' := Subgroup.zpowers y)
    (Subgroup.zpowers_le.2 sevenElt_mem_Hj) (Subgroup.zpowers_le.2 hy)
    (by rw [Nat.card_zpowers, hx7]) (by rw [Nat.card_zpowers, hord])
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hconj y (Subgroup.mem_zpowers y))
  have hy1 : h * y * h⁻¹ ≠ 1 := by
    intro h1
    have : y = 1 := by
      have := congrArg (fun z => h⁻¹ * z * h) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hord
    omega
  have hinv1 : (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ = (h * y * h⁻¹)⁻¹ := by
    calc (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ = h * (g * y * g⁻¹) * h⁻¹ := by group
      _ = h * y⁻¹ * h⁻¹ := by rw [hinv]
      _ = (h * y * h⁻¹)⁻¹ := by group
  have hg1 : h * g * h⁻¹ ∈ Hj := Hj.mul_mem (Hj.mul_mem hh hg) (Hj.inv_mem hh)
  have hm7 : (orderOf sevenElt : ℤ) = 7 := by rw [hx7]; rfl
  set k : ℕ := (m % 7).toNat with hkdef
  have hmod0 : 0 ≤ m % 7 := Int.emod_nonneg _ (by norm_num)
  have hmod7 : m % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
  have hkm : ((k : ℕ) : ℤ) = m % 7 := Int.toNat_of_nonneg hmod0
  have hxk : sevenElt ^ k = h * y * h⁻¹ := by
    rw [← hm, ← zpow_natCast, hkm, ← hm7, zpow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk, pow_zero] at hxk
    exact hy1 hxk.symm
  have hk : k ∈ List.range' 1 6 := by
    rw [List.mem_range'_1]
    omega
  refine not_inverting_pow hM hk hg1 ?_
  rw [hxk]
  exact hinv1

end CFSG.Quasithin.J4Seven
