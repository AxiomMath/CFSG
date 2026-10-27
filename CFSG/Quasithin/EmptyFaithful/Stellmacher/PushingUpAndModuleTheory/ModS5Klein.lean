module

public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

set_option maxRecDepth 100000 in
private theorem ff_pairs : ∀ x ∈ S5SylF, ∀ y ∈ S5SylF, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
    x ≠ y → (x * y) * (x * y) = 1 →
    ({1, x, y, x * y} : Finset (Perm (Fin 5))) = S5TF ∨
      ({1, x, y, x * y} : Finset (Perm (Fin 5))) = S5ThatF := by
  unfold S5SylF S5TF S5ThatF
  decide +kernel

theorem card_S5T_eq_four : Nat.card S5T = 4 := by
  have h : S5TF.card = 4 := by unfold S5TF; decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5T_iff)

theorem card_S5That_eq_four : Nat.card S5That = 4 := by
  have h : S5ThatF.card = 4 := by unfold S5ThatF; decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

private theorem card_zpowers_of_sq {n : ℕ} {x : Perm (Fin n)} (hx1 : x ≠ 1) (hx : x * x = 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1

theorem le_syl_cases {B : Subgroup (Perm (Fin 5))} (hle : B ≤ S5Syl) (hexp : ∀ x ∈ B, x * x = 1)
    (hne : B ≠ ⊥) :
    (∃ t ∈ B, t ≠ 1 ∧ B = Subgroup.zpowers t ∧ Nat.card B = 2) ∨ B = S5T ∨ B = S5That := by
  obtain ⟨⟨x, hxB⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcardB : Nat.card B ∣ 8 := by
    rw [← card_S5Syl]
    exact Subgroup.card_dvd_of_le hle
  have hz : Nat.card (Subgroup.zpowers x) = 2 := card_zpowers_of_sq hx1' (hexp x hxB)
  have hzle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hxB
  by_cases hB2 : B ≤ Subgroup.zpowers x
  · left
    have heq : B = Subgroup.zpowers x := le_antisymm hB2 hzle
    refine ⟨x, hxB, hx1', heq, ?_⟩
    rw [heq]; exact hz
  right
  obtain ⟨y, hyB, hyx⟩ := IsConcreteLE.not_le_iff_exists.mp hB2
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hxyB : x * y ∈ B := B.mul_mem hxB hyB
  have hcase := ff_pairs x ((mem_S5Syl_iff x).mp (hle hxB)) y ((mem_S5Syl_iff y).mp (hle hyB))
    (hexp x hxB) (hexp y hyB) hx1' hy1 hxy (hexp _ hxyB)
  have hB4 : Nat.card B = 4 ∨ Nat.card B = 8 := by
    have h2 : 2 ∣ Nat.card B := by
      rw [← hz]; exact Subgroup.card_dvd_of_le hzle
    have h3 : Nat.card B ≠ 2 := by
      intro h
      have := Subgroup.card_le_of_le hzle
      have h4 : Nat.card B ≤ Nat.card (Subgroup.zpowers x) := by
        have : Nat.card (Subgroup.zpowers x) = Nat.card B := by rw [hz, h]
        omega
      have := Subgroup.eq_of_le_of_card_ge hzle h4
      exact hyx (this ▸ hyB)
    have h5 : Nat.card B ≤ 8 := Nat.le_of_dvd (by norm_num) hcardB
    have : Nat.card B ∈ ({1, 2, 4, 8} : Finset ℕ) := by
      have hd : Nat.card B ∈ Nat.divisors 8 := by simp [hcardB]
      have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rwa [this] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hxyAll : ∀ w ∈ ({1, x, y, x * y} : Finset (Perm (Fin 5))), w ∈ B := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact B.one_mem
    · exact hxB
    · exact hyB
    · exact hxyB
  rcases hB4 with h4 | h8
  · rcases hcase with h | h
    · left
      have hle' : S5T ≤ B := fun σ hσ => hxyAll σ (by rw [h]; exact (mem_S5T_iff σ).mp hσ)
      exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [card_S5T_eq_four, h4])).symm
    · right
      have hle' : S5That ≤ B := fun σ hσ =>
        hxyAll σ (by rw [h]; exact (mem_S5That_iff σ).mp hσ)
      exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [card_S5That_eq_four, h4])).symm
  · exfalso
    have hBS : B = S5Syl := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_S5Syl, h8]
    have hg : S5g ∈ B := by
      rw [hBS, mem_S5Syl_iff]
      unfold S5SylF; decide +kernel
    have := hexp _ hg
    revert this
    unfold S5g
    decide +kernel

theorem exists_conj_le_syl {B : Subgroup (Perm (Fin 5))} (hexp : ∀ x ∈ B, x * x = 1) :
    ∃ g : Perm (Fin 5), B.map (MulAut.conj g).toMonoidHom ≤ S5Syl := by
  have hp : IsPGroup 2 B := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    exact ⟨1, by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext (hexp x x.2))⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hcard : Nat.card (Q : Subgroup (Perm (Fin 5))) = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h120 : (Nat.factorial 5).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have : Nat.factorial 5 = 2 ^ 3 * 15 := by decide
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [h120]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hcard
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbQ : b ∈ (Q : Subgroup (Perm (Fin 5))) := hQ hb
  rw [hg] at hbQ
  obtain ⟨s, hs, hsb⟩ := hbQ
  have : (MulAut.conj g⁻¹).toMonoidHom b = s := by
    rw [← hsb]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hs

end CFSG.Quasithin.F53Mod
