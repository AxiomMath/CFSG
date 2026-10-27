module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.He8

open CFSG.Open

section E27

variable {Q : Type} [Group Q] [Finite Q]

theorem three_le_pRank_of_central {A : Subgroup Q} {z : Q}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : Nat.card A = 9) (hz3 : z ^ 3 = 1) (hzA : z ∉ A)
    (hzc : ∀ a ∈ A, a * z = z * a) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  classical
  have hzk : ∀ a ∈ A, ∀ k : ℤ, Commute a (z ^ k) := fun a ha k => Commute.zpow_right (hzc a ha) k
  let E : Subgroup Q :=
    { carrier := {x | ∃ a ∈ A, ∃ k : ℤ, x = a * z ^ k}
      mul_mem' := by
        rintro x y ⟨a, ha, i, rfl⟩ ⟨b, hb, j, rfl⟩
        refine ⟨a * b, A.mul_mem ha hb, i + j, ?_⟩
        have hc : Commute (z ^ i) b := (hzk b hb i).symm
        rw [zpow_add]
        calc a * z ^ i * (b * z ^ j) = a * (z ^ i * b) * z ^ j := by group
          _ = a * (b * z ^ i) * z ^ j := by rw [hc.eq]
          _ = a * b * (z ^ i * z ^ j) := by group
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨a, ha, i, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, -i, ?_⟩
        rw [mul_inv_rev, ← zpow_neg]
        exact (hzk a⁻¹ (A.inv_mem ha) (-i)).eq.symm }
  have hmem : ∀ x ∈ E, ∃ a ∈ A, ∃ k : ℤ, x = a * z ^ k := fun x hx => hx
  have hcomm : IsMulCommutative E := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha, i, hx⟩ := hmem x x.2
    obtain ⟨b, hb, j, hy⟩ := hmem y y.2
    apply Subtype.ext
    change (x : Q) * y = y * x
    rw [hx, hy]
    have h1 : Commute (z ^ i) b := Commute.zpow_left (show Commute z b from (hzc b hb).symm) i
    have h2 : Commute (z ^ j) a := Commute.zpow_left (show Commute z a from (hzc a ha).symm) j
    have h3 : Commute (z ^ i) (z ^ j) := (Commute.refl z).zpow_zpow i j
    calc a * z ^ i * (b * z ^ j) = a * (z ^ i * b) * z ^ j := by group
      _ = a * (b * z ^ i) * z ^ j := by rw [h1.eq]
      _ = a * b * (z ^ i * z ^ j) := by group
      _ = b * a * (z ^ j * z ^ i) := by rw [hAcomm a ha b hb, h3.eq]
      _ = b * (a * z ^ j) * z ^ i := by group
      _ = b * (z ^ j * a) * z ^ i := by rw [h2.eq]
      _ = b * z ^ j * (a * z ^ i) := by group
  have hpow : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, i, rfl⟩ := hmem x hx
    have hc : Commute a (z ^ i) := Commute.zpow_right (hzc a ha) i
    rw [hc.mul_pow, hA3 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hz3, one_zpow]
  have hEel : IsElemAbelian 3 E := ⟨hcomm, hpow⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by
    have := hpow x x.2
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hE3
  have hAE : A < E := by
    have hle : A ≤ E := fun a ha => ⟨a, ha, 0, by simp⟩
    refine lt_of_le_of_ne hle fun h => hzA ?_
    rw [h]
    exact ⟨1, A.one_mem, 1, by simp⟩
  have hlt : Nat.card A < Nat.card E := Subgroup.card_lt_of_lt hAE
  rw [hAcard, hm] at hlt
  have hm3 : 3 ≤ m := by
    by_contra hcon
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hm3.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hEel hm)

end E27

end CFSG.Quasithin.He8
