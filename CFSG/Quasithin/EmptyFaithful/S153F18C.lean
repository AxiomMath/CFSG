module

public import CFSG.Quasithin.EmptyFaithful.S153F18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace S153F

theorem sl2_sq_eq_one_of_fixed {F : Type} [Field F] (h2 : (2 : F) = 0)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) (hw : w ≠ 0)
    (hM : (M : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : M ^ 2 = 1 := by
  have hdet : ((M : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨w, hw, ?_⟩
    rw [Matrix.sub_mulVec, hM, Matrix.one_mulVec, sub_self]
  have hM1 : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  rw [Matrix.det_fin_two] at hdet hM1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    OfNat.ofNat_ne_one, not_false_eq_true, sub_zero, zero_ne_one, Fin.one_eq_zero_iff] at hdet
  have h1 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 + (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    linear_combination hM1 - hdet + h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 0 0 * h1 - hM1 - h2
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 0 1 * h1
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 1 0 * h1
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 1 1 * h1 - hM1 - h2

theorem lin2NatFixedPoints_proved : Lin2NatFixedPoints := by
  intro G _ _ L n hL y hy hyo hy1 a ha hya
  obtain ⟨F, hF, hFin, hcard, α, -, hαk, β, -, hβk, heq⟩ := hL
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hcard] at this
    simp at this
  have h2 : (2 : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    push_cast at h0
    exact (pow_eq_zero_iff hn0).mp h0
  let ℓ : ↥L := ⟨y, hy⟩
  let u : ↥(blockU L) := ⟨a, ha⟩
  have hv : (u : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ := hya.symm
  have hw := heq ℓ u u hv
  have hβ : β u = 1 := by
    by_contra hne
    have hw0 : Multiplicative.toAdd (β u) ≠ 0 := fun h =>
      hne (Multiplicative.toAdd.injective (by simpa using h))
    have hsq := sl2_sq_eq_one_of_fixed h2 (α ℓ) _ hw0 hw.symm
    have hd1 : orderOf (α ℓ) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hd2 : orderOf (α ℓ) ∣ orderOf y := by
      have := orderOf_map_dvd α ℓ
      rwa [Subgroup.orderOf_mk y hy] at this
    have hodd : Odd (orderOf (α ℓ)) := Odd.of_dvd_nat hyo hd2
    have hk : orderOf (α ℓ) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have hα1 : α ℓ = 1 := orderOf_eq_one_iff.mp hk
    have hℓ : ℓ ∈ CFSG.pCore 2 ↥L := hαk ▸ MonoidHom.mem_ker.mpr hα1
    obtain ⟨k, hk2⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨ℓ, hℓ⟩
    have hpow : ℓ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk2
    have hdy : orderOf y ∣ 2 ^ k := by
      have := orderOf_dvd_of_pow_eq_one hpow
      rwa [Subgroup.orderOf_mk y hy] at this
    have hcop : Nat.Coprime (orderOf y) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hyo)
    exact hy1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdy))
  have hu : u ∈ β.ker := MonoidHom.mem_ker.mpr hβ
  rw [hβk] at hu
  exact (Subgroup.mem_subgroupOf.mp hu).2

end S153F

end CFSG.Quasithin
