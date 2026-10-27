module

public import CFSG.RankThree.PartOne.Q1327C.BU5

public section

namespace CFSG.RankThree.PartOne.Q1327C

open Matrix CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def torusVec25 (K : Type) [Field K] : Subgroup (Fin 5 → Kˣ) where
  carrier := {d | (∀ i, d i ^ 25 = 1) ∧ ∏ i, d i = 1 ∧ ∀ i j, d i ^ 5 = d j ^ 5}
  mul_mem' := fun {a b} ha hb => ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i],
    by simp [Finset.prod_mul_distrib, ha.2.1, hb.2.1],
    fun i j => by simp [mul_pow, ha.2.2 i j, hb.2.2 i j]⟩
  one_mem' := ⟨fun i => by simp, by simp, fun i j => by simp⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i],
    by simp [Finset.prod_inv_distrib, ha.2.1], fun i j => by simp [inv_pow, ha.2.2 i j]⟩

theorem torusVec_le_torusVec25 : torusVec 5 5 K ≤ torusVec25 K := by
  rintro d ⟨h1, h2⟩
  refine ⟨fun i => ?_, h2, fun i j => by rw [h1 i, h1 j]⟩
  calc d i ^ 25 = (d i ^ 5) ^ 5 := by rw [← pow_mul]
    _ = 1 := by rw [h1 i]; simp

theorem torusVec25_le_torusVec : torusVec25 K ≤ torusVec 25 5 K :=
  fun _ hd => ⟨hd.1, hd.2.1⟩

@[expose] def lift5 (ξ : Kˣ) : Fin 5 → Kˣ := ![ξ, ξ, ξ, ξ, (ξ ^ 4)⁻¹]

theorem lift5_mem {ξ : Kˣ} (hξ : orderOf ξ = 25) : lift5 ξ ∈ torusVec25 K := by
  have h25 : ξ ^ 25 = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
  have h4 : ((ξ ^ 4)⁻¹) ^ 25 = 1 := by
    calc ((ξ ^ 4)⁻¹) ^ 25 = (ξ ^ 25)⁻¹ ^ 4 := by group
      _ = 1 := by rw [h25]; simp
  have h5 : ((ξ ^ 4)⁻¹) ^ 5 = ξ ^ 5 := by
    calc ((ξ ^ 4)⁻¹) ^ 5 = ξ ^ 5 * (ξ ^ 25)⁻¹ := by group
      _ = ξ ^ 5 := by rw [h25]; simp
  have hval : ∀ i : Fin 5, lift5 (K := K) ξ i = ξ ∨ lift5 (K := K) ξ i = (ξ ^ 4)⁻¹ := by
    intro i
    fin_cases i <;> simp [lift5]
  refine ⟨fun i => ?_, ?_, fun i j => ?_⟩
  · rcases hval i with h | h <;> rw [h]
    · exact h25
    · exact h4
  · simp only [lift5, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_eq_empty, Finset.prod_empty, Matrix.cons_val_fin_one]
    group
  · rcases hval i with hi | hi <;> rcases hval j with hj | hj <;> rw [hi, hj] <;>
      first | rfl | exact h5 | exact h5.symm

theorem lift5_not_mem {ξ : Kˣ} (hξ : orderOf ξ = 25) : lift5 ξ ∉ torusVec 5 5 K := by
  intro h
  have h1 := h.1 0
  simp only [lift5, Matrix.cons_val_zero] at h1
  have := orderOf_dvd_of_pow_eq_one h1
  rw [hξ] at this
  omega

theorem torusVec_lt_torusVec25 {ξ : Kˣ} (hξ : orderOf ξ = 25) :
    torusVec 5 5 K < torusVec25 K :=
  lt_of_le_of_ne torusVec_le_torusVec25 fun h => lift5_not_mem hξ (h ▸ lift5_mem hξ)

theorem pow_four_le_card_torusVec [Finite K] (hrK : 5 ∣ Nat.card Kˣ) :
    5 ^ 4 ≤ Nat.card (torusVec 5 5 K) := by
  have h1 := pow_four_le_card_torusSU (K := K) Nat.prime_five hrK
  rwa [torusSU, Subgroup.card_map_of_injective diagU_injective] at h1

theorem pow_four_lt_card_torusVec25 [Finite K] (hrK : 5 ∣ Nat.card Kˣ) {ξ : Kˣ}
    (hξ : orderOf ξ = 25) : 5 ^ 4 < Nat.card (torusVec25 K) := by
  have h1 := pow_four_le_card_torusVec hrK
  have h2 : Nat.card (torusVec 5 5 K) < Nat.card (torusVec25 K) := by
    by_contra hnot
    exact (torusVec_lt_torusVec25 hξ).ne
      (Subgroup.eq_of_le_of_card_ge torusVec_le_torusVec25 (not_lt.1 hnot))
  omega

theorem diagU_pow_five_mem_scalars {d : Fin 5 → Kˣ} (hd : ∀ i j, d i ^ 5 = d j ^ 5) :
    (diagU d : GL (Fin 5) K) ^ 5 ∈ StatedScalars (Fin 5) K := by
  rw [diagU_pow]
  refine ⟨d 0 ^ 5, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  have : (d ^ 5 : Fin 5 → Kˣ) = fun _ => d 0 ^ 5 := funext fun i => hd i 0
  rw [this, diagU_val]
  simp [Matrix.scalar_apply]

theorem scalar_eq_diagU (c : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) = diagU (fun _ => c) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, diagU_val]
  simp [Matrix.scalar_apply]

end CFSG.RankThree.PartOne.Q1327C
