module

public import CFSG.Quasithin.EmptyFaithful.S146yL3Par
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X7a Matrix

namespace CFSG.Quasithin.S15223P4.D1

local instance decEqSL3F2 : DecidableEq SL3F2 := fun a b =>
  decidable_of_iff ((a : Matrix (Fin 3) (Fin 3) (ZMod 2)) = b) Subtype.ext_iff.symm

theorem card_Q3_zero : Nat.card (Q3 (ZMod 2) 0) = 24 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun g : SL3F2 => g ∈ Q3 (ZMod 2) 0)) =
      Finset.univ.filter (fun g : SL3F2 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0) :=
    Finset.filter_congr (fun g _ => mem_Q3_zero_iff g)
  rw [h]
  decide +kernel

theorem card_Q3_one : Nat.card (Q3 (ZMod 2) 1) = 24 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun g : SL3F2 => g ∈ Q3 (ZMod 2) 1)) =
      Finset.univ.filter (fun g : SL3F2 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0) :=
    Finset.filter_congr (fun g _ => mem_Q3_one_iff g)
  rw [h]
  decide +kernel

theorem card_maxParabolic {P : Subgroup SL3F2} (hP : IsMaxParabolic2 (⊤ : Subgroup SL3F2) P) :
    Nat.card P = 24 := by
  obtain ⟨g, j, rfl⟩ := isMaxParabolic2_eq_map_Q3 hP
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  fin_cases j
  · exact card_Q3_zero
  · exact card_Q3_one

theorem eq_one_or_eq_or_eq_sq : ∀ y : SL3F2, y ^ 3 = 1 → y ≠ 1 → ∀ z : SL3F2, z * y = y * z →
    z = 1 ∨ z = y ∨ z = y ^ 2 := by
  decide +kernel

theorem mem_zpowers_of_commute {L : Type*} [Group L] (e : L ≃* SL3F2) {y : L} (hy : orderOf y = 3)
    {z : L} (hz : z * y = y * z) : z ∈ Subgroup.zpowers y := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  have h3 : (e y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have h1 : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hc : e z * e y = e y * e z := by rw [← map_mul, ← map_mul, hz]
  rcases eq_one_or_eq_or_eq_sq (e y) h3 h1 (e z) hc with h | h | h
  · have : z = 1 := e.injective (by rw [h, map_one])
    rw [this]; exact Subgroup.one_mem _
  · have : z = y := e.injective h
    rw [this]; exact Subgroup.mem_zpowers y
  · have : z = y ^ 2 := e.injective (by rw [h, map_pow])
    rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2

theorem mem_zpowers_cases {Q : Type*} [Group Q] {y : Q} (hy3 : y ^ 3 = 1) {z : Q}
    (hz : z ∈ Subgroup.zpowers y) : z = 1 ∨ z = y ∨ z = y ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h : y ^ k = y ^ (k % 3) := by
    have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
    conv_lhs => rw [hk, _root_.zpow_add, _root_.zpow_mul]
    have : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
    rw [this, _root_.one_zpow, one_mul]
  rw [h]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp [pow_two]

theorem exists_inv_of_card_24 {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 24) {y : Q}
    (hy : orderOf y = 3) (hC : ∀ z : Q, z * y = y * z → z ∈ Subgroup.zpowers y) :
    ∃ g : Q, g * y * g⁻¹ = y⁻¹ := by
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  set P : Subgroup Q := Subgroup.zpowers y with hP
  have hPcard : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hy]
  have hPQ : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hidx : P.index = 8 := by
    have := Subgroup.card_mul_index P
    rw [hPcard, hQ] at this
    omega
  let Ps : Sylow 3 Q := IsPGroup.toSylow hPQ (by rw [hidx]; norm_num)
  have hN : Subgroup.normalizer (P : Set Q) = P := by
    refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
    have hg' : g * y * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_zpowers y)
    rcases mem_zpowers_cases hy3 hg' with h | h | h
    · exact absurd (by simpa using h) hy1
    · apply hC
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h]
    · have hsq : y ^ 2 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy3)
      exact absurd (h.trans hsq) (hno g)
  have hcount : Nat.card (Sylow 3 Q) = (Subgroup.normalizer (P : Set Q)).index :=
    Sylow.card_eq_index_normalizer Ps
  have hmod := card_sylow_modEq_one 3 Q
  rw [hcount, hN, hidx] at hmod
  exact absurd hmod (by decide)

end CFSG.Quasithin.S15223P4.D1
