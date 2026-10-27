module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcShift
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem Hs_mono (h : IsTutteSys s r l ξ Hs) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ s) :
    Hs i ≤ Hs j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (h.mono j (by omega))

theorem finite_Hs (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i ≤ s) : Finite (Hs i) := by
  refine Nat.finite_of_card_ne_zero ?_
  rcases Nat.lt_or_ge i s with hlt | hge
  · rw [h.card_lt i hlt]
    exact (Nat.two_pow_pos i).ne'
  · obtain rfl : i = s := le_antisymm hi hge
    rw [h.card_s]
    have := Nat.two_pow_pos (i - 1)
    omega

theorem tx_mem_of_le (h : IsTutteSys s r l ξ Hs) {k i : ℕ} (hk : k ≤ i) (hi : i ≤ s) :
    tx r l k ∈ Hs i :=
  Hs_mono h hk hi (h.x_mem k (hk.trans hi))

theorem Hs_eq_closure (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i ≤ s) :
    Hs i = Subgroup.closure {g | ∃ k : ℕ, 1 ≤ k ∧ k ≤ i ∧ g = tx r l k} := by
  induction i with
  | zero =>
    rw [h.zero]
    have : {g : H | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 0 ∧ g = tx r l k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun g ⟨k, hk1, hk0, _⟩ => by omega
    rw [this, Subgroup.closure_empty]
  | succ i ih =>
    have ih' := ih (by omega)
    set C : Subgroup H := Subgroup.closure {g | ∃ k : ℕ, 1 ≤ k ∧ k ≤ i + 1 ∧ g = tx r l k} with hC
    have hfin : Finite (Hs (i + 1)) := finite_Hs h hi
    have hCle : C ≤ Hs (i + 1) := by
      rw [hC, Subgroup.closure_le]
      rintro g ⟨k, -, hk, rfl⟩
      exact tx_mem_of_le h hk hi
    have hHC : Hs i ≤ C := by
      rw [ih']
      exact Subgroup.closure_mono fun g ⟨k, hk1, hk, hg⟩ => ⟨k, hk1, by omega, hg⟩
    have hxC : tx r l (i + 1) ∈ C :=
      Subgroup.subset_closure ⟨i + 1, by omega, le_rfl, rfl⟩
    have hxn : tx r l (i + 1) ∉ Hs i := by
      simpa using h.x_not_mem (i + 1) (by omega) hi
    have hfinC : Finite C := Finite.of_injective _ (Subgroup.inclusion_injective hCle)
    obtain ⟨p, hp, hcard⟩ : ∃ p : ℕ, p.Prime ∧ Nat.card (Hs (i + 1)) = p * Nat.card (Hs i) := by
      rcases Nat.lt_or_ge (i + 1) s with hlt | hge
      · exact ⟨2, Nat.prime_two, by
          rw [h.card_lt (i + 1) hlt, h.card_lt i (by omega), pow_succ, mul_comm]⟩
      · obtain rfl : i + 1 = s := le_antisymm hi hge
        exact ⟨3, Nat.prime_three, by
          rw [h.card_s, h.card_lt i (by omega)]
          simp⟩
    have hfini : Finite (Hs i) := finite_Hs h (by omega)
    have hpos : 0 < Nat.card (Hs i) := Nat.card_pos
    have hlt : Nat.card (Hs i) < Nat.card C := by
      by_contra hle
      have heq := Subgroup.eq_of_le_of_card_ge hHC (not_lt.mp hle)
      exact hxn (heq ▸ hxC)
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHC
    have hdvd : Nat.card C ∣ Nat.card (Hs (i + 1)) := Subgroup.card_dvd_of_le hCle
    rw [hm, hcard, mul_comm p] at hdvd
    have hmp : m ∣ p := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
    rcases (Nat.dvd_prime hp).mp hmp with rfl | rfl
    · rw [hm, mul_one] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact (Subgroup.eq_of_le_of_card_ge hCle (by rw [hcard, hm, mul_comm])).symm

theorem inv_mul_mem_of_not_mem (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : k + 1 < s) {a b : H}
    (ha : a ∈ Hs (k + 1)) (hb : b ∈ Hs (k + 1)) (ha' : a ∉ Hs k) (hb' : b ∉ Hs k) :
    a⁻¹ * b ∈ Hs k := by
  have hle : Hs k ≤ Hs (k + 1) := h.mono k (by omega)
  have hidx : ((Hs k).subgroupOf (Hs (k + 1))).index = 2 := by
    have e := Subgroup.relIndex_mul_card (H := Hs k) (K := Hs (k + 1))
    rw [inf_of_le_left hle, h.card_lt (k + 1) hk, h.card_lt k (by omega), pow_succ] at e
    have e2 : (Hs k).relIndex (Hs (k + 1)) * 2 ^ k = 2 * 2 ^ k := by rw [e, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos k) e2
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : Hs (k + 1))⁻¹)
    (b := ⟨b, hb⟩)).mpr (by
      rw [inv_mem_iff]
      exact ⟨fun h1 => absurd h1 ha', fun h2 => absurd h2 hb'⟩)
  exact hmem

theorem tx_sq_mem (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : 1 ≤ k) (hks : k < s) :
    tx r l k ^ 2 ∈ Hs (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hx : tx r l (m + 1) ∈ Hs (m + 1) := h.x_mem (m + 1) hks.le
  have hnx : tx r l (m + 1) ∉ Hs m := by
    simpa using h.x_not_mem (m + 1) hk hks.le
  have hnx' : (tx r l (m + 1))⁻¹ ∉ Hs m := fun hmem => hnx (by simpa using (Hs m).inv_mem hmem)
  have := inv_mul_mem_of_not_mem h hks ((Hs (m + 1)).inv_mem hx) hx hnx' hnx
  simpa [sq] using this

theorem shift_mem (h : IsTutteSys s r l ξ Hs) {c j : ℕ} (hcj : c + j ≤ s) {g : H}
    (hg : g ∈ Hs c) : r ^ (-(j : ℤ)) * g * r ^ (j : ℤ) ∈ Hs (c + j) := by
  have key : Hs c ≤ (Hs (c + j)).comap (MulAut.conj (r ^ (-(j : ℤ)))).toMonoidHom := by
    rw [Hs_eq_closure h (by omega : c ≤ s), Subgroup.closure_le]
    rintro g ⟨k, hk1, hkc, rfl⟩
    have e := tx_shift r l 0 k j
    rw [tx_zero, inv_one, one_mul] at e
    show r ^ (-(j : ℤ)) * tx r l k * (r ^ (-(j : ℤ)))⁻¹ ∈ Hs (c + j)
    simp only [zpow_neg, inv_inv, zero_add] at e ⊢
    rw [e]
    have e1 : tx r l (j : ℤ) ∈ Hs (c + j) := tx_mem_of_le h (by omega) hcj
    have e2 : tx r l ((k : ℤ) + (j : ℤ)) ∈ Hs (c + j) := by
      have := tx_mem_of_le h (k := k + j) (i := c + j) (by omega) hcj
      simpa using this
    exact (Hs (c + j)).mul_mem ((Hs (c + j)).inv_mem e1) e2
  have h1 := Subgroup.mem_comap.mp (key hg)
  have e : (MulAut.conj (r ^ (-(j : ℤ)))).toMonoidHom g = r ^ (-(j : ℤ)) * g * r ^ (j : ℤ) := by
    show r ^ (-(j : ℤ)) * g * (r ^ (-(j : ℤ)))⁻¹ = _
    simp only [zpow_neg, inv_inv]
  rwa [e] at h1

end CFSG.Quasithin.Fan86.Tutte
