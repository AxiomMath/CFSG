module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcChain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcDefs

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem abel_sq_eq_one (h : IsTutteSys s r l ξ Hs) {i k : ℕ} (hi : i < s) (hab : Abel Hs i)
    (hk : 1 ≤ k) (hki : k ≤ i) : tx r l k ^ 2 = 1 := by
  have key : ∀ n : ℕ, n + 1 ≤ i →
      tx r l (n : ℤ) ^ 2 = 1 ∧ tx r l ((n + 1 : ℕ) : ℤ) ^ 2 = 1 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨by simp [tx_zero], ?_⟩
      have := tx_sq_mem h (k := 1) le_rfl (by omega)
      simpa [h.zero] using this
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2, ?_⟩
      have mem : ∀ m : ℕ, m ≤ i → tx r l (m : ℤ) ∈ Hs i := fun m hm =>
        tx_mem_of_le h hm hi.le
      have hxn := mem (n + 1) (by omega)
      have hxm := mem (n + 1 + 1) hn
      have hinv1 : (tx r l (n : ℤ))⁻¹ = tx r l (n : ℤ) :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h1)
      have hinv2 : (tx r l ((n + 1 : ℕ) : ℤ))⁻¹ = tx r l ((n + 1 : ℕ) : ℤ) :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h2)
      have hA : tx r l ((n + 1 : ℕ) : ℤ) * (tx r l (n : ℤ))⁻¹ =
          tx r l (n : ℤ) * (tx r l ((n + 1 : ℕ) : ℤ))⁻¹ := by
        rw [hinv1, hinv2]
        exact hab _ hxn _ (mem n (by omega))
      have s1 := tx_shift_l r l ((n + 1 : ℕ) : ℤ) (n : ℤ) 1
      have s2 := tx_shift_l r l (n : ℤ) ((n + 1 : ℕ) : ℤ) 1
      rw [hA] at s1
      have e1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e2, e1] at s1
      rw [e1, e2] at s2
      have hB : tx r l ((n + 1 + 1 : ℕ) : ℤ) * (tx r l ((n + 1 : ℕ) : ℤ))⁻¹ =
          tx r l ((n + 1 : ℕ) : ℤ) * (tx r l ((n + 1 + 1 : ℕ) : ℤ))⁻¹ := by
        rw [← s1, s2]
      have hC : tx r l ((n + 1 : ℕ) : ℤ) * (tx r l ((n + 1 + 1 : ℕ) : ℤ))⁻¹ =
          (tx r l ((n + 1 + 1 : ℕ) : ℤ))⁻¹ * tx r l ((n + 1 : ℕ) : ℤ) :=
        hab _ hxn _ (Subgroup.inv_mem _ hxm)
      rw [hC, hinv2] at hB
      have hD := mul_right_cancel hB
      rw [pow_two]
      exact (inv_eq_iff_mul_eq_one.mp hD.symm)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact (key n hki).2

theorem abelian_iff (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : i < s) :
    Abel Hs i ↔ ∀ k : ℕ, 1 ≤ k → k ≤ i → tx r l k ^ 2 = 1 := by
  have _ : 1 ≤ i := hi
  refine ⟨fun hab k hk hki => abel_sq_eq_one h his hab hk hki, fun hsq => ?_⟩
  have hcomm : ∀ j k : ℕ, 1 ≤ j → j < k → k ≤ i →
      tx r l (k : ℤ) * tx r l (j : ℤ) = tx r l (j : ℤ) * tx r l (k : ℤ) := by
    intro j k hj hjk hki
    have hd : tx r l ((k - j : ℕ) : ℤ) ^ 2 = 1 := hsq (k - j) (by omega) (by omega)
    have hsh := tx_shift_l r l ((k - j : ℕ) : ℤ) 0 (j : ℤ)
    have e : ((k - j : ℕ) : ℤ) + (j : ℤ) = (k : ℤ) := by omega
    rw [tx_zero, inv_one, mul_one, zero_add, e] at hsh
    have hsqk : (tx r l (k : ℤ) * (tx r l (j : ℤ))⁻¹) *
        (tx r l (k : ℤ) * (tx r l (j : ℤ))⁻¹) = 1 := by
      have conj_sq : ∀ x : H,
          (l ^ (-(j : ℤ)) * x * l ^ (j : ℤ)) * (l ^ (-(j : ℤ)) * x * l ^ (j : ℤ)) =
            l ^ (-(j : ℤ)) * (x * x) * l ^ (j : ℤ) := fun x => by group
      rw [← hsh, conj_sq, ← pow_two, hd]
      group
    have hkinv : (tx r l (k : ℤ))⁻¹ = tx r l (k : ℤ) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq k (by omega) hki)
    have hjinv : (tx r l (j : ℤ))⁻¹ = tx r l (j : ℤ) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq j hj (by omega))
    rw [hjinv] at hsqk
    have := inv_eq_of_mul_eq_one_right hsqk
    rw [mul_inv_rev, hkinv, hjinv] at this
    exact this.symm
  set S : Set H := {g | ∃ k : ℕ, 1 ≤ k ∧ k ≤ i ∧ g = tx r l k} with hS
  have hgen : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a ⟨p, hp1, hpi, rfl⟩ b ⟨q, hq1, hqi, rfl⟩
    rcases lt_trichotomy p q with hpq | rfl | hqp
    · exact (hcomm p q hp1 hpq hqi).symm
    · rfl
    · exact hcomm q p hq1 hqp hpi
  intro a ha b hb
  rw [Hs_eq_closure h his.le] at ha hb
  have ha' : a ∈ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      hgen y hy x hx) ha
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.closure_le_centralizer_centralizer S hb) a ha'

end CFSG.Quasithin.Fan86.Tutte
