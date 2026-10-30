module

public import CFSG.RankThree.Literature.ThompsonDihedralProduct

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59


open DihedralGroup in
theorem dihedral4_aut_cube (ψ : DihedralGroup 4 ≃* DihedralGroup 4)
    (h3 : ∀ x, ψ (ψ (ψ x)) = x) : ∀ x, ψ x = x := by
  have key : ∀ a : DihedralGroup 4, a ^ 4 = 1 → a ^ 2 ≠ 1 → a = r 1 ∨ a = r 3 := by
    decide +kernel
  have key3 : ∀ t : ZMod 4, t + (t + t) = 0 → t = 0 := by
    decide +kernel
  have key4 : ∀ b : DihedralGroup 4, b * b = 1 →
      (∃ j : ZMod 4, b = sr j) ∨ b = r 0 ∨ b = r 2 := by
    decide +kernel
  have hpow : ∀ i : ZMod 4, (r i : DihedralGroup 4) = r 1 ^ i.val := by
    decide +kernel
  have h14 : (r 1 : DihedralGroup 4) ^ 4 = 1 := by decide +kernel
  have h4 : ψ (r 1) ^ 4 = 1 := by
    rw [← map_pow ψ, h14, map_one]
  have h2 : ψ (r 1) ^ 2 ≠ 1 := by
    rw [← map_pow ψ]
    intro h
    have h' : (r 1 : DihedralGroup 4) ^ 2 = 1 := ψ.injective (h.trans (map_one ψ).symm)
    exact absurd h' (by decide +kernel)
  have hr1 : ψ (r 1) = r 1 := by
    rcases key _ h4 h2 with h | h
    · exact h
    · exfalso
      have e1 : ψ (r 3) = r 1 := by
        rw [show (r 3 : DihedralGroup 4) = r 1 ^ 3 by decide +kernel, map_pow ψ, h]
        decide +kernel
      have h3r := h3 (r 1)
      rw [h, e1, h] at h3r
      exact absurd h3r (by decide +kernel)
  have hr : ∀ i : ZMod 4, ψ (r i) = r i := by
    intro i
    rw [hpow i, map_pow ψ, hr1]
  have hsq : ψ (sr 0) * ψ (sr 0) = 1 := by
    rw [← map_mul ψ, show (sr 0 : DihedralGroup 4) * sr 0 = 1 by decide +kernel, map_one]
  have hsr0 : ∃ j, ψ (sr 0) = sr j := by
    rcases key4 _ hsq with ⟨j, hj⟩ | hb | hb
    · exact ⟨j, hj⟩
    · exfalso
      have h0' : ψ (sr 0) = ψ 1 := by simp [hb]
      exact absurd (ψ.injective h0') (by decide +kernel)
    · exfalso
      have h2' : ψ (sr 0) = ψ (r 2) := hb.trans (hr 2).symm
      exact absurd (ψ.injective h2') (by decide +kernel)
  obtain ⟨j, hj⟩ := hsr0
  have hsr : ∀ k : ZMod 4, ψ (sr k) = sr (j + k) := by
    intro k
    have e : (sr k : DihedralGroup 4) = sr 0 * r k := by
      rw [sr_mul_r, zero_add]
    rw [e, map_mul ψ, hj, hr k, sr_mul_r]
  have hj0 : j = 0 := by
    have h' := h3 (sr 0)
    rw [hj, hsr j, hsr (j + j)] at h'
    exact key3 j (sr.inj h')
  intro x
  cases x with
  | r i => exact hr i
  | sr i => rw [hsr i, hj0, zero_add]



theorem nonempty_mulEquiv_dihedral_four {V : Type} [Group V] [Finite V]
    (hV : Nat.card V = 8) (hsq : Nat.card {v : V // v ^ 2 = 1} = 6) :
    Nonempty (V ≃* DihedralGroup 4) := by
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨H, hH⟩ : ∃ H : Subgroup V, ∀ v : V, v ∈ H ↔ v ^ 2 = 1 :=
      ⟨{ carrier := {v : V | v ^ 2 = 1}
         mul_mem' := fun {a b} ha hb => by
           have hc : Commute a b :=
             hcon a b (show a ^ 2 = 1 from ha) (show b ^ 2 = 1 from hb)
           show (a * b) ^ 2 = 1
           rw [hc.mul_pow, show a ^ 2 = 1 from ha, show b ^ 2 = 1 from hb, one_mul]
         one_mem' := by
           show (1 : V) ^ 2 = 1
           rw [one_pow]
         inv_mem' := fun {a} ha => by
           show a⁻¹ ^ 2 = 1
           rw [inv_pow, show a ^ 2 = 1 from ha, inv_one] }, fun v => Iff.rfl⟩
    have hHcard : Nat.card H = 6 :=
      (Nat.card_congr (Equiv.subtypeEquivRight hH)).trans hsq
    have hdvd := Subgroup.card_subgroup_dvd_card H
    rw [hHcard, hV] at hdvd
    omega
  have hxx : x * x = 1 := by rw [← sq]; exact hx
  have hyy : y * y = 1 := by rw [← sq]; exact hy
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hrel : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxinv, hyinv]
    calc x * (x * y) * x = (x * x) * (y * x) := by simp only [mul_assoc]
      _ = y * x := by rw [hxx, one_mul]
  have hσρ : x ∉ Subgroup.zpowers (x * y) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc0 : Commute ((x * y) ^ k) (x * y) := (Commute.refl (x * y)).zpow_left k
    rw [hk] at hc0
    apply hxy
    have hc1 : Commute x (x⁻¹ * (x * y)) := (Commute.inv_right (Commute.refl x)).mul_right hc0
    rw [inv_mul_cancel_left] at hc1
    exact hc1.eq
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup
    (ρ := x * y) (σ := x) hx hrel hσρ
  have hcard : Nat.card (Subgroup.closure ({x * y, x} : Set V)) = 2 * orderOf (x * y) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hdvd : 2 * orderOf (x * y) ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x * y, x} : Set V))
    rw [hcard, hV] at h
    exact h
  have hn4 : orderOf (x * y) = 4 := by
    have hpos : 0 < orderOf (x * y) := orderOf_pos (x * y)
    have hle : 2 * orderOf (x * y) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hn1 : orderOf (x * y) ≠ 1 := by
      intro h
      have h1 : x * y = 1 := orderOf_eq_one_iff.mp h
      have h2 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hxinv] at h2
      exact hxy (by rw [h2])
    have hn2 : orderOf (x * y) ≠ 2 := by
      intro h
      have h2 : (x * y) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (x * y)
        rwa [h] at this
      rw [sq] at h2
      have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h2
      rw [mul_inv_rev, hxinv, hyinv] at h3
      exact hxy h3.symm
    have hn3 : orderOf (x * y) ≠ 3 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    omega
  have htop : Subgroup.closure ({x * y, x} : Set V) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcard, hn4, hV])
  have eTop : V ≃* Subgroup.closure ({x * y, x} : Set V) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm
  rw [hn4] at e
  exact ⟨eTop.trans e⟩


end CFSG.RankThree.PartTwo.Sec21.FF81.S59
