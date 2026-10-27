module

public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts
public import CFSG.Quasithin.Background.F7TwoInvL5TwoAut
public import CFSG.GroupTheory.GL52.SylowThree

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 CFSG.Quasithin.F7Two

private theorem isPGroup_sup_zpowers_three {y z : G52} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hyz : y * z = z * y) : IsPGroup 3 ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) := by
  have hcQ : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (hyz : Commute y z) m n).eq
  let T : Subgroup G52 :=
    { carrier := {w | ∃ x ∈ Subgroup.zpowers y, ∃ v ∈ Subgroup.zpowers z, w = x * v}
      mul_mem' := by
        rintro _ _ ⟨x, hx, v, hv, rfl⟩ ⟨x', hx', v', hv', rfl⟩
        refine ⟨x * x', mul_mem hx hx', v * v', mul_mem hv hv', ?_⟩
        have h := hcQ x' hx' v hv
        calc x * v * (x' * v') = x * (v * x') * v' := by group
          _ = x * (x' * v) * v' := by rw [← h]
          _ = x * x' * (v * v') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, v, hv, rfl⟩
        refine ⟨x⁻¹, inv_mem hx, v⁻¹, inv_mem hv, ?_⟩
        have h := hcQ x⁻¹ (inv_mem hx) v⁻¹ (inv_mem hv)
        calc (x * v)⁻¹ = v⁻¹ * x⁻¹ := by group
          _ = x⁻¹ * v⁻¹ := h.symm }
  have hle : Subgroup.zpowers y ⊔ Subgroup.zpowers z ≤ T :=
    sup_le (fun x hx => ⟨x, hx, 1, one_mem _, by simp⟩) (fun v hv => ⟨1, one_mem _, v, hv, by simp⟩)
  intro w
  obtain ⟨a, ha, b, hb, hw⟩ := hle w.2
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  show (w : G52) ^ 3 = 1
  have hxa : a ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hyb : b ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hab : Commute a b := hcQ a ha b hb
  rw [hw, hab.mul_pow, hxa, hyb, one_mul]

theorem exists_sylow_zpowers_sup {y z : G52} (hy : orderOf y = 3) (hz : orderOf z = 3)
    (hyz : y * z = z * y) (hzy : z ∉ Subgroup.zpowers y) :
    ∃ Q : Sylow 3 G52, (Q : Subgroup G52) = Subgroup.zpowers y ⊔ Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hz3 : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨Q, hQ⟩ := (isPGroup_sup_zpowers_three hy3 hz3 hyz).exists_le_sylow
  have hQc : Nat.card Q = 9 := by
    rw [syl3_card_sylow Q]
  have hd1 : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) ∣ 9 := by
    rw [← hQc]
    exact Subgroup.card_dvd_of_le hQ
  have hd2 : 3 ∣ Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) := by
    rw [← hy, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers y = Subgroup.zpowers y ⊔ Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, Nat.card_zpowers, hy])
    apply hzy
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have h9 : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) = 9 := by
    have hle : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) ≤ 9 :=
      Nat.le_of_dvd (by norm_num) hd1
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) := Nat.card_pos
    interval_cases h : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) <;> omega
  exact ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ (by rw [hQc, h9])).symm⟩


private def mul5 (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j + A i 4 * B 4 j

private theorem mul5_eq (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : mul5 A B = A * B := by
  ext i j
  simp [mul5, Matrix.mul_apply, Fin.sum_univ_five, add_assoc]

private def dot5 (v w : Fin 5 → ZMod 2) : ZMod 2 :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4

private theorem dot5_eq (v w : Fin 5 → ZMod 2) : dot5 v w = dotProduct v w := by
  simp [dot5, dotProduct, Fin.sum_univ_five, add_assoc]

private def oddVecs : List (Fin 5 → ZMod 2) := [![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 1, 1], ![0, 1, 0, 0, 0], ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 0], ![1, 1, 0, 0, 1], ![1, 1, 0, 1, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 1, 1]]

private theorem mem_oddVecs : ∀ v : Fin 5 → ZMod 2, dot5 v v = 1 → v ∈ oddVecs := by
  decide +kernel

private def ordChk (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Bool :=
  let B := mul5 M M
  let C := mul5 M B
  let D := mul5 C B
  let E := mul5 D (mul5 D D)
  decide (C = 1) || decide (D = 1) || !decide (E = 1)

private theorem ordChk_spec {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : ordChk M = true)
    (h15 : M ^ 15 = 1) : M ^ 5 = 1 ∨ M ^ 3 = 1 := by
  simp only [ordChk, mul5_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  have e3 : M * (M * M) = M ^ 3 := (pow_three M).symm
  have e5 : M ^ 3 * (M * M) = M ^ 5 := by
    rw [← pow_two, ← pow_add]
  have e15 : M ^ 5 * (M ^ 5 * M ^ 5) = M ^ 15 := by
    rw [← pow_add, ← pow_add]
  rw [e3, e5, e15] at h
  rcases h with (h | h) | h
  · right; exact h
  · left; exact h
  · exact absurd h15 h

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem orthCheck :
    ∀ r0 ∈ oddVecs, ∀ r1 ∈ oddVecs, dot5 r0 r1 = 0 →
    ∀ r2 ∈ oddVecs, dot5 r0 r2 = 0 → dot5 r1 r2 = 0 →
    ∀ r3 ∈ oddVecs, dot5 r0 r3 = 0 → dot5 r1 r3 = 0 → dot5 r2 r3 = 0 →
    ∀ r4 ∈ oddVecs, dot5 r0 r4 = 0 → dot5 r1 r4 = 0 → dot5 r2 r4 = 0 → dot5 r3 r4 = 0 →
    ordChk (Matrix.of ![r0, r1, r2, r3, r4]) = true := by
  decide +kernel

private theorem orth_no15 (M : M5) (h : M.transpose * M = 1) (h' : M * M.transpose = 1) :
    M ^ 15 = 1 → M ^ 5 = 1 ∨ M ^ 3 = 1 := by
  intro h15
  have hdot : ∀ i j : Fin 5, dot5 (M i) (M j) = (1 : M5) i j := by
    intro i j
    rw [dot5_eq, ← h']
    simp [Matrix.mul_apply, dotProduct]
  have hM : M = Matrix.of ![M 0, M 1, M 2, M 3, M 4] := by
    ext i j
    fin_cases i <;> rfl
  have h0 := hdot 0 0
  have h1 := hdot 1 1
  have h2 := hdot 2 2
  have h3 := hdot 3 3
  have h4 := hdot 4 4
  have h01 := hdot 0 1
  have h02 := hdot 0 2
  have h03 := hdot 0 3
  have h04 := hdot 0 4
  have h12 := hdot 1 2
  have h13 := hdot 1 3
  have h14 := hdot 1 4
  have h23 := hdot 2 3
  have h24 := hdot 2 4
  have h34 := hdot 3 4
  simp only [Matrix.one_apply] at h0 h1 h2 h3 h4 h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  have key := orthCheck (M 0) (mem_oddVecs _ (by simpa using h0)) (M 1)
    (mem_oddVecs _ (by simpa using h1)) (by simpa using h01) (M 2)
    (mem_oddVecs _ (by simpa using h2)) (by simpa using h02) (by simpa using h12) (M 3)
    (mem_oddVecs _ (by simpa using h3)) (by simpa using h03) (by simpa using h13)
    (by simpa using h23) (M 4) (mem_oddVecs _ (by simpa using h4)) (by simpa using h04)
    (by simpa using h14) (by simpa using h24) (by simpa using h34)
  rw [← hM] at key
  exact ordChk_spec key h15

private theorem dual_fixed_no15 {g : G52} (hg : dualG g = g) (h15 : g ^ 15 = 1) :
    g ^ 5 = 1 ∨ g ^ 3 = 1 := by
  have hT : (g : M5).transpose = ((g⁻¹ : G52) : M5) := by
    have := congrArg (fun x : G52 => ((x : G52) : M5).transpose) hg
    simpa [coe_dualG, Matrix.transpose_transpose] using this.symm
  have h1 : (g : M5).transpose * (g : M5) = 1 := by
    rw [hT, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (g : M5) * (g : M5).transpose = 1 := by
    rw [hT, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h15' : (g : M5) ^ 15 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h15, Units.val_one]
  rcases orth_no15 (g : M5) h1 h2 h15' with h | h
  · left
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  · right
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])

private theorem outer_case {y₁ y₂ ρ : G52} (hy₁ : orderOf y₁ = 3) (hy₂ : orderOf y₂ = 3)
    (hc : y₁ * y₂ = y₂ * y₁) (hn : y₂ ∉ Subgroup.zpowers y₁) (hρ : orderOf ρ = 5)
    (hρc : ρ * (y₁ * y₂) = (y₁ * y₂) * ρ)
    (h₁ : dualG y₁ = y₁) (h₂ : dualG y₂ = y₂) (h₃ : dualG ρ = ρ) : False := by
  have hy₁3 : y₁ ^ 3 = 1 := by rw [← hy₁]; exact pow_orderOf_eq_one y₁
  have hy₂3 : y₂ ^ 3 = 1 := by rw [← hy₂]; exact pow_orderOf_eq_one y₂
  have hρ5 : ρ ^ 5 = 1 := by
    have := pow_orderOf_eq_one ρ
    rwa [hρ] at this
  set w := y₁ * y₂ with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, (Commute.mul_pow (hc : Commute y₁ y₂)), hy₁3, hy₂3, one_mul]
  have hw1 : w ≠ 1 := by
    intro h
    apply hn
    have : y₂ = y₁⁻¹ := by
      rw [hw] at h
      exact eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y₁)
  have hdw : dualG w = w := by rw [hw, map_mul, h₁, h₂]
  have hcomm : Commute ρ w := hρc
  have hg : dualG (ρ * w) = ρ * w := by rw [map_mul, hdw, h₃]
  have h15 : (ρ * w) ^ 15 = 1 := by
    rw [hcomm.mul_pow, show (15 : ℕ) = 5 * 3 by norm_num, pow_mul ρ, hρ5, one_pow, one_mul,
      show (5 * 3 : ℕ) = 3 * 5 by norm_num, pow_mul w 3 5, hw3, one_pow]
  have hord : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  rcases dual_fixed_no15 hg h15 with h | h
  · rw [hcomm.mul_pow, hρ5, one_mul] at h
    have h5 : orderOf w ∣ 5 := orderOf_dvd_of_pow_eq_one h
    have : orderOf w ∣ Nat.gcd 3 5 := Nat.dvd_gcd hord h5
    have h1 : orderOf w = 1 := by simpa using this
    exact hw1 (orderOf_eq_one_iff.1 h1)
  · rw [hcomm.mul_pow, hw3, mul_one] at h
    have : orderOf ρ ∣ 3 := orderOf_dvd_of_pow_eq_one h
    rw [hρ] at this
    omega


private theorem inner_case {y₁ y₂ A : G52} (hy₁ : orderOf y₁ = 3) (hy₂ : orderOf y₂ = 3)
    (hc : y₁ * y₂ = y₂ * y₁) (hn : y₂ ∉ Subgroup.zpowers y₁)
    (hA₁ : A * y₁ * A⁻¹ = y₁) (hA₂ : A * y₂ * A⁻¹ = y₂)
    (hAA : ∀ g : G52, A * (A * g * A⁻¹) * A⁻¹ = g) : MulAut.conj A = 1 := by
  obtain ⟨Q, hQ⟩ := exists_sylow_zpowers_sup hy₁ hy₂ hc hn
  obtain ⟨-, hel, hcent, -⟩ := syl3_structure Q
  have hAC : A ∈ Subgroup.centralizer (Q : Set G52) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ (Q : Subgroup G52) := hh
    rw [hQ] at hh'
    have hle : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ ≤ Subgroup.centralizer {A} := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc y₁ * A = A * y₁ * A⁻¹ * A := by rw [hA₁]
          _ = A * y₁ := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc y₂ * A = A * y₂ * A⁻¹ * A := by rw [hA₂]
          _ = A * y₂ := by group
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh')
  rw [hcent] at hAC
  have hAC' : A ∈ (Q : Subgroup G52) := hAC
  have hA3 : A ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := (Q : Subgroup G52)) A hAC'
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.conj_apply, MulAut.one_apply]
  have h2 := hAA g
  have hAinv : A⁻¹ = A * A := by
    rw [inv_eq_iff_mul_eq_one]
    calc A * (A * A) = A ^ 3 := (pow_three A).symm
      _ = 1 := hA3
  have hA2 : g * (A * A) = A * A * g := by
    calc g * (A * A) = (A * (A * g * A⁻¹) * A⁻¹) * (A * A) := by rw [h2]
      _ = A * A * g := by group
  calc A * g * A⁻¹ = A * (g * (A * A)) := by rw [hAinv]; group
    _ = A * (A * A * g) := by rw [hA2]
    _ = A ^ 3 * g := by rw [pow_three', mul_assoc, mul_assoc, mul_assoc]
    _ = g := by rw [hA3, one_mul]


theorem ff79KAutL5_holds : FF79KAutL5 := by
  intro φ hφ y₁ y₂ ρ hy₁ hy₂ hc hn hρ hρc h₁ h₂ h₃
  rcases aut_involution_L5 φ hφ with ⟨A, rfl⟩ | ⟨H, rfl⟩
  · refine inner_case hy₁ hy₂ hc hn h₁ h₂ fun g => ?_
    have := congrArg (fun ψ : MulAut G52 => ψ g) hφ
    simpa [MulAut.conj_apply] using this
  · exfalso
    set e : MulAut G52 := (MulAut.conj H).symm with he
    have hfix : ∀ x : G52, (MulAut.conj H * dualG * (MulAut.conj H)⁻¹) x = x →
        dualG (e x) = e x := by
      intro x hx
      have h' : MulAut.conj H (dualG (e x)) = x := hx
      calc dualG (e x) = e (MulAut.conj H (dualG (e x))) :=
            ((MulAut.conj H).symm_apply_apply _).symm
        _ = e x := by rw [h']
    refine outer_case (y₁ := e y₁) (y₂ := e y₂) (ρ := e ρ) ?_ ?_ ?_ ?_ ?_ ?_ (hfix _ h₁) (hfix _ h₂)
      (hfix _ h₃)
    · rw [MulEquiv.orderOf_eq]; exact hy₁
    · rw [MulEquiv.orderOf_eq]; exact hy₂
    · rw [← map_mul, ← map_mul, hc]
    · rintro ⟨k, hk⟩
      apply hn
      refine ⟨k, e.injective ?_⟩
      rw [map_zpow]
      exact hk
    · rw [MulEquiv.orderOf_eq]; exact hρ
    · have := congrArg e hρc
      simpa only [map_mul] using this

end CFSG.RankThree.PartTwo.Sec21.FF79
