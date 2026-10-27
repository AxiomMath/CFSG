module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD4

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

theorem form_act_trv (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) (u x : Fin 4 → k) :
    Q (natAct (trv u 1) x) = Q x + spBil x u ^ 2 * (Q u + 1) := by
  rw [act_trv, one_mul]
  have h := hQ x (spBil x u • u)
  rw [QuadraticMap.polar, LinearMap.map_smul (spBil x), smul_eq_mul] at h
  have h' : Q (spBil x u • u) = spBil x u * spBil x u * Q u := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
  linear_combination h + h'

theorem form_act_trv_of_eq_one (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {u : Fin 4 → k} (hu : Q u = 1)
    (x : Fin 4 → k) : Q (natAct (trv u 1) x) = Q x := by
  rw [form_act_trv Q hQ, hu]
  linear_combination spBil x u ^ 2 * (CharTwo.two_eq_zero : (2 : k) = 0)

theorem eq_one_of_form_act_trv (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {u : Fin 4 → k} (hu : u ≠ 0)
    (h : ∀ x, Q (natAct (trv u 1) x) = Q x) : Q u = 1 := by
  obtain ⟨x, hx⟩ := exists_bil_ne_zero hu
  have h1 := h x
  rw [form_act_trv Q hQ] at h1
  have h0 : spBil x u ^ 2 * (Q u + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h0 with h2 | h2
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h2) hx
  · linear_combination h2 - (CharTwo.two_eq_zero : (2 : k) = 0)

theorem eq_one_of_conj_inv (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {c₀ : antiSp k}
    (hc₀ : ∀ x, Q (natAct c₀ x) = Q x) {p : Fin 4 → k} (hfix : natAct c₀ p ≠ p)
    (hconj : trv p 1 * c₀ * trv p 1 = c₀⁻¹) : Q p = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hinv : ∀ x, Q (natAct c₀⁻¹ x) = Q x := fun x => by
    rw [← hc₀ (natAct c₀⁻¹ x), act_act_inv]
  have hcomm : c₀⁻¹ * trv p 1 = trv p 1 * c₀ := by
    rw [← hconj, mul_assoc _ (trv p 1), trv_mul_self, mul_one]
  by_contra hne
  have hκ : Q p + 1 ≠ 0 := fun h => hne (by linear_combination h - h2)
  have key : ∀ x, spBil (natAct c₀ x) p = spBil x p := by
    intro x
    have e : natAct (trv p 1) (natAct c₀ x) = natAct c₀⁻¹ (natAct (trv p 1) x) := by
      rw [← natAct_mul, ← natAct_mul, hcomm]
    have h1 := congrArg Q e
    rw [form_act_trv Q hQ, hinv, form_act_trv Q hQ, hc₀] at h1
    have h3 : (spBil (natAct c₀ x) p ^ 2 - spBil x p ^ 2) * (Q p + 1) = 0 := by
      linear_combination h1
    have h4 := (mul_eq_zero.mp h3).resolve_right hκ
    have h5 : (spBil (natAct c₀ x) p - spBil x p) ^ 2 = 0 := by
      linear_combination h4 + (spBil x p ^ 2 - spBil (natAct c₀ x) p * spBil x p) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h5)
  have hq : natAct c₀⁻¹ p = p := by
    have h0 : natAct c₀⁻¹ p - p = 0 := by
      apply eq_zero_of_bil_eq_zero
      intro x
      rw [map_sub, sub_eq_zero, ← key x]
      have h := bil_act c₀⁻¹ (natAct c₀ x) p
      rw [act_inv_act] at h
      exact h
    exact sub_eq_zero.mp h0
  apply hfix
  calc natAct c₀ p = natAct c₀ (natAct c₀⁻¹ p) := by rw [hq]
    _ = p := act_act_inv c₀ p

theorem act_ne_self {u₁ u₂ p : Fin 4 → k} (hu₁ : u₁ 1 = 0 ∧ u₁ 2 = 0)
    (hu₂ : u₂ 1 = 0 ∧ u₂ 2 = 0) (hp : p 1 = 0 ∧ p 2 = 0) (hc : spBil u₁ u₂ ≠ 0) (hp0 : p ≠ 0) :
    natAct (trv u₁ 1 * trv u₂ 1) p ≠ p := by
  intro h
  have e : natAct (trv u₂ 1) p = natAct (trv u₁ 1) p := by
    rw [natAct_mul] at h
    calc natAct (trv u₂ 1) p
        = natAct (trv u₁ 1) (natAct (trv u₁ 1) (natAct (trv u₂ 1) p)) := by
          rw [← natAct_mul, trv_mul_self, natAct_one]
      _ = natAct (trv u₁ 1) p := by rw [h]
  rw [act_trv, act_trv, one_mul, one_mul, add_right_inj] at e
  have e1 := congrArg (spBil u₁) e
  have e2 := congrArg (spBil u₂) e
  simp only [map_smul, smul_eq_mul, bil_self, mul_zero] at e1 e2
  have hc' : spBil u₂ u₁ ≠ 0 := by rwa [bil_symm]
  have hpu₂ : spBil p u₂ = 0 := (mul_eq_zero.mp e1).resolve_right hc
  have hpu₁ : spBil p u₁ = 0 := (mul_eq_zero.mp e2.symm).resolve_right hc'
  apply hp0
  have hw : spBil u₁ ((spBil u₁ u₂)⁻¹ • u₂) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]
  have hd := eq_bil_smul_add hu₁ (by simp [hu₂.1, hu₂.2]) hp hw
  rw [hd, LinearMap.map_smul₂, bil_symm u₂ p, hpu₂, bil_symm u₁ p, hpu₁]
  simp

theorem dihedral_sr_of_sq {z : ℕ} (hz : Odd z) {g : DihedralGroup z} (hg : g ^ 2 = 1)
    (hg1 : g ≠ 1) : ∃ i, g = DihedralGroup.sr i := by
  rcases g with i | i
  · exfalso
    apply hg1
    rw [sq, DihedralGroup.r_mul_r, DihedralGroup.one_def] at hg
    have h2 : i + i = 0 := DihedralGroup.r.inj hg
    obtain ⟨m, rfl⟩ := hz
    have hu : ((m + 1 : ℕ) : ZMod (2 * m + 1)) * 2 = 1 := by
      have h0 : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self _
      push_cast at h0 ⊢
      linear_combination h0
    have hi : i = 0 := by
      calc i = ((m + 1 : ℕ) : ZMod (2 * m + 1)) * 2 * i := by rw [hu, one_mul]
        _ = ((m + 1 : ℕ) : ZMod (2 * m + 1)) * (i + i) := by ring
        _ = 0 := by rw [h2, mul_zero]
    rw [hi, DihedralGroup.r_zero]
  · exact ⟨i, rfl⟩

theorem dihedral_conj_inv {z : ℕ} (hz : Odd z) {H : Type*} [Group H] (φ : H ≃* DihedralGroup z)
    {s a b : H} (hs : s ^ 2 = 1) (hs1 : s ≠ 1) (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1)
    (hb1 : b ≠ 1) : s * (a * b) * s = (a * b)⁻¹ := by
  have inv : ∀ g : H, g ^ 2 = 1 → g ≠ 1 → ∃ i, φ g = DihedralGroup.sr i := fun g hg hg1 =>
    dihedral_sr_of_sq hz (by rw [← map_pow, hg, map_one])
      (fun h => hg1 (φ.injective (by rw [h, map_one])))
  obtain ⟨l, hl⟩ := inv s hs hs1
  obtain ⟨i, hi⟩ := inv a ha ha1
  obtain ⟨j, hj⟩ := inv b hb hb1
  apply φ.injective
  simp only [map_mul, map_inv, hl, hi, hj, DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_r,
    DihedralGroup.inv_r]
  congr 1
  ring

@[expose] def stabQ (Q : QuadraticForm k (Fin 4 → k)) : Subgroup (antiSp k) where
  carrier := {g | ∀ x, Q (natAct g x) = Q x}
  one_mem' := fun x => by rw [natAct_one]
  mul_mem' {g h} hg hh := fun x => by rw [natAct_mul, hg, hh]
  inv_mem' {g} hg := fun x => by rw [← hg (natAct g⁻¹ x), act_act_inv]

theorem closure_eq_of_card_six [Finite k] {H : Subgroup (antiSp k)} (h6 : Nat.card H = 6)
    {u₁ u₂ : Fin 4 → k} (h₁ : trv u₁ 1 ∈ H) (h₂ : trv u₂ 1 ∈ H) (hc : spBil u₁ u₂ ≠ 0) :
    Subgroup.closure {trv u₁ 1, trv u₂ 1} = H := by
  set D := Subgroup.closure ({trv u₁ 1, trv u₂ 1} : Set (antiSp k)) with hD
  have hDH : D ≤ H := by
    rw [hD, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h₁
    · exact h₂
  have hu₁ : u₁ ≠ 0 := by
    rintro rfl
    simp at hc
  have h1D : trv u₁ 1 ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have h2D : trv u₂ 1 ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hord : orderOf (⟨trv u₁ 1, h1D⟩ : D) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simp [sq, trv_mul_self]))
      (fun h => (isTransvection_trv hu₁ one_ne_zero).1 (congrArg Subtype.val h))
  have h2 : 2 ∣ Nat.card D := hord ▸ orderOf_dvd_natCard _
  have htr : Matrix.trace (glMat ((trv u₁ 1 * trv u₂ 1 : antiSp k) : GL (Fin 4) k)) ≠ 0 := by
    rw [trace_trv_mul_trv, one_mul, one_mul]
    exact pow_ne_zero 2 hc
  have hnot : ∀ j : ℕ, (trv u₁ 1 * trv u₂ 1) ^ 2 ^ j ≠ 1 := fun j hj =>
    htr (trace_eq_zero_of_pow_two_pow hj)
  have hdvd6 : orderOf (trv u₁ 1 * trv u₂ 1) ∣ 6 := by
    have h := orderOf_dvd_natCard (⟨_, H.mul_mem h₁ h₂⟩ : H)
    rwa [h6, Subgroup.orderOf_mk] at h
  have h3 : 3 ∣ orderOf (trv u₁ 1 * trv u₂ 1) := by
    have h1 : orderOf (trv u₁ 1 * trv u₂ 1) ≠ 1 := fun h =>
      hnot 0 (by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp h)
    have h2' : orderOf (trv u₁ 1 * trv u₂ 1) ≠ 2 := fun h =>
      hnot 1 (by rw [pow_one, ← h]; exact pow_orderOf_eq_one _)
    have hle : orderOf (trv u₁ 1 * trv u₂ 1) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases h : orderOf (trv u₁ 1 * trv u₂ 1) <;> omega
  have h3D : 3 ∣ Nat.card D := by
    refine h3.trans ?_
    rw [← Subgroup.orderOf_mk _ (D.mul_mem h1D h2D)]
    exact orderOf_dvd_natCard _
  have h6D : Nat.card D = 6 :=
    Nat.dvd_antisymm (h6 ▸ Subgroup.card_dvd_of_le hDH)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3D)
  exact Subgroup.eq_of_le_of_card_ge hDH (by rw [h6, h6D])

end CFSG.Quasithin.Ch3E213M.G41.Big
