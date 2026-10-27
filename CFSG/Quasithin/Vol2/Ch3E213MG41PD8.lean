module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD6

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem mul_zpow_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (j : ℤ) : a * (a * b) ^ j = (a * b) ^ (-j) * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [ha', mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]
  have h2 : a * (a * b) ^ j * a⁻¹ = (a * b) ^ (-j) := by
    have := map_zpow (MulAut.conj a) (a * b) j
    simp only [MulAut.conj_apply] at this
    rw [this, h1, zpow_neg, inv_zpow]
  calc a * (a * b) ^ j = a * (a * b) ^ j * a⁻¹ * a := by group
    _ = (a * b) ^ (-j) * a := by rw [h2]

theorem mem_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    {g : G} (hg : g ∈ Subgroup.closure {a, b}) :
    ∃ j : ℤ, g = (a * b) ^ j ∨ g = (a * b) ^ j * a := by
  have key := mul_zpow_pair ha hb
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg, zpow_one, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hb]
  | one => exact ⟨0, Or.inl (by rw [zpow_zero])⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨j, rfl | rfl⟩ := hy
    · exact ⟨i + j, Or.inl (by rw [zpow_add])⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · exact ⟨i - j, Or.inr (by rw [mul_assoc, key, ← mul_assoc, ← zpow_add, sub_eq_add_neg])⟩
    · refine ⟨i - j, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc a, key, mul_assoc, ha, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv x _ hx =>
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact ⟨-i, Or.inl (by rw [zpow_neg])⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, ← zpow_neg, key, neg_neg]

theorem zpow_mul_conj {G : Type*} [Group G] {a c : G} (ha : a * a = 1)
    (key : ∀ j : ℤ, a * c ^ j = c ^ (-j) * a) (j : ℤ) : c ^ j * a * c * (c ^ j * a) = c⁻¹ := by
  calc c ^ j * a * c * (c ^ j * a) = c ^ j * (a * c ^ (1 + j)) * a := by
        rw [zpow_one_add]
        group
    _ = c ^ j * (c ^ (-(1 + j)) * a) * a := by rw [key]
    _ = c⁻¹ * (a * a) := by group
    _ = c⁻¹ := by rw [ha, mul_one]

variable {k : Type} [Field k] [CharP k 2]

theorem CaseA.conj_inv [Finite k] {G₀ : Subgroup (antiSp k)} (hA : CaseA G₀)
    {z₁ z₂ z : Fin 4 → k} (hz₁ : z₁ ∈ cenT G₀) (hz₂ : z₂ ∈ cenT G₀) (hz : z ∈ cenT G₀)
    (hc : spBil (proj z₁) (proj z₂) ≠ 0) (hpz : proj z ≠ 0) :
    trv (proj z) 1 * (trv (proj z₁) 1 * trv (proj z₂) 1) * trv (proj z) 1 =
      (trv (proj z₁) 1 * trv (proj z₂) 1)⁻¹ := by
  set H := secGrp (cenT G₀) with hH
  have h₁ : trv (proj z₁) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz₁
  have h₂ : trv (proj z₂) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz₂
  have hp : trv (proj z) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz
  have hu₁0 : proj z₁ ≠ 0 := fun h => hc (by rw [h]; simp)
  have hu₂0 : proj z₂ ≠ 0 := fun h => hc (by rw [h, map_zero])
  rcases hA with ⟨M, -, hM, -, ⟨φ⟩⟩ | h6
  · have hinvol : ∀ (u : Fin 4 → k) (hu : trv u 1 ∈ H), u ≠ 0 →
        (⟨trv u 1, hu⟩ : H) ^ 2 = 1 ∧ (⟨trv u 1, hu⟩ : H) ≠ 1 := fun u hu hu0 =>
      ⟨Subtype.ext (by simp [sq, trv_mul_self]),
        fun h => (isTransvection_trv hu0 one_ne_zero).1 (congrArg Subtype.val h)⟩
    obtain ⟨hs, hs1⟩ := hinvol _ hp hpz
    obtain ⟨ha, ha1⟩ := hinvol _ h₁ hu₁0
    obtain ⟨hb, hb1⟩ := hinvol _ h₂ hu₂0
    have h := congrArg Subtype.val (dihedral_conj_inv hM φ hs hs1 ha ha1 hb hb1)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  · have hmem : trv (proj z) 1 ∈ Subgroup.closure {trv (proj z₁) 1, trv (proj z₂) 1} := by
      rw [closure_eq_of_card_six h6 h₁ h₂ hc]
      exact hp
    have ha := trv_mul_self (proj z₁) 1
    have hb := trv_mul_self (proj z₂) 1
    obtain ⟨j, hj | hj⟩ := mem_closure_pair ha hb hmem
    · exfalso
      have hcomm : trv (proj z₁) 1 * trv (proj z₂) 1 * trv (proj z) 1 *
          (trv (proj z₁) 1 * trv (proj z₂) 1)⁻¹ = trv (proj z) 1 := by
        rw [hj, (Commute.self_zpow _ j).eq, mul_inv_cancel_right]
      rw [conj_trv] at hcomm
      obtain ⟨μ, -, hμ, hμ2⟩ := trv_eq_trv hpz one_ne_zero hcomm
      rw [mul_one] at hμ2
      rw [eq_one_of_sq_eq_one hμ2, one_smul] at hμ
      exact act_ne_self (by simp [proj]) (by simp [proj]) (by simp [proj]) hc hpz hμ
    · rw [hj]
      exact zpow_mul_conj ha (mul_zpow_pair ha hb) j

end CFSG.Quasithin.Ch3E213M.G41.Big
