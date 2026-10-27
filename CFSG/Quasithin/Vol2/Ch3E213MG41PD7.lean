module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD6

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] noncomputable def formA (u w : Fin 4 → k) (c : k) : QuadraticForm k (Fin 4 → k) :=
  QuadraticMap.linMulLin (spBil w) (spBil u) +
    QuadraticMap.linMulLin (spBil w + c⁻¹ • spBil u) (spBil w + c⁻¹ • spBil u) +
    QuadraticMap.linMulLin (LinearMap.proj 1) (LinearMap.proj 2)

omit [CharP k 2] in
theorem formA_apply (u w : Fin 4 → k) (c : k) (x : Fin 4 → k) :
    formA u w c x = spBil w x * spBil u x + (spBil w x + c⁻¹ * spBil u x) ^ 2 + x 1 * x 2 := by
  simp [formA, QuadraticMap.linMulLin_apply, sq]
  ring

theorem polar_formA {u w : Fin 4 → k} (hu : u 1 = 0 ∧ u 2 = 0) (hw : w 1 = 0 ∧ w 2 = 0)
    (huw : spBil u w = 1) (c : k) (x y : Fin 4 → k) :
    QuadraticMap.polar (formA u w c) x y = spBil x y := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have huw' : u 0 * w 3 + u 3 * w 0 = 1 := by
    rw [bil_apply, hu.1, hu.2, hw.1, hw.2] at huw
    linear_combination huw
  simp only [QuadraticMap.polar, formA_apply, map_add, Pi.add_apply, bil_apply, hu.1, hu.2, hw.1,
    hw.2]
  linear_combination (x 3 * y 0 + x 0 * y 3) * huw' +
    (w 0 * u 0 * x 3 * y 3 + w 3 * u 3 * x 0 * y 0 +
      (w 0 * x 3 + w 3 * x 0 + c⁻¹ * (u 0 * x 3 + u 3 * x 0)) *
        (w 0 * y 3 + w 3 * y 0 + c⁻¹ * (u 0 * y 3 + u 3 * y 0))) * h2

omit [CharP k 2] in
theorem formA_eOne {u w : Fin 4 → k} (hu : u 2 = 0) (hw : w 2 = 0) (c : k) :
    formA u w c (eOne k) = 0 := by
  rw [formA_apply, bil_eOne, bil_eOne, hu, hw]
  simp [eOne]

omit [CharP k 2] in
theorem formA_of_two {u w x : Fin 4 → k} (hu : u 1 = 0 ∧ u 2 = 0) (hw : w 1 = 0 ∧ w 2 = 0)
    (hx : x 2 = 0) (c : k) : formA u w c x = formA u w c (proj x) := by
  simp [formA_apply, bil_apply, hu.1, hu.2, hw.1, hw.2, hx, proj]

theorem formA_left {u w : Fin 4 → k} (hu : u 2 = 0) (huw : spBil u w = 1) (c : k) :
    formA u w c u = 1 := by
  rw [formA_apply, bil_self, bil_symm w u, huw, hu]
  ring

theorem formA_smul_right {u w : Fin 4 → k} (hw : w 2 = 0) (huw : spBil u w = 1) {c : k}
    (hc : c ≠ 0) : formA u w c (c • w) = 1 := by
  rw [formA_apply]
  simp only [map_smul, smul_eq_mul, bil_self, huw, Pi.smul_apply, hw, mul_zero, zero_mul,
    zero_add, add_zero, mul_one, inv_mul_cancel₀ hc, one_pow]

theorem CaseA.form [Finite k] {G₀ : Subgroup (antiSp k)} (hA : CaseA G₀) {z₁ z₂ : Fin 4 → k}
    (hz₁ : z₁ ∈ cenT G₀) (hz₂ : z₂ ∈ cenT G₀) (hc : spBil (proj z₁) (proj z₂) ≠ 0) :
    ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
      Q (eOne k) = 0 ∧ Q (proj z₁) = 1 ∧ Q (proj z₂) = 1 ∧
        ∀ z ∈ cenT G₀, proj z ≠ 0 → Q z = 1 := by
  set H := secGrp (cenT G₀) with hH
  set c := spBil (proj z₁) (proj z₂) with hcdef
  set w := c⁻¹ • proj z₂ with hw
  have hsu : proj z₁ 1 = 0 ∧ proj z₁ 2 = 0 := by simp [proj]
  have hsu₂ : proj z₂ 1 = 0 ∧ proj z₂ 2 = 0 := by simp [proj]
  have hsw : w 1 = 0 ∧ w 2 = 0 := by simp [hw, proj]
  have huw : spBil (proj z₁) w = 1 := by
    rw [hw, map_smul, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc]
  have hu₂w : proj z₂ = c • w := by rw [hw, smul_smul, mul_inv_cancel₀ hc, one_smul]
  set Q := formA (proj z₁) w c with hQdef
  have hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y := polar_formA hsu hsw huw c
  have hQ₁ : Q (proj z₁) = 1 := formA_left hsu.2 huw c
  have hQ₂ : Q (proj z₂) = 1 := by rw [hu₂w]; exact formA_smul_right hsw.2 huw hc
  refine ⟨Q, hQ, formA_eOne hsu.2 hsw.2 c, hQ₁, hQ₂, ?_⟩
  intro z hz hpz
  rw [hQdef, formA_of_two hsu hsw hz.2 c, ← hQdef]
  have h₁ : trv (proj z₁) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz₁
  have h₂ : trv (proj z₂) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz₂
  have hp : trv (proj z) 1 ∈ H := trv_proj_mem_secGrp cenT_two hz
  have hinv₁ := form_act_trv_of_eq_one Q hQ hQ₁
  have hinv₂ := form_act_trv_of_eq_one Q hQ hQ₂
  rcases hA with ⟨M, -, hM, -, ⟨φ⟩⟩ | h6
  · have hinvol : ∀ (u : Fin 4 → k) (hu : trv u 1 ∈ H), u ≠ 0 →
        (⟨trv u 1, hu⟩ : H) ^ 2 = 1 ∧ (⟨trv u 1, hu⟩ : H) ≠ 1 := fun u hu hu0 =>
      ⟨Subtype.ext (by simp [sq, trv_mul_self]),
        fun h => (isTransvection_trv hu0 one_ne_zero).1 (congrArg Subtype.val h)⟩
    have hu₁0 : proj z₁ ≠ 0 := ne_zero_of_bil_eq_one huw
    have hu₂0 : proj z₂ ≠ 0 := fun h => hc (by rw [hcdef, h, map_zero])
    obtain ⟨hs, hs1⟩ := hinvol _ hp hpz
    obtain ⟨ha, ha1⟩ := hinvol _ h₁ hu₁0
    obtain ⟨hb, hb1⟩ := hinvol _ h₂ hu₂0
    have hconj := congrArg Subtype.val (dihedral_conj_inv hM φ hs hs1 ha ha1 hb hb1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hconj
    have hc₀ : ∀ x, Q (natAct (trv (proj z₁) 1 * trv (proj z₂) 1) x) = Q x := fun x => by
      rw [natAct_mul, hinv₁, hinv₂]
    exact eq_one_of_conj_inv Q hQ hc₀ (act_ne_self hsu hsu₂ (by simp [proj]) hc hpz) hconj
  · have hle : Subgroup.closure {trv (proj z₁) 1, trv (proj z₂) 1} ≤ stabQ Q := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hinv₁
      · exact hinv₂
    rw [closure_eq_of_card_six h6 h₁ h₂ hc] at hle
    exact eq_one_of_form_act_trv Q hQ hpz (hle hp)

end CFSG.Quasithin.Ch3E213M.G41.Big
