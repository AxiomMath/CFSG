module

public import CFSG.Quasithin.MS93.S46I466bLin

public section

namespace CFSG.Quasithin.MS93.S46.I467

open CFSG.Quasithin CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix

variable {F : Type} [Field F]

theorem commN_eq_fixN_of_elemAb_card [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g)
    (hcard : Nat.card E = Nat.card F ^ 2) : commN E = fixN E := by
  have hle := commN_le_fixN_of_elemAb h2 hc
  have hik := Submodule.finrank_mono hle
  have hk3 := Submodule.finrank_le (fixN E)
  rw [Module.finrank_fin_fun] at hk3
  have hb := card_le_pow_finrank E
  rw [hcard] at hb
  have hexp := (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp hb
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  generalize Module.finrank F (fixN E) = k at *
  generalize Module.finrank F (commN E) = i at *
  interval_cases k <;> omega

theorem exists_mulVec_e0_eq {w : Fin 3 → F} (hw1 : w 1 = 0) (hw0 : w ≠ 0) :
    ∃ m : SL3 F, (m : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = w ∧
      ∀ v : Fin 3 → F, ((m : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 := by
  by_cases h0 : w 0 = 0
  · have h2 : w 2 ≠ 0 := by
      intro h2
      apply hw0
      funext i
      fin_cases i
      · exact h0
      · exact hw1
      · exact h2
    refine ⟨⟨!![0, 0, -(w 2)⁻¹; 0, 1, 0; w 2, 0, 0], ?_⟩, ?_, fun v => ?_⟩
    · simp [Matrix.det_fin_three, h2]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, hw1]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨⟨!![w 0, 0, 0; 0, 1, 0; w 2, 0, (w 0)⁻¹], ?_⟩, ?_, fun v => ?_⟩
    · simp [Matrix.det_fin_three, h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw1]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_mulVec_eq_of_coord_one {u₀ u : Fin 3 → F} (hu₀1 : u₀ 1 = 0) (hu₀ : u₀ ≠ 0)
    (hu1 : u 1 = 0) (hu : u ≠ 0) :
    ∃ g : SL3 F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ u₀ = u ∧
      ∀ v : Fin 3 → F, ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 := by
  obtain ⟨m₀, hm₀, hm₀1⟩ := exists_mulVec_e0_eq hu₀1 hu₀
  obtain ⟨m, hm, hm1⟩ := exists_mulVec_e0_eq hu1 hu
  have hinv : ∀ v : Fin 3 → F, (((m₀⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 := by
    intro v
    have := hm₀1 (((m₀⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    rwa [mulVec_inv_mulVec_SL3, eq_comm] at this
  refine ⟨m * m₀⁻¹, ?_, fun v => ?_⟩
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, ← hm₀, inv_mulVec_mulVec_SL3, hm]
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hm1, hinv]

omit [Field F] in
theorem mulVec_conj_SL3 [Field F] (y C : SL3 F) (v : Fin 3 → F) :
    ((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ((C : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
  rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_conj_axisGroup {P : Submodule F (Fin 3 → F)} {y : SL3 F}
    (hyP : ∀ p ∈ P, ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ p) 1 = 0)
    (hyP' : ∀ w : Fin 3 → F, w 1 = 0 → ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ P)
    {C : SL3 F} (hC : C ∈ axisGroup P) :
    (∀ v : Fin 3 → F, ((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        v + v 1 • (((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] -
          ![0, 1, 0])) ∧
      (((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] - ![0, 1, 0] :
        Fin 3 → F) 1 = 0 := by
  obtain ⟨hC1, hC2⟩ := hC
  have hfix : ∀ w : Fin 3 → F, w 1 = 0 →
      ((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro w hw
    rw [mulVec_conj_SL3, hC1 _ (hyP' w hw), mulVec_inv_mulVec_SL3]
  refine ⟨fun v => ?_, ?_⟩
  · have hdec : v = (v - v 1 • ![0, 1, 0]) + v 1 • ![0, 1, 0] := by abel
    have hw : ((v - v 1 • ![0, 1, 0] : Fin 3 → F) 1 = 0) := by simp
    conv_lhs => rw [hdec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hfix _ hw, smul_sub]
    abel
  · have e : ((y * C * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] - ![0, 1, 0] =
        (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ((C : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0]) -
          ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0]) := by
      rw [Matrix.mulVec_sub, mulVec_inv_mulVec_SL3, mulVec_conj_SL3]
    rw [e]
    exact hyP _ (hC2 _)

theorem eq_axisGroup_of_invariant {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {S : Subgroup (SL3 F)} (hS : S ≤ axisGroup P) (hS1 : S ≠ ⊥)
    (hinv : ∀ g : SL3 F, (∀ p ∈ P, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P) →
      ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    S = axisGroup P := by
  refine le_antisymm hS fun B hB => ?_
  obtain ⟨⟨s₀, hs₀S⟩, hs₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS1
  have hs₀1' : s₀ ≠ 1 := fun h => hs₀1 (Subtype.ext h)
  obtain ⟨x₀, hx₀⟩ : ∃ x : Fin 3 → F, (s₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ x ≠ x := by
    by_contra hall
    push Not at hall
    exact hs₀1' (eq_one_of_mulVec_eq_self hall)
  have hrP : (s₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ x₀ - x₀ ∈ P := (hS hs₀S).2 x₀
  have hr0 : (s₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ x₀ - x₀ ≠ 0 := sub_ne_zero.mpr hx₀
  obtain ⟨y, -, hyP, hyP'⟩ := exists_flag_conj hP hrP hr0
  obtain ⟨hD₀, hu₀1⟩ := mulVec_conj_axisGroup hyP hyP' (hS hs₀S)
  obtain ⟨hD, hu1⟩ := mulVec_conj_axisGroup hyP hyP' hB
  set u₀ := ((y * s₀ * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] - ![0, 1, 0]
    with hu₀def
  set u := ((y * B * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] - ![0, 1, 0]
    with hudef
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    apply hs₀1'
    have h1 : y * s₀ * y⁻¹ = 1 := eq_one_of_mulVec_eq_self fun v => by
      rw [hD₀ v, h0, smul_zero, add_zero]
    calc s₀ = y⁻¹ * (y * s₀ * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  by_cases hu : u = 0
  · have h1 : y * B * y⁻¹ = 1 := eq_one_of_mulVec_eq_self fun v => by
      rw [hD v, hu, smul_zero, add_zero]
    have hB1 : B = 1 := by
      calc B = y⁻¹ * (y * B * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    rw [hB1]
    exact S.one_mem
  obtain ⟨g, hg, hg1⟩ := exists_mulVec_eq_of_coord_one hu₀1 hu₀ hu1 hu
  have hginv : ∀ v : Fin 3 → F, (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 := by
    intro v
    have := hg1 (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    rwa [mulVec_inv_mulVec_SL3, eq_comm] at this
  have hh : ∀ p ∈ P, ((y⁻¹ * g * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P := by
    intro p hp
    rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hyP' _ (by rw [hg1]; exact hyP p hp)
  have hmem := hinv _ hh s₀ hs₀S
  have hyy : y * ((y⁻¹ * g * y) * s₀ * (y⁻¹ * g * y)⁻¹) * y⁻¹ = y * B * y⁻¹ := by
    have h1 : y * ((y⁻¹ * g * y) * s₀ * (y⁻¹ * g * y)⁻¹) * y⁻¹ = g * (y * s₀ * y⁻¹) * g⁻¹ := by
      group
    rw [h1]
    refine Subtype.ext (Matrix.ext_of_mulVec_single fun i => ?_)
    change ((g * (y * s₀ * y⁻¹) * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1 =
      ((y * B * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1
    rw [hD, mulVec_conj_SL3, hD₀, Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_inv_mulVec_SL3, hg,
      hginv]
  have hBeq : (y⁻¹ * g * y) * s₀ * (y⁻¹ * g * y)⁻¹ = B := by
    have := congrArg (fun z => y⁻¹ * z * y) hyy
    simpa [mul_assoc] using this
  rw [← hBeq]
  exact hmem

end CFSG.Quasithin.MS93.S46.I467
