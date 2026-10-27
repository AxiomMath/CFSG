module

public import CFSG.Quasithin.EmptyFaithful.S146yL3Par

public section

namespace CFSG.Quasithin.H13.U3.NLine

open Matrix CFSG.Quasithin CFSG.QuasithinUnique.Setup.X7a

@[expose] def radMat : Fin 2 → ZMod 2 → ZMod 2 → Matrix (Fin 3) (Fin 3) (ZMod 2)
  | 0, r, s => !![1, r, s; 0, 1, 0; 0, 0, 1]
  | 1, r, s => !![1, 0, r; 0, 1, s; 0, 0, 1]

theorem radMat_mul (j : Fin 2) (r s r' s' : ZMod 2) :
    radMat j r s * radMat j r' s' = radMat j (r + r') (s + s') := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [radMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem radMat_zero (j : Fin 2) : radMat j 0 0 = 1 := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;> simp [radMat]

theorem det_radMat (j : Fin 2) (r s : ZMod 2) : (radMat j r s).det = 1 := by
  fin_cases j <;> revert r s <;> decide

@[expose] def radElt (j : Fin 2) (r s : ZMod 2) : SL3F2 := ⟨radMat j r s, det_radMat j r s⟩

@[expose] def radQ3 (j : Fin 2) : Subgroup SL3F2 where
  carrier := {u | ∃ r s : ZMod 2, (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) = radMat j r s}
  one_mem' := ⟨0, 0, by rw [radMat_zero]; rfl⟩
  mul_mem' := by
    rintro u v ⟨r, s, hu⟩ ⟨r', s', hv⟩
    exact ⟨r + r', s + s', by rw [Matrix.SpecialLinearGroup.coe_mul, hu, hv, radMat_mul]⟩
  inv_mem' := by
    rintro u ⟨r, s, hu⟩
    refine ⟨r, s, ?_⟩
    have h2 : radMat j r s * radMat j r s = 1 := by
      rw [radMat_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, radMat_zero]
    have hu2 : u * u = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, hu, h2]; rfl)
    have : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one]; exact hu2
    rw [this, hu]

theorem radQ3_le (j : Fin 2) : radQ3 j ≤ Q3 (ZMod 2) j := by
  rintro u ⟨r, s, hu⟩
  fin_cases j
  · refine (mem_Q3_zero_iff u).2 ⟨?_, ?_⟩ <;> rw [hu] <;> simp [radMat]
  · refine (mem_Q3_one_iff u).2 ⟨?_, ?_⟩ <;> rw [hu] <;> simp [radMat]

theorem norm_decide0 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M 1 0 = 0 → M 2 0 = 0 →
    M.det = 1 → ∀ r s : ZMod 2, ∃ r' s' : ZMod 2,
      M * !![1, r, s; 0, 1, 0; 0, 0, 1] = !![1, r', s'; 0, 1, 0; 0, 0, 1] * M := by
  decide +kernel

theorem norm_decide1 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M 2 0 = 0 → M 2 1 = 0 →
    M.det = 1 → ∀ r s : ZMod 2, ∃ r' s' : ZMod 2,
      M * !![1, 0, r; 0, 1, s; 0, 0, 1] = !![1, 0, r'; 0, 1, s'; 0, 0, 1] * M := by
  decide +kernel

theorem fpf_decide0 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M 1 0 = 0 → M 2 0 = 0 →
    M.det = 1 → M ^ 3 = 1 → M ≠ 1 → ∀ r s : ZMod 2,
      (!![1, r, s; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 →
      M * !![1, r, s; 0, 1, 0; 0, 0, 1] ≠ !![1, r, s; 0, 1, 0; 0, 0, 1] * M := by
  decide +kernel

theorem fpf_decide1 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M 2 0 = 0 → M 2 1 = 0 →
    M.det = 1 → M ^ 3 = 1 → M ≠ 1 → ∀ r s : ZMod 2,
      (!![1, 0, r; 0, 1, s; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 →
      M * !![1, 0, r; 0, 1, s; 0, 0, 1] ≠ !![1, 0, r; 0, 1, s; 0, 0, 1] * M := by
  decide +kernel

theorem norm_radMat {j : Fin 2} {g : SL3F2} (hg : g ∈ Q3 (ZMod 2) j) (r s : ZMod 2) :
    ∃ r' s' : ZMod 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * radMat j r s =
      radMat j r' s' * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  fin_cases j
  · obtain ⟨h10, h20⟩ := (mem_Q3_zero_iff g).1 hg
    exact norm_decide0 _ h10 h20 g.2 r s
  · obtain ⟨h20, h21⟩ := (mem_Q3_one_iff g).1 hg
    exact norm_decide1 _ h20 h21 g.2 r s

theorem conj_mem_radQ3 {j : Fin 2} {g u : SL3F2} (hg : g ∈ Q3 (ZMod 2) j) (hu : u ∈ radQ3 j) :
    g * u * g⁻¹ ∈ radQ3 j := by
  obtain ⟨r, s, hum⟩ := hu
  obtain ⟨r', s', h⟩ := norm_radMat hg r s
  have hgu : g * u = radElt j r' s' * g := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hum]
    exact h)
  rw [hgu, mul_inv_cancel_right]
  exact ⟨r', s', rfl⟩

theorem mul_ne_mul_of_radQ3 {j : Fin 2} {g u : SL3F2} (hg : g ∈ Q3 (ZMod 2) j) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (hu : u ∈ radQ3 j) (hu1 : u ≠ 1) : g * u ≠ u * g := by
  obtain ⟨r, s, hum⟩ := hu
  intro h
  have hM3 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg3]
    rfl
  have hM1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h1 => hg1 (Subtype.ext h1)
  have hR1 : radMat j r s ≠ 1 := by
    rw [← hum]
    intro h1
    exact hu1 (Subtype.ext h1)
  have hc : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * radMat j r s =
      radMat j r s * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← hum, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  fin_cases j
  · obtain ⟨h10, h20⟩ := (mem_Q3_zero_iff g).1 hg
    exact fpf_decide0 _ h10 h20 g.2 hM3 hM1 r s hR1 hc
  · obtain ⟨h20, h21⟩ := (mem_Q3_one_iff g).1 hg
    exact fpf_decide1 _ h20 h21 g.2 hM3 hM1 r s hR1 hc

theorem isPGroup_radQ3 (j : Fin 2) : IsPGroup 2 (radQ3 j) := by
  rintro ⟨u, r, s, hu⟩
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_pow, hu, pow_two, radMat_mul, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, radMat_zero]
  rfl

theorem exists_ne_one_radQ3 (j : Fin 2) : ∃ u ∈ radQ3 j, u ≠ 1 :=
  ⟨radElt j 1 0, ⟨1, 0, rfl⟩, fun h => by
    have h1 := congrArg (fun g : SL3F2 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    revert h1
    fin_cases j <;> decide⟩

theorem exists_radical_of_isMaxParabolic2 {P : Subgroup SL3F2}
    (hP : IsMaxParabolic2 (⊤ : Subgroup SL3F2) P) :
    ∃ U : Subgroup SL3F2, U ≤ P ∧ (∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U) ∧ IsPGroup 2 U ∧
      (∃ u ∈ U, u ≠ 1) ∧ ∀ p ∈ P, p ^ 3 = 1 → p ≠ 1 → ∀ u ∈ U, u ≠ 1 → p * u ≠ u * p := by
  obtain ⟨g, j, rfl⟩ := isMaxParabolic2_eq_map_Q3 hP
  set φ : SL3F2 →* SL3F2 := (MulAut.conj g).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.conj g).injective
  refine ⟨(radQ3 j).map φ, Subgroup.map_mono (radQ3_le j), ?_, (isPGroup_radQ3 j).map φ, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨p * u * p⁻¹, conj_mem_radQ3 hp hu, by simp only [map_mul, map_inv]⟩
  · obtain ⟨u, hu, hu1⟩ := exists_ne_one_radQ3 j
    exact ⟨φ u, ⟨u, hu, rfl⟩, fun h => hu1 (hφi (h.trans (map_one φ).symm))⟩
  · rintro _ ⟨p, hp, rfl⟩ hp3 hp1 _ ⟨u, hu, rfl⟩ hu1 h
    refine mul_ne_mul_of_radQ3 hp (hφi ?_) (fun h1 => hp1 (by rw [h1, map_one])) hu
      (fun h1 => hu1 (by rw [h1, map_one])) (hφi ?_)
    · rw [map_pow, hp3, map_one]
    · rw [map_mul, map_mul, h]

end CFSG.Quasithin.H13.U3.NLine
