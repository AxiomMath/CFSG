module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocE

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

@[expose] def a1X {b c d : K} (hb : h.bar b = b) (hd : h.bar d = d) : Xg h :=
  ⟨miyamotoXGL h 0 b c d,
    miyamotoUnipotent_le_SU h true false ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩)⟩

theorem a1X_mem_Vx {b c d : K} (hb : h.bar b = b) (hc : h.bar c = c) (hd : h.bar d = d) :
    a1X h (c := c) hb hd ∈ Vx h :=
  Subgroup.mem_subgroupOf.2 ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩,
    (miyamotoXGL_mem_Cu h).2 ⟨map_zero _, hb, hc, hd⟩⟩

theorem z1X_mem_Vx : z1X h ∈ Vx h := by
  have e : z1X h = a1X h (b := 0) (c := 0) (d := 1) (map_zero _) (map_one _) :=
    Subtype.ext (coe_z1X h)
  rw [e]
  exact a1X_mem_Vx h (map_zero _) (map_zero _) (map_one _)

theorem N1Fx_faithful {x : Xg h} (hx : x ∈ N1Fx h)
    (hcomm : ∀ v ∈ Vx h, x * v * x⁻¹ * v⁻¹ ∈ Ux h) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨m0, hm0⟩ := Subgroup.mem_subgroupOf.1 (inv_mem hx : x⁻¹ ∈ N1Fx h)
  set m : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.map h.fixedField.subtype m0 with hmdef
  have hm : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) =
      (m : Matrix (Fin 2) (Fin 2) K) i j := fun i j => h.mem_fixedField.1 (m0 i j).2
  have hxm : ((x : Xg h) : GL (Fin 4) K) = (miyamotoN1Hom h m)⁻¹ := by
    have e : miyamotoN1Hom h m = ((x⁻¹ : Xg h) : GL (Fin 4) K) := hm0
    rw [e]
    rfl
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  have t1 := Subgroup.mem_subgroupOf.1 (hcomm _ (z1X_mem_Vx h))
  obtain ⟨c, hc, hc1⟩ := t1
  have hz : (miyamotoXGL h 0 0 0 1)⁻¹ = miyamotoXGL h 0 0 0 1 :=
    inv_eq_of_mul_eq_one_right (miyamotoXGL_A1_mul_self h (map_zero _))
  have e1 : ((x * z1X h * x⁻¹ * (z1X h)⁻¹ : Xg h) : GL (Fin 4) K) =
      miyamotoXGL h 0 (m 0 1 * m 0 1) (m 0 1 * m 0 0) (m 0 0 * m 0 0 + 1) := by
    show (x : GL (Fin 4) K) * (z1X h : GL (Fin 4) K) * (x : GL (Fin 4) K)⁻¹ *
      ((z1X h : Xg h) : GL (Fin 4) K)⁻¹ = _
    rw [hxm, inv_inv, coe_z1X, miyamotoN1Hom_conj_z1, hz, hm 0 1, hm 0 0,
      miyamotoXGL_mul_A1 h (by rw [map_mul, hm 0 1])]
    simp
  rw [e1, miyamotoXGL_inj] at hc1
  obtain ⟨-, hq, -, hp⟩ := hc1
  have hm01 : (m : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := mul_self_eq_zero.1 hq
  have hm00 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have : ((m : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((m : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) =
        0 := by linear_combination hp - (m : Matrix (Fin 2) (Fin 2) K) 0 0 * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have hv1 : a1X h (b := 1) (c := 0) (d := 0) (map_one _) (map_zero _) ∈ Vx h :=
    a1X_mem_Vx h (map_one _) (map_zero _) (map_zero _)
  obtain ⟨c', hc', hc2⟩ := Subgroup.mem_subgroupOf.1 (hcomm _ hv1)
  have hv1i : (miyamotoXGL h 0 1 0 0)⁻¹ = miyamotoXGL h 0 1 0 0 :=
    inv_eq_of_mul_eq_one_right (miyamotoXGL_A1_mul_self h (map_one _))
  have key := miyamotoN1Hom_conj_A1 h m (b := 1) (c := 0) (d := 0) (map_one _) (map_zero _)
  simp only [hm, map_zero, zero_mul, zero_add, one_mul, mul_zero, sub_zero] at key
  have hc2' : (x : GL (Fin 4) K) * miyamotoXGL h 0 1 0 0 * (x : GL (Fin 4) K)⁻¹ *
      (miyamotoXGL h 0 1 0 0)⁻¹ = miyamotoXGL h 0 0 c' 0 := hc2
  rw [hxm, inv_inv, key, hv1i, miyamotoXGL_mul_A1 h (by rw [map_mul, hm 1 1]),
    miyamotoXGL_inj] at hc2'
  obtain ⟨-, -, -, hd⟩ := hc2'
  have hm10 : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    mul_self_eq_zero.1 (by linear_combination (-1 : K) * hd)
  have hm11 : (m : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hm00, hm01] at hdet
    simpa using hdet
  have hm1 : m = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm00, hm01, hm10, hm11]
  apply Subtype.ext
  rw [hxm, hm1, map_one, inv_one]
  rfl

end CFSG.Quasithin.H13.F431.Un.LL
