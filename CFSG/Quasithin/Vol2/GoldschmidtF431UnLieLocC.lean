module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem exists_sqrt_fixed {c : K} (hc : h.bar c = c) : ∃ p : K, h.bar p = p ∧ p * p = c := by
  have := h.finite
  obtain ⟨⟨p, hp⟩, hpp⟩ := FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2)
    (⟨c, h.mem_fixedField.2 hc⟩ : h.fixedField)
  exact ⟨p, h.mem_fixedField.1 hp, (congrArg Subtype.val hpp).symm⟩

@[expose] def ucX {c : K} (hc : h.bar c = c) : Xg h :=
  ⟨miyamotoXGL h 0 0 c 0,
    miyamotoUnipotent_le_SU h true false ((ucGL_le h (miyamotoXGL_mem_ucGL h hc)).1)⟩

theorem coe_ucX {c : K} (hc : h.bar c = c) :
    ((ucX h hc : Xg h) : GL (Fin 4) K) = miyamotoXGL h 0 0 c 0 := rfl

theorem ucX_mem {c : K} (hc : h.bar c = c) : ucX h hc ∈ Ux h :=
  Subgroup.mem_subgroupOf.2 (miyamotoXGL_mem_ucGL h hc)

theorem exists_row {p q : K} (hp : h.bar p = p) (hq : h.bar q = q) (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ r s : K, h.bar r = r ∧ h.bar s = s ∧ p * s - q * r = 1 := by
  rcases hpq with hp0 | hq0
  · exact ⟨0, p⁻¹, map_zero _, by rw [map_inv₀, hp],
      by rw [mul_zero, sub_zero, mul_inv_cancel₀ hp0]⟩
  · refine ⟨-q⁻¹, 0, by rw [map_neg, map_inv₀, hq], map_zero _, ?_⟩
    rw [mul_zero, zero_sub, mul_neg, neg_neg, mul_inv_cancel₀ hq0]

theorem exists_conj_z1 {p q : K} (hp : h.bar p = p) (hq : h.bar q = q) (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ s ∈ Cx h, (s : GL (Fin 4) K) * ((z1X h : Xg h) : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹ =
      miyamotoXGL h 0 (q * q) (q * p) (p * p) := by
  obtain ⟨r, t, hr, ht, hdet⟩ := exists_row h hp hq hpq
  let m : SpecialLinearGroup (Fin 2) K :=
    ⟨!![p, q; r, t], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  have hm : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) =
      (m : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hp
    · exact hq
    · exact hr
    · exact ht
  have hN := miyamotoN1Hom_mem_N1_inf_Cu h hm
  have hNF : (miyamotoN1Hom h m)⁻¹ ∈ miyamotoN1F h := by
    rw [← miyamotoN1_inf_Cu h]
    exact inv_mem hN
  have hG : (miyamotoN1Hom h m)⁻¹ ∈ gramSU h (miyamotoJ4 K) :=
    inv_mem (miyamotoN1_le_gramSU h hN.1)
  refine ⟨⟨_, hG⟩, ?_, ?_⟩
  · rw [cent_z2X h]
    exact Subgroup.mem_subgroupOf.2 (mem_sup_right hNF)
  · have e := miyamotoN1Hom_conj_z1 h m
    show (miyamotoN1Hom h m)⁻¹ * ((z1X h : Xg h) : GL (Fin 4) K) *
      ((miyamotoN1Hom h m)⁻¹)⁻¹ = _
    have e00 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = p := rfl
    have e01 : (m : Matrix (Fin 2) (Fin 2) K) 0 1 = q := rfl
    rw [inv_inv, coe_z1X, e, e00, e01, hp, hq]

theorem coset_Vx {v : Xg h} (hv : v ∈ Vx h) (hvU : v ∉ Ux h) :
    ∃ x ∈ Cx h, ∃ u ∈ Ux h, v = x * z1X h * x⁻¹ * u := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hA, hC⟩ := Subgroup.mem_subgroupOf.1 hv
  obtain ⟨b, c, d, hb, hd, hvx⟩ := (mem_A1 h).1 hA
  rw [hvx] at hC
  obtain ⟨-, -, hc, -⟩ := (miyamotoXGL_mem_Cu h).1 hC
  have hbd : d ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hvU (Subgroup.mem_subgroupOf.2 ⟨c, hc, by rw [hvx, hcon.1, hcon.2]⟩)
  obtain ⟨p, hp, hpp⟩ := exists_sqrt_fixed h hd
  obtain ⟨q, hq, hqq⟩ := exists_sqrt_fixed h hb
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    rcases hbd with hd0 | hb0
    · exact Or.inl fun hp0 => hd0 (by rw [← hpp, hp0, mul_zero])
    · exact Or.inr fun hq0 => hb0 (by rw [← hqq, hq0, mul_zero])
  obtain ⟨s, hs, hsz⟩ := exists_conj_z1 h hp hq hpq
  have hc' : h.bar (c + q * p) = c + q * p := by rw [map_add, map_mul, hc, hp, hq]
  refine ⟨s, hs, ucX h hc', ucX_mem h hc', Subtype.ext ?_⟩
  show (v : GL (Fin 4) K) = (s : GL (Fin 4) K) * ((z1X h : Xg h) : GL (Fin 4) K) *
    (s : GL (Fin 4) K)⁻¹ * (ucX h hc' : GL (Fin 4) K)
  rw [hsz, coe_ucX, hqq, hpp, miyamotoXGL_mul_A1 h hb, hvx, miyamotoXGL_inj]
  exact ⟨rfl, by ring, by linear_combination (-(q * p)) * h2, by ring⟩

end CFSG.Quasithin.H13.F431.Un.LL
