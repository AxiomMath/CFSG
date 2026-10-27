module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKFormDefs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

namespace E6Dep

private def X1 (c : ZMod 3) : Finset Vec6 := (kNorm1 c).filter fun u => fpart c u = 0

private def X2 (c : ZMod 3) : Finset Vec6 :=
  (kNorm1 c).filter fun u => fpart c u = 0 ∨ mpart u = 0

private theorem X1_mem {c : ZMod 3} {v : Vec6} :
    v ∈ X1 c ↔ v ∈ kNorm1 c ∧ fpart c v = 0 := by
  rw [X1, Finset.mem_filter]

private theorem X2_mem {c : ZMod 3} {v : Vec6} :
    v ∈ X2 c ↔ v ∈ kNorm1 c ∧ (fpart c v = 0 ∨ mpart v = 0) := by
  rw [X2, Finset.mem_filter]

private theorem bilK_eq (c : ZMod 3) (u v : Vec6) :
    bilK c u v = u 0 * (v 0 + v 1) + u 1 * (v 0 + v 1 + v 2) + u 2 * (v 1 + v 2 + v 3) +
      u 3 * (v 2 + v 3) + (c * u 4 - u 5) * (c * v 4 - v 5) := by
  simp [bilK, gbeta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem normK_eq (c : ZMod 3) (h : Vec6) :
    normK c h = norm6 (mpart h) + fpart c h * fpart c h := by
  simp [normK, bilK, gbeta, norm6, bil6, gram6, mpart, fpart, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

private theorem normK_add_smul (c : ZMod 3) (w u : Vec6) (a : ZMod 3) :
    normK c (w + a • u) = normK c w + 2 * a * bilK c w u + a * a * normK c u := by
  simp only [normK, bilK_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem zmod3_three_mul : ∀ x : ZMod 3, (3 : ZMod 3) * x = 0 := by decide +kernel

private theorem zmod3_sq : ∀ a b : ZMod 3, a ≠ 0 → 1 = b + a * a → b = 0 := by decide +kernel

private theorem normK_refl (c : ZMod 3) (w u : Vec6) (hu : normK c u = 1) :
    normK c (w + bilK c w u • u) = normK c w := by
  rw [normK_add_smul, hu]
  have h3 : (3 : ZMod 3) * (bilK c w u * bilK c w u) = 0 := zmod3_three_mul _
  calc normK c w + 2 * bilK c w u * bilK c w u + bilK c w u * bilK c w u * 1
      = normK c w + 3 * (bilK c w u * bilK c w u) := by ring
    _ = normK c w + 0 := by rw [h3]
    _ = normK c w := by ring

private theorem mpart_eq_zero_iff (h : Vec6) :
    mpart h = 0 ↔ h 0 = 0 ∧ h 1 = 0 ∧ h 2 = 0 ∧ h 3 = 0 := by
  constructor
  · intro hh
    exact ⟨by simpa [mpart] using congrFun hh 0,
      by simpa [mpart] using congrFun hh 1,
      by simpa [mpart] using congrFun hh 2,
      by simpa [mpart] using congrFun hh 3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext i
    fin_cases i <;> simp [mpart, h0, h1, h2, h3]

private theorem bilK_of_mpart_left (c : ZMod 3) {u v : Vec6} (hu : mpart u = 0) :
    bilK c u v = fpart c u * fpart c v := by
  obtain ⟨h0, h1, h2, h3⟩ := (mpart_eq_zero_iff u).mp hu
  rw [bilK_eq]
  simp [fpart, h0, h1, h2, h3]

private theorem bilK_of_mpart_right (c : ZMod 3) {u v : Vec6} (hv : mpart v = 0) :
    bilK c u v = fpart c u * fpart c v := by
  obtain ⟨h0, h1, h2, h3⟩ := (mpart_eq_zero_iff v).mp hv
  rw [bilK_eq]
  simp [fpart, h0, h1, h2, h3]

private theorem mpart_add (u v : Vec6) : mpart (u + v) = mpart u + mpart v := by
  ext i; fin_cases i <;> simp [mpart]

private theorem mpart_smul (a : ZMod 3) (u : Vec6) : mpart (a • u) = a • mpart u := by
  ext i; fin_cases i <;> simp [mpart, smul_eq_mul]

private theorem fpart_add (c : ZMod 3) (u v : Vec6) :
    fpart c (u + v) = fpart c u + fpart c v := by
  simp [fpart, smul_eq_mul]; ring

private theorem fpart_smul (c : ZMod 3) (a : ZMod 3) (u : Vec6) :
    fpart c (a • u) = a * fpart c u := by
  simp [fpart, smul_eq_mul]; ring

private theorem mpart_kY (c : ZMod 3) : mpart (kY c) = 0 := by
  ext i; fin_cases i <;> simp [mpart, kY]

private theorem fpart_kY (c : ZMod 3) : fpart c (kY c) = 0 := by
  simp [fpart, kY]

private theorem mpart_add_kY (c : ZMod 3) (u : Vec6) : mpart (u + kY c) = mpart u := by
  rw [mpart_add, mpart_kY, add_zero]

private theorem fpart_add_kY (c : ZMod 3) (u : Vec6) : fpart c (u + kY c) = fpart c u := by
  rw [fpart_add, fpart_kY, add_zero]

private theorem normK_add_kY (c : ZMod 3) (u : Vec6) : normK c (u + kY c) = normK c u := by
  rw [normK_eq, normK_eq, mpart_add_kY, fpart_add_kY]

private theorem kNorm1_mem {c : ZMod 3} {v : Vec6} : v ∈ kNorm1 c ↔ normK c v = 1 := by
  simp [kNorm1]

private theorem cS_props (c : ZMod 3) {u : Vec6} (hu : u ∈ cS) :
    mpart u = u ∧ fpart c u = 0 ∧ normK c u = 1 := by
  rw [cS] at hu
  obtain ⟨-, h4, h5, hn6⟩ := Finset.mem_filter.mp hu
  have hm : mpart u = u := by
    ext i; fin_cases i <;> simp [mpart, h4, h5]
  have hf : fpart c u = 0 := by simp [fpart, h4, h5]
  have hn : normK c u = 1 := by rw [normK_eq, hm, hf, hn6]; ring
  exact ⟨hm, hf, hn⟩

private theorem normK_xx : ∀ c : ZMod 3, normK c xx = 1 := by decide +kernel

private theorem fpart_xx_ne : ∀ c : ZMod 3, fpart c xx ≠ 0 := by decide +kernel

private theorem normK_h0_xx : ∀ c : ZMod 3, normK c (h0 + xx) = 1 := by decide +kernel

private theorem fpart_h0_xx : ∀ c : ZMod 3, fpart c (h0 + xx) ≠ 0 ∧ mpart (h0 + xx) ≠ 0 := by
  decide +kernel

private theorem X1_closed (c : ZMod 3) :
    X1 c ⊆ kNorm1 c ∧ (∀ u ∈ X1 c, ∀ w ∈ X1 c, w + bilK c w u • u ∈ X1 c) ∧
    (∀ u ∈ X1 c, u + kY c ∈ X1 c) ∧ cS ⊆ X1 c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; exact (X1_mem.mp hv).1
  · intro u hu w hw
    obtain ⟨hu1, hu2⟩ := X1_mem.mp hu
    obtain ⟨hw1, hw2⟩ := X1_mem.mp hw
    rw [X1_mem]
    refine ⟨?_, ?_⟩
    · rw [kNorm1_mem] at hu1 hw1 ⊢
      rw [normK_refl c w u hu1, hw1]
    · rw [fpart_add, fpart_smul, hu2, hw2]; ring
  · intro u hu
    obtain ⟨hu1, hu2⟩ := X1_mem.mp hu
    rw [X1_mem]
    refine ⟨?_, ?_⟩
    · rw [kNorm1_mem] at hu1 ⊢
      rw [normK_add_kY, hu1]
    · rw [fpart_add_kY, hu2]
  · intro u hu
    obtain ⟨hmu, hfu, hnu⟩ := cS_props c hu
    rw [X1_mem]
    exact ⟨kNorm1_mem.mpr hnu, hfu⟩

private theorem X2_closed (c : ZMod 3) :
    X2 c ⊆ kNorm1 c ∧ (∀ u ∈ X2 c, ∀ w ∈ X2 c, w + bilK c w u • u ∈ X2 c) ∧
    (∀ u ∈ X2 c, u + kY c ∈ X2 c) ∧ cS ⊆ X2 c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; exact (X2_mem.mp hv).1
  · intro u hu w hw
    obtain ⟨hu1, hu2⟩ := X2_mem.mp hu
    obtain ⟨hw1, hw2⟩ := X2_mem.mp hw
    rw [X2_mem]
    refine ⟨?_, ?_⟩
    · rw [kNorm1_mem] at hu1 hw1 ⊢
      rw [normK_refl c w u hu1, hw1]
    · rcases hu2 with hu2 | hu2
      · rcases hw2 with hw2 | hw2
        · left; rw [fpart_add, fpart_smul, hu2, hw2]; ring
        · right
          have hb : bilK c w u = 0 := by
            rw [bilK_of_mpart_left c hw2, hu2, mul_zero]
          rw [hb, zero_smul, add_zero, hw2]
      · rcases hw2 with hw2 | hw2
        · left
          have hb : bilK c w u = 0 := by
            rw [bilK_of_mpart_right c hu2, hw2, zero_mul]
          rw [hb, zero_smul, add_zero, hw2]
        · right
          rw [mpart_add, mpart_smul, hw2, hu2]; simp
  · intro u hu
    obtain ⟨hu1, hu2⟩ := X2_mem.mp hu
    rw [X2_mem]
    refine ⟨?_, ?_⟩
    · rw [kNorm1_mem] at hu1 ⊢
      rw [normK_add_kY, hu1]
    · rcases hu2 with hu2 | hu2
      · left; rw [fpart_add_kY, hu2]
      · right; rw [mpart_add_kY, hu2]
  · intro u hu
    obtain ⟨hmu, hfu, hnu⟩ := cS_props c hu
    rw [X2_mem]
    exact ⟨kNorm1_mem.mpr hnu, Or.inl hfu⟩

theorem kgen_parts {c : ZMod 3} {h : Vec6} (hn : normK c h = 1) (hg : KGen c h) :
    mpart h ≠ 0 ∧ norm6 (mpart h) = 0 ∧ fpart c h ≠ 0 := by
  have hf : fpart c h ≠ 0 := by
    intro hf0
    obtain ⟨hsub, hrefl, hy, hcS⟩ := X1_closed c
    have hX := hg (X1 c) hsub hrefl hy hcS (X1_mem.mpr ⟨kNorm1_mem.mpr hn, hf0⟩)
    have hxx : xx ∈ X1 c := by rw [hX, kNorm1_mem]; exact normK_xx c
    exact fpart_xx_ne c (X1_mem.mp hxx).2
  have hm : mpart h ≠ 0 := by
    intro hm0
    obtain ⟨hsub, hrefl, hy, hcS⟩ := X2_closed c
    have hX := hg (X2 c) hsub hrefl hy hcS (X2_mem.mpr ⟨kNorm1_mem.mpr hn, Or.inr hm0⟩)
    have h' : h0 + xx ∈ X2 c := by rw [hX, kNorm1_mem]; exact normK_h0_xx c
    rcases (X2_mem.mp h').2 with hf0 | hm0'
    · exact (fpart_h0_xx c).1 hf0
    · exact (fpart_h0_xx c).2 hm0'
  have hnorm : norm6 (mpart h) = 0 := by
    have h1 : (1 : ZMod 3) = norm6 (mpart h) + fpart c h * fpart c h := by
      rw [← normK_eq, hn]
    exact zmod3_sq (fpart c h) (norm6 (mpart h)) hf h1
  exact ⟨hm, hnorm, hf⟩

end E6Dep

end CFSG.StandardType

end
