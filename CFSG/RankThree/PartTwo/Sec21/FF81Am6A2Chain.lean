module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Cen
public import CFSG.LargeExtraspecial.A2ModFrCMat

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF79

noncomputable def pH : H6 := ofCode (a2P, a2P) (by decide +kernel)

noncomputable def qH : H6 := ofCode (a2Q, a2Q) (by decide +kernel)

noncomputable def rH : H6 := pH * qH * pH

noncomputable def ePH : H6 := ofCode (a2EP, a2EP) (by decide +kernel)

noncomputable def eMH : H6 := ofCode (a2EM, a2EM) (by decide +kernel)

noncomputable def gYH : H6 := ofCode (a2GY, a2GYI) (by decide +kernel)

noncomputable def jH : H6 := ofCode (j6C, j6C) (by decide +kernel)

theorem mat6_pH : mat6 pH = dec6 a2P := mat6_ofCode _ _

theorem mat6_qH : mat6 qH = dec6 a2Q := mat6_ofCode _ _

theorem mat6_rH : mat6 rH = dec6 a2R := by
  rw [rH, map_mul, map_mul, mat6_pH, mat6_qH, a2R, dec6_mul6, dec6_mul6]

theorem mat6_ePH : mat6 ePH = dec6 a2EP := mat6_ofCode _ _

theorem mat6_eMH : mat6 eMH = dec6 a2EM := mat6_ofCode _ _

theorem mat6_gYH : mat6 gYH = dec6 a2GY := mat6_ofCode _ _

theorem mat6_gYH_inv : mat6 gYH⁻¹ = dec6 a2GYI := mat6_ofCode_inv _ _

theorem mat6_jH : mat6 jH = dec6 j6C := mat6_ofCode _ _

theorem mat6_jH_inv : mat6 jH⁻¹ = dec6 j6C := mat6_ofCode_inv _ _

section Chain


theorem chain_parts : chainPairs = true ∧ chainXstar = true ∧ chainK2 = true ∧
    chainSiegel = true ∧ chainWords = true := by
  have h := a2_parts.2.2.2.2.2
  simp only [chainCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem ePH_mem_Xstar : ePH ∈ Xstar := by
  have h := chain_parts.2.1
  simp only [chainXstar, Bool.and_eq_true] at h
  have hm : mat6 (hH⁻¹ * ePH * hH) = dec6 (cj a2HI a2EP a2H) := by
    rw [map_mul, map_mul, mat6_hH_inv, mat6_ePH, mat6_hH, cj, dec6_mul6, dec6_mul6]
  have hX := mem_Xs_of_found 2 hm h.1
  exact ⟨hH⁻¹ * ePH * hH, hX, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem eMH_mem_Xstar : eMH ∈ Xstar := by
  have h := chain_parts.2.1
  simp only [chainXstar, Bool.and_eq_true] at h
  have hm : mat6 (hH⁻¹ * eMH * hH) = dec6 (cj a2HI a2EM a2H) := by
    rw [map_mul, map_mul, mat6_hH_inv, mat6_eMH, mat6_hH, cj, dec6_mul6, dec6_mul6]
  have hX := mem_Xs_of_found 2 hm h.2
  exact ⟨hH⁻¹ * eMH * hH, hX, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem K2star_involutions {u : H6} (hu : u ∈ K2star) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    u = pH ∨ u = qH ∨ u = rH := by
  have hk := chain_parts.2.2.1
  simp only [chainK2, Bool.and_eq_true] at hk
  obtain ⟨k, hkl, hcode, hcanon⟩ := exists_code_closure k2Pairs k2Pairs_all 6 closureOK_K2 hu
  have hmap : k2Pairs.map Prod.fst = a2K2Gens := rfl
  rw [hmap] at hkl hcode
  have hc := allCheck_spec hk.2 hkl
  set c := (closureT a2K2Gens).getD k [] with hcdef
  have hsq : mul6 c c = one6 := by
    refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
    rw [dec6_mul6, hcode, ← map_mul, hu2, map_one, dec6_one6]
  simp only [hsq, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at hc
  rcases hc with ((h | h) | h) | h
  · exact absurd (mat6_injective (by rw [← hcode, h, dec6_one6, map_one])) hu1
  · exact Or.inl (mat6_injective (by rw [← hcode, h, mat6_pH]))
  · exact Or.inr (Or.inl (mat6_injective (by rw [← hcode, h, mat6_qH])))
  · exact Or.inr (Or.inr (mat6_injective (by rw [← hcode, h, mat6_rH])))

theorem pH_word : pH = (rH * ePH * rH) * eMH * (rH * ePH * rH) * eMH := by
  have h := chain_parts.2.2.2.2
  simp only [chainWords, Bool.and_eq_true, beq_iff_eq] at h
  apply mat6_injective
  have e : mat6 ((rH * ePH * rH) * eMH * (rH * ePH * rH) * eMH) =
      dec6 (mul6 (mul6 (mul6 (cj a2R a2EP a2R) a2EM) (cj a2R a2EP a2R)) a2EM) := by
    simp only [map_mul, mat6_rH, mat6_ePH, mat6_eMH, cj, dec6_mul6]
  rw [e, h.1, mat6_pH]

theorem qH_word : qH = ePH * (rH * eMH * rH) * ePH * (rH * eMH * rH) := by
  have h := chain_parts.2.2.2.2
  simp only [chainWords, Bool.and_eq_true, beq_iff_eq] at h
  apply mat6_injective
  have e : mat6 (ePH * (rH * eMH * rH) * ePH * (rH * eMH * rH)) =
      dec6 (mul6 (mul6 (mul6 a2EP (cj a2R a2EM a2R)) a2EP) (cj a2R a2EM a2R)) := by
    simp only [map_mul, mat6_rH, mat6_ePH, mat6_eMH, cj, dec6_mul6]
  rw [e, h.2, mat6_qH]

noncomputable abbrev Slev : G3 →* H6 :=
  CFSG.LargeExtraspecial.A2Mod.FrC.levi (k := 3) (F := ZMod 2)

noncomputable def tv01 : G3 :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1

noncomputable def tv10 : G3 :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) 1

noncomputable def tv12 : G3 :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1

noncomputable def tv21 : G3 :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) 1

theorem mat6_Slev_tv01 : mat6 (Slev tv01) = dec6 a2S01 := by
  unfold tv01
  decide +kernel

theorem mat6_Slev_tv10 : mat6 (Slev tv10) = dec6 a2S10 := by
  unfold tv10
  decide +kernel

theorem mat6_Slev_tv12 : mat6 (Slev tv12) = dec6 a2S12 := by
  unfold tv12
  decide +kernel

theorem mat6_Slev_tv21 : mat6 (Slev tv21) = dec6 a2S21 := by
  unfold tv21
  decide +kernel

theorem Slev_conj_gY :
    gYH * Slev tv01 * gYH⁻¹ = pH ∧ gYH * Slev tv10 * gYH⁻¹ = qH ∧
      gYH * Slev tv12 * gYH⁻¹ = ePH ∧ gYH * Slev tv21 * gYH⁻¹ = eMH := by
  have h := chain_parts.2.2.2.1
  simp only [chainSiegel, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨conj_eq_of_code mat6_gYH mat6_gYH_inv mat6_Slev_tv01 mat6_pH h1,
    conj_eq_of_code mat6_gYH mat6_gYH_inv mat6_Slev_tv10 mat6_qH h2,
    conj_eq_of_code mat6_gYH mat6_gYH_inv mat6_Slev_tv12 mat6_ePH h3,
    conj_eq_of_code mat6_gYH mat6_gYH_inv mat6_Slev_tv21 mat6_eMH h4⟩

theorem Slev_conj_jH :
    jH * Slev tv01 * jH⁻¹ = Slev tv10 ∧ jH * Slev tv10 * jH⁻¹ = Slev tv01 ∧
      jH * Slev tv12 * jH⁻¹ = Slev tv21 ∧ jH * Slev tv21 * jH⁻¹ = Slev tv12 := by
  have h := chain_parts.2.2.2.1
  simp only [chainSiegel, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨conj_eq_of_code mat6_jH mat6_jH_inv mat6_Slev_tv01 mat6_Slev_tv10 h5,
    conj_eq_of_code mat6_jH mat6_jH_inv mat6_Slev_tv10 mat6_Slev_tv01 h6,
    conj_eq_of_code mat6_jH mat6_jH_inv mat6_Slev_tv12 mat6_Slev_tv21 h7,
    conj_eq_of_code mat6_jH mat6_jH_inv mat6_Slev_tv21 mat6_Slev_tv12 h8⟩

theorem Slev_conj_gYJ :
    gYH * jH * Slev tv01 * (gYH * jH)⁻¹ = qH ∧ gYH * jH * Slev tv10 * (gYH * jH)⁻¹ = pH ∧
      gYH * jH * Slev tv12 * (gYH * jH)⁻¹ = eMH ∧ gYH * jH * Slev tv21 * (gYH * jH)⁻¹ = ePH := by
  obtain ⟨a1, a2, a3, a4⟩ := Slev_conj_gY
  obtain ⟨b1, b2, b3, b4⟩ := Slev_conj_jH
  have key : ∀ x y : G3, jH * Slev x * jH⁻¹ = Slev y →
      gYH * jH * Slev x * (gYH * jH)⁻¹ = gYH * Slev y * gYH⁻¹ := fun x y h => by
    rw [← h]
    group
  exact ⟨(key _ _ b1).trans a2, (key _ _ b2).trans a1, (key _ _ b3).trans a4,
    (key _ _ b4).trans a3⟩

end Chain

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
