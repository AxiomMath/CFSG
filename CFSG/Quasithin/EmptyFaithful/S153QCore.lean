module

public import CFSG.Quasithin.EmptyFaithful.S153Q1c
public import CFSG.Quasithin.EmptyFaithful.S153Q2c
public import CFSG.Quasithin.EmptyFaithful.S153Q3Ad
public import CFSG.Quasithin.EmptyFaithful.S153Q3Bb
public import CFSG.Quasithin.EmptyFaithful.S153Q4Ac
public import CFSG.Quasithin.EmptyFaithful.S153Q4Bg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S153Q

theorem hatGeomAbs_holds : HatGeomAbs := by
  intro W _ _ hW2 hWc Γ X P hΓ _ hX hPΓ hP2 hP1 V V₁ V₂ hV hI h1 h2 hPV hX'
  obtain ⟨Ah, z, hG⟩ := hatGrp_of_isHatSym (K := MulAut W) hΓ
  have hfpf := hat_z_fpf hW2 hWc hG
  obtain ⟨lab, hO0⟩ := exists_ovals0 hW2 hWc hG hfpf
  have hO : OvalData Ah z lab := OvalData.ofOvalData0 hW2 hG.z_cube hfpf hO0
  have hAX : Ah ≤ X := hG.gen_odd X hX
  have hV16 : Nat.card ↥V = 16 := by
    have hnorm : V₂ ≤ Subgroup.normalizer (V₁ : Set W) := by
      intro g _
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp
    have := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V₁ V₂ hnorm
      (disjoint_iff.mpr hI)
    rw [hV, h1, h2] at this
    simpa using this
  obtain ⟨i, j, hij, hVij⟩ := hat_core_A hW2 hWc hG hfpf hO hPΓ hP2 hP1 V hV16 hPV
  obtain ⟨ρ, hρ, hρi, hρj⟩ := exists_alt_mapsto i j hij
  have hO' := hO.relabel hρ
  have hVij' : V = (fun k => lab (ρ.symm k)) 4 ⊔ (fun k => lab (ρ.symm k)) 5 := by
    have h4 : ρ.symm 4 = i := by rw [← hρi]; simp
    have h5 : ρ.symm 5 = j := by rw [← hρj]; simp
    simp only [h4, h5]
    exact hVij
  exact hat_core_B hW2 hWc hG hfpf hO' hAX V V₁ V₂ hVij' hV hI h1 h2 hX'

end S153Q

end CFSG.Quasithin
