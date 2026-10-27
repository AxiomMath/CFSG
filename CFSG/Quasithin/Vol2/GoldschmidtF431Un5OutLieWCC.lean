module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieWCB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5w_not_conj {u : hypSU hK 2 1} (huV : u ∈ Vsub hK) (hdet : (Yof u).det ≠ 0)
    (hk : ∃ k : MulAut (hypPSU hK 2 1), k * innM hK (z₁SU hK) * k⁻¹ = innM hK u) : False := by
  have hz2 : z₂SU hK ∈ Vsub hK := vSU_mem_Vsub (isHerm_swap hK)
  have hdet2 : (Yof (z₂SU hK)).det ≠ 0 := by
    rw [Yof_z₂SU, Matrix.det_fin_two_of]
    simp
  obtain ⟨A, hA, hl⟩ := exists_lev_conj_of_det_ne_zero huV hz2 hdet hdet2
  obtain ⟨k, hk⟩ := hk
  have h1 : (innM hK (lev A hA) * k) * innM hK (z₁SU hK) * (innM hK (lev A hA) * k)⁻¹ =
      innM hK (z₂SU hK) := by
    calc (innM hK (lev A hA) * k) * innM hK (z₁SU hK) * (innM hK (lev A hA) * k)⁻¹
        = innM hK (lev A hA) * (k * innM hK (z₁SU hK) * k⁻¹) * (innM hK (lev A hA))⁻¹ := by
          group
      _ = innM hK (lev A hA * u * (lev A hA)⁻¹) := by rw [hk, map_mul, map_mul, map_inv]
      _ = innM hK (z₂SU hK) := by rw [hl]
  have h2 : cj5 hK ((innM hK (lev A hA) * k) (z5Y hK)) = cj5 hK (t5Y hK) := by
    rw [← aut5_mul_cj5_mul_inv]
    exact h1
  exact noconj_Y _ (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective (u5_center_eq_bot hK) h2)

theorem un5_W_cls (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) (y : MulAut (hypPSU hK 2 1))
    (hy : y ∈ spWf T (fieldP hK (bar5 hK)))
    (hk : ∃ k : MulAut (hypPSU hK 2 1), k * innM hK (z₁SU hK) * k⁻¹ = y) :
    y ∈ (ZPsub hK).map (innM hK) := by
  have _hf := hf
  obtain ⟨u, hu, rfl, hfix, hc⟩ := un5w_central hK hU hT hb hy
  have huV := un5w_mem_Vsub hK hu hfix hc
  have h11 := un5w_Yof_11 hK huV hc
  have h10 := un5w_Yof_10 hK huV hfix
  have h01 : Yof u 0 1 = 0 := by
    by_contra hne
    refine un5w_not_conj hK huV ?_ hk
    rw [Matrix.det_fin_two, h11, h10]
    simpa using hne
  exact ⟨u, un5w_mem_ZPsub hK hu huV h01 h11, rfl⟩

end CFSG.Quasithin.H13.F431.Un.OL5
