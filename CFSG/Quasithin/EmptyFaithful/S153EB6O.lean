module

public import CFSG.Quasithin.EmptyFaithful.S153EB6N
public import CFSG.Quasithin.EmptyFaithful.S153EB6K

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL

theorem input15358Two_main (h : G64.LemmaG64) : Input15358Two := by
  intro W instC instF hexp H K a W₁ W₂ hHsq _hH2 _hHirr hKmin hnonab haH _ha1 ha2 hT hdir hirr₁
    hirr₂ _hcard h8₁ h8₂ ha₁ ha₂ hc₁ hc₂ h3
  have hC : Ctx H K a := ⟨hHsq, hKmin.1, hKmin.2.1, haH, ha2, hT⟩
  have hS₁ : SumCtx K a W₁ := ⟨hirr₁.2.1, ha₁, hirr₁, hc₁⟩
  have hS₂ : SumCtx K a W₂ := ⟨hirr₂.2.1, ha₂, hirr₂, hc₂⟩
  have hI₁ := induced_of_summand h hexp hC hS₁ hKmin hnonab h8₁
  have hI₂ := induced_of_summand h hexp hC hS₂ hKmin hnonab h8₂
  have hMF₁ := model_facts hI₁
  have hMF₂ := model_facts hI₂
  have hN₁ : ∀ n ∈ Nk K W₁, n = 1 := Nk_eq_bot_of_model hC hdir.1 hS₁ hS₂ hI₂ hMF₂ h3
  have hinj : Function.Injective (indResK hC hS₁) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    exact Subtype.ext (hN₁ _ ⟨k.2, (indResK_eq_one_iff hC hS₁).1 hk⟩)
  rcases hMF₁.case with ⟨hGtop, hcard8, hKbG⟩ | ⟨g, hgG, hg3, hgc⟩
  · refine realizes_of_top hexp hS₁.KU hcard8 (indResK hC hS₁) (fun k u => rfl) hinj ?_
    intro φ
    have : φ ∈ indK hC hS₁ := by rw [hKbG, hGtop]; exact Subgroup.mem_top φ
    exact (mem_indK_iff hC hS₁).1 this
  · exfalso
    have hgK : g ∈ indK hC hS₁ := mem_Kb_of_order_three hI₁ hgG hg3
    obtain ⟨k, hk⟩ := (mem_indK_iff hC hS₁).1 hgK
    have hk3 : orderOf (k : MulAut W) = 3 := by
      rw [Subgroup.orderOf_coe, ← orderOf_injective _ hinj k, hk]
      exact hg3
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])
    let k' : ↥K := ⟨a * (k : MulAut W)⁻¹ * a, by
      have := hC.Kn a hC.aH _ (K.inv_mem k.2)
      rwa [hainv] at this⟩
    have hk' : indResK hC hS₁ k' = indA hC hS₁ * (indResK hC hS₁ k)⁻¹ * indA hC hS₁ := by
      ext u
      show ((indResK hC hS₁ k' u : ↥W₁) : W) = a ((((indResK hC hS₁ k)⁻¹ (indA hC hS₁ u) : ↥W₁)) : W)
      rw [← map_inv]
      rfl
    have hprod : indResK hC hS₁ (k * k') = 1 := by
      rw [map_mul, hk', hk]
      have h1 : indA hC hS₁ * g = g * indA hC hS₁ := hgc.symm
      calc g * (indA hC hS₁ * g⁻¹ * indA hC hS₁) = (g * indA hC hS₁) * g⁻¹ * indA hC hS₁ := by group
        _ = (indA hC hS₁ * g) * g⁻¹ * indA hC hS₁ := by rw [h1]
        _ = indA hC hS₁ * indA hC hS₁ := by group
        _ = 1 := by rw [← pow_two]; exact indA_sq hC hS₁
    have hker := hN₁ _ ⟨(k * k').2, (indResK_eq_one_iff hC hS₁).1 hprod⟩
    have hcomm : (k : MulAut W) * a = a * (k : MulAut W) := by
      have h1 : (k : MulAut W) * (a * (k : MulAut W)⁻¹ * a) = 1 := hker
      have h2 : (k : MulAut W) * a * (k : MulAut W)⁻¹ * a = 1 := by
        rw [← h1]; group
      have h3' : (k : MulAut W) * a = a⁻¹ * (k : MulAut W) := by
        have : (k : MulAut W) * a * (k : MulAut W)⁻¹ = a⁻¹ := mul_eq_one_iff_eq_inv.1 h2
        calc (k : MulAut W) * a = ((k : MulAut W) * a * (k : MulAut W)⁻¹) * (k : MulAut W) := by group
          _ = a⁻¹ * (k : MulAut W) := by rw [this]
      rw [h3', hainv]
    obtain ⟨r, hr, hkr⟩ := h3 _ (hC.KH k.2) hk3
    exact hkr (commV_invariant_of_comm hcomm hr)

end S153EB6

namespace S153E

theorem input15358Two_of_lemmaG64 (h : G64.LemmaG64) : Input15358Two :=
  S153EB6.input15358Two_main h

end S153E

end CFSG.Quasithin
