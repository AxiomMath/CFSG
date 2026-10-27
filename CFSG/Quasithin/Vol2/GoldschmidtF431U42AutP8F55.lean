module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Fin
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cj

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

section Conj

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem Conf55.of_conj (c : AutCtx G M₁ M₂ z) {g : G} (hg : g ∈ M₁ ⊓ M₂) {f : G}
    (h : Conf55 (c.conj hg) f) : Conf55 c f := by
  obtain ⟨hX, hM, ι', h1, h2⟩ := h
  have hgM : g⁻¹ ∈ M₁ ⊔ M₂ := inv_mem (le_sup_left (a := M₁) (b := M₂) hg.1)
  refine ⟨hX, hM, ι'.trans (MulAut.conj (⟨g⁻¹, hgM⟩ : ↥(M₁ ⊔ M₂))), fun x => ?_, fun x => ?_⟩
  · have h1x : ((ι' (x : Ah) : ↥(M₁ ⊔ M₂)) : G) = g * (c.iso.phi1 x : G) * g⁻¹ := h1 x
    show g⁻¹ * ((ι' (x : Ah) : ↥(M₁ ⊔ M₂)) : G) * (g⁻¹)⁻¹ = (c.iso.phi1 x : G)
    rw [h1x]
    group
  · have h2x : ((ι' (x : Ah) : ↥(M₁ ⊔ M₂)) : G) = g * (c.iso.phi2 x : G) * g⁻¹ := h2 x
    show g⁻¹ * ((ι' (x : Ah) : ↥(M₁ ⊔ M₂)) : G) * (g⁻¹)⁻¹ = (c.iso.phi2 x : G)
    rw [h2x]
    group

end Conj

theorem u42AutF55_of_iota
    (hι : U42AutIotaOfCox) : U42AutF55 := by
  intro G _ _ M₁ M₂ z c T hT f hfT hf R hR hTR hC h54
  obtain ⟨g, hgB, -, hTg, hfg⟩ := exists_norm c hT hfT hf
  have hF : (c.conj hgB).iso.toG fhB = f := by
    rw [hfg]
    exact AutIso.toG_conjIso c.iso hgB fhB
  have hT' : (c.conj hgB).iso.imgG That = T := by
    rw [hTg]
    exact AutIso.imgG_conjIso c.iso hgB That
  rw [← hF] at hR hTR hC h54 ⊢
  rw [← hT'] at hTR hC
  exact Conf55.of_conj c hgB
    (conf55_std (c.conj hgB) hι (F55Ctx.of_conf (c.conj hgB) hR hTR hC h54))

end CFSG.Quasithin.H13.F431.U42Aut
