module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Good
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

theorem u42AutFusionZ :
    U42AutFusionZ := by
  intro G _ _ M₁ M₂ z c f hf hconj
  obtain ⟨f', hf', rfl⟩ := hf
  obtain ⟨a, haB, hfa⟩ := good_conj hf'
  have h1 : f' = ⟨a, haB⟩ * fhB * (⟨a, haB⟩ : ↥Bh)⁻¹ := Subtype.ext hfa
  obtain ⟨d, hd⟩ := isConj_iff.1 hconj
  refine no_conj_core c (c0 := d * c.iso.toG ⟨a, haB⟩) ?_
  rw [h1, AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv] at hd
  refine Eq.trans ?_ hd
  group

end CFSG.Quasithin.H13.F431.U42Aut
