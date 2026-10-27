module

public import CFSG.Quasithin.Vol2.Ch11SecU1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.Sig

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem mem_centralizer_conj {b g y : G} :
    y ∈ Subgroup.centralizer {g * b * g⁻¹} ↔ g⁻¹ * y * g ∈ Subgroup.centralizer {b} := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * y * g * b = g⁻¹ * (y * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * y) * g := by rw [h]
      _ = b * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * b * g⁻¹) = g * ((g⁻¹ * y * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * y := by group

theorem sigmaFacts_conj {L : Subgroup G} [hL : L.Normal] {b : G} (h : SigmaFacts L b) (g : G) :
    SigmaFacts L (g * b * g⁻¹) := by
  obtain ⟨L₀, hle, hs, hnab, hN, hC⟩ := h
  have : IsSimpleGroup ↥L₀ := hs
  set f := (MulAut.conj g).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj g).injective
  let e : ↥L₀ ≃* ↥(L₀.map f) := L₀.equivMapOfInjective f hfi
  refine ⟨L₀.map f, ?_, e.symm.isSimpleGroup, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp (hle hx)
    refine ⟨hL.conj_mem x hxL g, mem_centralizer_conj.mpr ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g ∈ _
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  · obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  · intro y hy
    rw [← Subgroup.map_equiv_normalizer_eq L₀ (MulAut.conj g), Subgroup.mem_map_equiv]
    exact hN (mem_centralizer_conj.mp hy)
  · refine le_bot_iff.mp fun z hz => ?_
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    have h1 : g⁻¹ * z * g ∈ L ⊓ Subgroup.centralizer (L₀ : Set G) := by
      refine ⟨by simpa using hL.conj_mem z hzL g⁻¹, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have h2 := Subgroup.mem_centralizer_iff.mp hzC (g * x * g⁻¹) ⟨x, hx, rfl⟩
      calc x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h2]
        _ = g⁻¹ * z * g * x := by group
    rw [hC, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

end CFSG.Quasithin.Vol2.Ch11.SecU1.Sig
