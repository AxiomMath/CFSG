module

public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE

variable {Ω : Type} [Field Ω]

@[expose] def E6AdToral (X : Subgroup (ModGL Tag.E6 Ω)) : Prop :=
  ∃ C ∈ adjointGroup Tag.E6 Ω, ∀ x ∈ X, C * x * C⁻¹ ∈ torusGroup Tag.E6 Ω

@[expose] def E6AdLangToral (Fr : Ω →+* Ω) (X : Subgroup (ModGL Tag.E6 Ω)) : Prop :=
  ∃ v : WeylGroup Tag.E6, ∃ g0 ∈ adjointGroup Tag.E6 Ω,
    twistE6 Ω Fr g0 = g0 * canonicalRep (coxeterSystem Tag.E6) Ω v ∧
    ∀ x ∈ X, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) Ω v)
      (twistE6 Ω Fr)).map (MulAut.conj g0).toMonoidHom

theorem e6AdToral_mono {X Y : Subgroup (ModGL Tag.E6 Ω)} (hXY : X ≤ Y) (h : E6AdToral Y) :
    E6AdToral X :=
  let ⟨C, hC, hY⟩ := h
  ⟨C, hC, fun x hx => hY x (hXY hx)⟩

theorem e6AdToral_map_conj {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (X : Subgroup (ModGL Tag.E6 Ω)) :
    E6AdToral (X.map (MulAut.conj g).toMonoidHom) ↔ E6AdToral X := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C * g, mul_mem hC hg, fun x hx => ?_⟩
    have hgx := h _ (Subgroup.mem_map_of_mem _ hx)
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show C * (g * x * g⁻¹) * C⁻¹ = C * g * x * (C * g)⁻¹ by group] at hgx
  · rintro ⟨C, hC, h⟩
    refine ⟨C * g⁻¹, mul_mem hC (inv_mem hg), fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show C * g⁻¹ * (g * x * g⁻¹) * (C * g⁻¹)⁻¹ = C * x * C⁻¹ by group]
    exact h x hx

theorem exists_rootDiagUnit_of_mem_langTorus {Fr : Ω →+* Ω} {v : WeylGroup Tag.E6}
    {g0 x : ModGL Tag.E6 Ω}
    (hx : x ∈ (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) Ω v)
      (twistE6 Ω Fr)).map (MulAut.conj g0).toMonoidHom) (hx3 : x ^ 3 = 1) :
    ∃ b : Fin Tag.E6.rank → Ωˣ, (∀ i, b i ^ 3 = 1) ∧ x = g0 * rootDiagUnit Tag.E6 b * g0⁻¹ ∧
      canonicalRep (coxeterSystem Tag.E6) Ω v * twistE6 Ω Fr (rootDiagUnit Tag.E6 b) *
        (canonicalRep (coxeterSystem Tag.E6) Ω v)⁻¹ = rootDiagUnit Tag.E6 b := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨hT, hF⟩ := mem_twistedTorusOf.1 ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx3 ⊢
  refine ⟨b, fun i => ?_, rfl, hF⟩
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at hx3
  have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_pow, rootDiagUnit_one, hx3]
  simpa using congrFun (rootDiagUnit_injective h1) i

end CFSG.StandardType.SCFourCover

end
