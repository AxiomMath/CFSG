module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitExcModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoord
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}

private theorem pxB_isRefl_map {n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {t : MulAut ↥Bs}
    (ht : GGIsReflection p t) :
    ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) t) :=
  (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) t).mp ht

private theorem pxB_oneClass_map {n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {A : Subgroup (MulAut ↥Bs)}
    (hone : ∀ s ∈ A, ∀ t ∈ A, GGIsReflection p s → GGIsReflection p t →
      ∃ g ∈ A, t = g * s * g⁻¹) :
    ZS.OneClass p (A.map (ggLin (p := p) (bCoordIota eta))) := by
  intro x hx y hy hxr hyr
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  have hsr : GGIsReflection p s :=
    (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) s).mpr hxr
  have htr : GGIsReflection p t :=
    (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) t).mpr hyr
  obtain ⟨g, hg, hgt⟩ := hone s hs t ht hsr htr
  refine ⟨ggLin (p := p) (bCoordIota eta) g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
  rw [hgt]
  simp

private theorem pxB_modelIso_map {n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {A : Subgroup (MulAut ↥Bs)}
    {k : ZS.ExcRow}
    (hmod : ∃ f : ↥(ZS.model k) ≃* ↥A,
      ∀ g : ↥(ZS.model k), ZS.IsReflMat g.1 ↔ GGIsReflection p (f g : MulAut ↥Bs)) :
    ZS.ModelIso p k (A.map (ggLin (p := p) (bCoordIota eta))) := by
  obtain ⟨f₀, hf⟩ := hmod
  let E := Subgroup.equivMapOfInjective A (ggLin (p := p) (bCoordIota eta))
    (ggLin_injective (bCoordIota eta))
  refine ⟨f₀.trans E, fun g => ?_⟩
  have hcoe : (E (f₀ g) : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) =
      ggLin (p := p) (bCoordIota eta) (f₀ g : MulAut ↥Bs) :=
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  change ZS.IsReflMat g.1 ↔ ZS.IsRefl p
    ((f₀.trans E) g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p))
  have htrans : ((f₀.trans E) g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) =
      E (f₀ g) := rfl
  rw [htrans, hcoe, hf g]
  exact ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) (f₀ g : MulAut ↥Bs)

theorem exists_conj_not_dvd_48_of_modelIso [Fact p.Prime]
    (hp2 : p ≠ 2) {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)} {k : ZS.ExcRow} (hk : k.needsModel)
    (hone : ∀ s ∈ A, ∀ t ∈ A, GGIsReflection p s → GGIsReflection p t →
      ∃ g ∈ A, t = g * s * g⁻¹)
    (hmod : ∃ f : ↥(ZS.model k) ≃* ↥A,
      ∀ g : ↥(ZS.model k), ZS.IsReflMat g.1 ↔ GGIsReflection p (f g : MulAut ↥Bs))
    {r₁ r₂ : MulAut ↥Bs} (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A) (hr₁ : GGIsReflection p r₁)
    (hr₂ : GGIsReflection p r₂) (hord : orderOf (r₁ * r₂) = 3) :
    ∃ g ∈ A, ¬ (Commute (g * r₁ * g⁻¹) r₁ ∧ Commute (g * r₁ * g⁻¹) r₂) ∧
      ¬ Nat.card (Subgroup.closure ({r₁, r₂, g * r₁ * g⁻¹} : Set (MulAut ↥Bs))) ∣ 48 := by
  let lin := ggLin (p := p) (bCoordIota eta)
  have hlin_inj : Function.Injective lin := ggLin_injective (bCoordIota eta)
  have hone' : ZS.OneClass p (A.map lin) := pxB_oneClass_map hp2 eta hone
  have hmod' : ZS.ModelIso p k (A.map lin) := pxB_modelIso_map hp2 eta hmod
  have hwit := ZS.wit_exc_model (p := p) k hk hone' hmod'
    (lin r₁) (Subgroup.mem_map.mpr ⟨r₁, h₁, rfl⟩) (pxB_isRefl_map hp2 eta hr₁)
  have hord' : orderOf (lin r₁ * lin r₂) = 3 := by
    rw [← map_mul, orderOf_injective lin hlin_inj, hord]
  obtain ⟨g', hg', hnc, hndvd⟩ :=
    hwit (lin r₂) (Subgroup.mem_map.mpr ⟨r₂, h₂, rfl⟩) (pxB_isRefl_map hp2 eta hr₂) hord'
  obtain ⟨g, hg, hg'eq⟩ := Subgroup.mem_map.mp hg'
  have hgc : lin (g * r₁ * g⁻¹) = g' * lin r₁ * g'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg'eq]
  refine ⟨g, hg, ?_, ?_⟩
  · rintro ⟨hc₁, hc₂⟩
    refine hnc ⟨?_, ?_⟩
    · rw [← hgc]
      exact hc₁.map lin
    · rw [← hgc]
      exact hc₂.map lin
  · intro hd
    refine hndvd ?_
    have hS : lin '' ({r₁, r₂, g * r₁ * g⁻¹} : Set (MulAut ↥Bs)) =
        ({lin r₁, lin r₂, g' * lin r₁ * g'⁻¹} : Set _) := by
      simp only [Set.image_insert_eq, Set.image_singleton, hgc]
    have hcard : Nat.card (Subgroup.closure ({lin r₁, lin r₂, g' * lin r₁ * g'⁻¹} :
          Set ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)))) =
        Nat.card (Subgroup.closure ({r₁, r₂, g * r₁ * g⁻¹} : Set (MulAut ↥Bs))) := by
      rw [← hS, ← MonoidHom.map_closure]
      exact Subgroup.card_map_of_injective hlin_inj
    rw [hcard]
    exact hd

end CFSG.StandardType

end
