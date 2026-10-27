module

public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.StandardType.RankOneXfer CFSG.StandardType.PsiDiagChar

theorem exists_unit_scalar_of_upper_action {K k : Type*} [Group K] [Field k]
    (T : Subgroup K) (phi : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hinj : Function.Injective phi)
    (hscalar : ∀ h ∈ T, ∃ c : k, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t))) :
    ∀ h ∈ T, ∃ c : kˣ, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper ((c : k) * t)) := by
  intro h hh
  obtain ⟨c, hc⟩ := hscalar h hh
  obtain ⟨d, hd⟩ := hscalar h⁻¹ (T.inv_mem hh)
  have heq : phi (sl2Upper (1 : k)) = phi (sl2Upper (c * d)) := by
    calc phi (sl2Upper (1 : k))
        = h * (h⁻¹ * phi (sl2Upper (1 : k)) * h) * h⁻¹ := by group
      _ = h * phi (sl2Upper (d * 1)) * h⁻¹ := by
        rw [show h⁻¹ * phi (sl2Upper (1 : k)) * h = phi (sl2Upper (d * 1)) by
          simpa only [inv_inv] using hd 1]
      _ = phi (sl2Upper (c * (d * 1))) := hc (d * 1)
      _ = phi (sl2Upper (c * d)) := by rw [mul_one]
  have hcd : (1 : k) = c * d := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k => A.val 0 1) (hinj heq)
    simpa [CFSG.LieType.Steinberg.coe_sl2Upper] using h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcd
    exact one_ne_zero hcd
  exact ⟨Units.mk0 c hc0, by simpa only [Units.val_mk0] using hc⟩

@[expose] def SelectedSL2Model.ofRootMap {K k : Type*} [Group K] [Field k]
    (D : UniversalRootDatum K) (gamma : Fin D.rank → ℤ) (hroot : gamma ∈ D.roots)
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* K) (hinj : Function.Injective phi)
    (hupper : (sl2UpperUniSub k).map phi = D.rootGroup gamma)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus D)
    (hscalar : ∀ h ∈ ggTorus D, ∃ c : k, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t))) :
    SelectedSL2Model D k gamma :=
  ⟨hroot, phi, hinj, hupper, hdiag,
    exists_unit_scalar_of_upper_action (ggTorus D) phi hinj hscalar⟩

theorem SelectedSL2Model.ofRootMap_range {K k : Type*} [Group K] [Field k]
    (D : UniversalRootDatum K) (gamma : Fin D.rank → ℤ) (hroot : gamma ∈ D.roots)
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* K) (hinj : Function.Injective phi)
    (hupper : (sl2UpperUniSub k).map phi = D.rootGroup gamma)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus D)
    (hscalar : ∀ h ∈ ggTorus D, ∃ c : k, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)))
    (hlower : Set.range (fun t : k => phi (sl2Lower t)) =
      (D.rootGroup (-gamma) : Set K)) :
    (ofRootMap D gamma hroot phi hinj hupper hdiag hscalar).phi.range =
      D.rootGroup gamma ⊔ D.rootGroup (-gamma) := by
  change phi.range = D.rootGroup gamma ⊔ D.rootGroup (-gamma)
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← closure_sl2Upper_sl2Lower_eq_top (k := k),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro z ⟨M, hM, rfl⟩
    rcases hM with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have ht : phi (sl2Upper t) ∈ D.rootGroup gamma := by
        rw [← hupper]
        exact Subgroup.mem_map.mpr
          ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, rfl⟩
      exact (show D.rootGroup gamma ≤ D.rootGroup gamma ⊔ D.rootGroup (-gamma)
        from le_sup_left) ht
    · have ht : phi (sl2Lower t) ∈ D.rootGroup (-gamma) := by
        change phi (sl2Lower t) ∈ (D.rootGroup (-gamma) : Set K)
        rw [← hlower]
        exact ⟨t, rfl⟩
      exact (show D.rootGroup (-gamma) ≤ D.rootGroup gamma ⊔ D.rootGroup (-gamma)
        from le_sup_right) ht
  · apply sup_le
    · intro z hz
      rw [← hupper] at hz
      obtain ⟨M, -, hMz⟩ := Subgroup.mem_map.mp hz
      exact ⟨M, hMz⟩
    · intro z hz
      change z ∈ (D.rootGroup (-gamma) : Set K) at hz
      rw [← hlower] at hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨sl2Lower t, rfl⟩

theorem exists_model_of_rankOneModel {K k : Type} [Group K] [Field k]
    {D : UniversalRootDatum K} (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ model : SelectedSL2Model D k (Pi.single i 1),
      model.phi.range = rankOne D.rootGroup i := by
  obtain ⟨x, C, O, hE, hlin⟩ := hM
  obtain ⟨phi, hinj, hupper, hlower⟩ := hE.rankOne i
  have hup : (sl2UpperUniSub k).map phi = D.rootGroup (Pi.single i 1) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := mem_sl2UpperUniSub_iff.mp ha
      rw [hupper c]
      exact ((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩
    · intro hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, mem_sl2UpperUniSub_iff.mpr ⟨c, rfl⟩, (hupper c).trans hc⟩
  have hscalar : ∀ h ∈ ggTorus D, ∃ c : k, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)) := by
    intro h hh
    obtain ⟨c, hc⟩ := hlin h hh i
    exact ⟨c, fun t => by simpa only [hupper] using hc t⟩
  let model : SelectedSL2Model D k (Pi.single i 1) :=
    SelectedSL2Model.ofRootMap D (Pi.single i 1) (single_mem_roots i) phi hinj hup
      (fun a => map_sl2Diag_mem_ggTorus hE i phi hupper hlower a) hscalar
  refine ⟨model, ?_⟩
  change phi.range = rankOne D.rootGroup i
  exact (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2 hE.param hupper hlower).symm

end CFSG.StandardType.SelectedRoot
