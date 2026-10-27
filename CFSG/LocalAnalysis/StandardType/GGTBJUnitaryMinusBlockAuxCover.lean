module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxCent
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxComp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Multiplicative
  CFSG.ComponentClassification CFSG.RankThree.CALinearPlane

theorem exists_alignedBlock_of_isComponentOf_of_centralizer
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {f m ε p : ℕ}
    [Fact p.Prime]
    {h : UnitaryFieldData 2 f F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε}
    (hmain : ∀ (E : Set (Multiplicative (Fin m → ZMod p))) (K : Subgroup (hypSU h m ε)),
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer (τ '' E)) →
      (∃ S : Finset (Fin m), S.Nonempty ∧ K = hypBlock h (zeroCoords S)) ∨
        ∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (w : hypSU h m ε),
          (∀ i, s i = 1 ∨ s i = -1) ∧
          (∀ t : Fin m → ZMod p, w * τ (Multiplicative.ofAdd t) * w⁻¹ =
            τ (Multiplicative.ofAdd fun i => s i * t i)) ∧
          2 ≤ S.card ∧
          K = (coordBlockSL F S).map ((MulAut.conj w).toMonoidHom.comp (leviSU h ε)))
    {φ : hypSU h m ε →* G} (hker : φ.ker ≤ Subgroup.center (hypSU h m ε))
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {C : Set G}
    (hC : ∀ c ∈ C, ∃ v, ∀ g ∈ φ.range,
      c * g * c⁻¹ = hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹)
    {J : Subgroup G} (hJ : CFSG.Assembly.IsComponentOf J (φ.range ⊓ Subgroup.centralizer C)) :
    (∃ S : Finset (Fin m), S.Nonempty ∧ J = (hypBlock h (zeroCoords S)).map φ) ∨
      ∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (w : hypSU h m ε),
        (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ t : Fin m → ZMod p, w * τ (Multiplicative.ofAdd t) * w⁻¹ =
          τ (Multiplicative.ofAdd fun i => s i * t i)) ∧
        2 ≤ S.card ∧
        J = (coordBlockSL F S).map ((φ.comp (MulAut.conj w).toMonoidHom).comp
          (leviSU h ε)) := by
  classical
  have hp : p.Prime := Fact.out
  let χ : G → Multiplicative (Fin m → ZMod p) := fun c =>
    if hc : c ∈ C then
      (MulEquiv.piMultiplicative (fun _ : Fin m => ZMod p)).symm (Classical.choose (hC c hc))
    else 1
  have hχ : ∀ c ∈ C, ∀ g ∈ φ.range,
      c * g * c⁻¹ = φ (τ (χ c)) * g * (φ (τ (χ c)))⁻¹ := by
    intro c hc g hg
    have h1 := Classical.choose_spec (hC c hc) g hg
    have h2 : hypFrame φ τ (Classical.choose (hC c hc)) = φ (τ (χ c)) := by
      simp only [hypFrame, χ, dif_pos hc, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rwa [h2] at h1
  let E : Set (Multiplicative (Fin m → ZMod p)) := χ '' C
  let H : Subgroup (hypSU h m ε) := Subgroup.centralizer (τ '' E)
  have hHmap : H.map φ = φ.range ⊓ Subgroup.centralizer C :=
    map_centralizer_eq_inf_centralizer (h := h) (τ := τ) (φ := φ) hker hkp χ hχ
  have hJ' : CFSG.Assembly.IsComponentOf J (H.map φ) := by
    rw [hHmap]
    exact hJ
  let ψ : ↥H →* G := φ.comp H.subtype
  have hψrange : ψ.range = H.map φ := by
    change (φ.comp H.subtype).range = H.map φ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerψ : ψ.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have hx1 : φ ((x : ↥H) : hypSU h m ε) = 1 := MonoidHom.mem_ker.mp hx
    have hxZ : ((x : ↥H) : hypSU h m ε) ∈ Subgroup.center (hypSU h m ε) :=
      hker (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ ((y : ↥H) : hypSU h m ε)
  obtain ⟨K, hKcomp, hKmap⟩ :=
    CFSG.exists_isComponentOf_map_eq_of_ker_le_center hkerψ (J := J) (ψ := ψ)
      (by rw [hψrange]; exact hJ')
  have hK'comp : CFSG.Assembly.IsComponentOf (K.map H.subtype) H := by
    have hkerH : H.subtype.ker ≤ Subgroup.center ↥H := by
      rw [Subgroup.ker_subtype]
      exact bot_le
    have h := CFSG.ComponentClassification.HarrisLit.N36.isComponentOf_map_of_ker_le_center
      H.subtype hkerH hKcomp
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hblock := hmain E (K.map H.subtype) hK'comp
  have hJK : J = (K.map H.subtype).map φ := by
    rw [Subgroup.map_map]
    exact hKmap.symm
  rcases hblock with ⟨S, hS, hJeq⟩ | ⟨S, s, w, hs, hw, hS, hJeq⟩
  · left
    refine ⟨S, hS, ?_⟩
    rw [hJK, hJeq]
  · right
    refine ⟨S, s, w, hs, hw, hS, ?_⟩
    rw [hJK, hJeq, Subgroup.map_map, MonoidHom.comp_assoc]

end CFSG.StandardType.SuSplitRootGen

end
