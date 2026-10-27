module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameData
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameCentral
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_frameL (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hNI : GGE6DepNonIsoPt) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) {K : Subgroup G} (hE : GGE6DepPerpCfg 3 Bs L K) (hxL : x ∉ L) :
    ∃ (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxBs : x ∈ Bs) (R : Type) (_ : Group R)
      (I : Set (MulAut R)) (ψ : ↥L →* R) (Φ : ↥(ggGamma L hBsN).range →*
        Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥L) (w : Fin 6 → ↥L)
      (ι : Additive ↥Bs ≃+ E6Dep.Vec6),
      GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range ∧
      Nat.card (ggGamma L hBsN).range = 3 ^ 5 ∧
      GGE6ThreeWeylModelWith ψ.ker (ggGamma L hBsN).range Φ T w ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) ∧
      (∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) ∧
      ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1 ∧
      (∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0) ∧
      (∀ b : ↥Bs, ι (Additive.ofMul b) 5 = 0 →
        E6Dep.coordE.mulVec (ι (Additive.ofMul b)) =
          Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b))) ∧
      (∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ E6Dep.closureL, E6Dep.ActsAs ι φ g) ∧
      (∀ g ∈ E6Dep.closureL, ∃ φ ∈ ggAutomizer L Bs, E6Dep.ActsAs ι φ g) ∧
      GGE6DepNonIsoProp R I := by
  obtain ⟨hBsN, R, _, I, ψ, hTB, hcard, hmodel, hNIP⟩ :=
    ggE6Dep_known_data_model hRig hM hNI hcfg hinn hE
  obtain ⟨hp3, hcardBs, -⟩ := hE
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  obtain ⟨Φ, T, w, hwith⟩ := hmodel
  have hZ := ggE6Dep_hZ hcfg hxL
  have hBsL := ggE6Dep_hBsL hcfg hp3 hBsN hcard ⟨Φ, T, w, hwith⟩
  obtain ⟨ι, hι5, hιL, hιΦ⟩ :=
    E6Dep.ggE6Dep_exists_coordinates hcfg hcardBs hBsN hxBs hZ hBsL hcard hwith
  obtain ⟨h₁, h₂⟩ := E6Dep.ggE6Dep_automizer_closureL hcfg hBsN hxBs hZ hBsL hcard hwith ι hι5
    hιL hιΦ
  exact ⟨hBsN, hxBs, R, inferInstance, I, ψ, Φ, T, w, ι, hTB, hcard, hwith, hZ, hBsL, hι5, hιL,
    hιΦ, h₁, h₂, hNIP⟩

end CFSG.StandardType

end
