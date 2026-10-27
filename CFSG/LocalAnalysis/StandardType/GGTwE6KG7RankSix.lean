module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7FieldIso
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeToralCentHolds

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

private theorem kg7rank_map_le_normalizer {G H : Type*} [Group G] [Group H]
    {S U : Subgroup G} (f : G →* H) (h : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    S.map f ≤ Subgroup.normalizer (U.map f : Set H) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs u hu
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
  have hmul : f s₀ * f u₀ * (f s₀)⁻¹ = f (s₀ * u₀ * s₀⁻¹) := by
    simp only [map_mul, map_inv]
  rw [hmul]
  exact Subgroup.mem_map.2 ⟨s₀ * u₀ * s₀⁻¹, h s₀ hs₀ u₀ hu₀, rfl⟩

theorem exists_rankSix_recipe_aut
    (hR6 : NoOffTwE6Three.GGTwE6ThreeTwoLocalRankSixInput)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {S : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hS : IsElemAbelian 3 S)
    (hSI : ∀ φ ∈ S, φ ∈ TwE6Delta.RecipeI K n) (h4 : Nat.card S = 3 ^ 4)
    {U : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hSU : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    ∃ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), S ≤ Y ∧
      (∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_recipeR_equiv_twC0 (n := n) hn hK
  let c : MulAut (TwE6Delta.RecipeR K n) ≃*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n)) :=
    MulAut.congr ψ
  let S' : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
      (frobQ 2 n))) := S.map c.toMonoidHom
  let U' : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
      (frobQ 2 n))) := U.map c.toMonoidHom
  have hS'el : IsElemAbelian 3 S' := CFSG.Open.IsElemAbelian.map hS c.toMonoidHom
  have hS'I : S' ≤ LayerSixE.twInndiagAut n := by
    intro φ hφ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hφ
    exact (hψ s).1 (hSI s hs)
  have h4' : Nat.card S' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (K := S) (f := c.toMonoidHom) c.injective, h4]
  have hU'ne : U' ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective (H := U) (f := c.toMonoidHom) c.injective]
    exact hU
  have hU'2 : IsPGroup 2 U' := hU2.map c.toMonoidHom
  have hS'U' : S' ≤ Subgroup.normalizer (U' : Set _) :=
    kg7rank_map_le_normalizer c.toMonoidHom hSU
  obtain ⟨Y', hY'I, hS'Y', hY'el, hY'c⟩ :=
    hR6 (f := n) hn h3 hS'el hS'I h4' ⟨U', hU'ne, hU'2, hS'U'⟩
  refine ⟨Y'.comap c.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact Subgroup.mem_comap.2 (hS'Y' (Subgroup.mem_map.2 ⟨s, hs, rfl⟩))
  · intro φ hφ
    exact (hψ φ).2 (hY'I (Subgroup.mem_comap.1 hφ))
  · exact CFSG.Open.IsElemAbelian.comap (f := c.toMonoidHom) hY'el c.injective
  · rw [← Subgroup.card_map_of_injective (K := Y'.comap c.toMonoidHom)
        (f := c.toMonoidHom) c.injective,
      Subgroup.map_comap_eq_self_of_surjective (f := c.toMonoidHom) c.surjective Y', hY'c]

end CFSG.StandardType.TwE6KG7
