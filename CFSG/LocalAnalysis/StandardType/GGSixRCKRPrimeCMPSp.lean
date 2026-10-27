module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

section Genuine


theorem rckClassicalModelID_PSp {X : Type} [Group X] [Finite X] {n f : ℕ} (hf : 1 ≤ f)
    {ψ : (ggU .PSp n f).K →* X} {G₀ : Subgroup X} (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D J K : Subgroup X} {d e : X} (hB₁ : IsElemAbelian p B₁) (hDB₁ : D ≤ B₁)
    (hDcard : Nat.card D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hp4 : p ^ 4 ≤ Nat.card B₁) (hB₁N : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hID : ∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSp n f).D ψ b) (heD : e ∈ D)
    (hK : IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e})) (hJK : J ≤ K) (hKJ : K ≠ J)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X)) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    RCKClassicalModelID K B₁ := by
  classical
  let F := GaloisField 2 f
  let ψ' : ↥(CFSG.Open.StatedSp n F) →* X := ψ
  have hker' : ψ'.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n F) := hker
  have hID' : ∀ b ∈ B₁, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ' b := hID
  have hrange' : ψ'.range = G₀ := hrange
  have hB₁N' : B₁ ≤ Subgroup.normalizer (ψ'.range : Set X) := hrange' ▸ hB₁N
  have heB₁ : e ∈ B₁ := hDB₁ heD
  have hep : e ^ p = 1 := hB₁.2 e heB₁
  have hB₁e : ∀ b ∈ B₁, Commute b e := fun b hb =>
    congrArg Subtype.val (hB₁.1.is_comm.comm (⟨b, hb⟩ : B₁) (⟨e, heB₁⟩ : B₁))
  have hKq : IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hK.2.2
  obtain ⟨s, hsSp, hslift, hsodd, ε, hε, -, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSp hp hp2 hep hf ψ hrange hker (hB₁N heB₁) (hID e heB₁) hK
  let s₀ : ↥(CFSG.Open.StatedSp n F) := ⟨s, hsSp⟩
  have hs₀ : ∀ u, e⁻¹ * ψ' u * e = ψ' (s₀ * u * s₀⁻¹) := by
    intro u
    obtain ⟨u', hu'1, hu'2⟩ := hslift u
    have hu' : u' = s₀ * u * s₀⁻¹ := Subtype.ext hu'1
    rw [← hu']
    exact hu'2
  have hJ'map' : J'.map ψ' = K := hJ'map
  have hJ'G : J' ≤ glBlockCentralizer (CFSG.Open.StatedSp n F).subtype {s} ε := by
    refine hJ'comp.1.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  have hperf : ⁅J', J'⁆ = J' := LayerFacts.ggCommutator_eq_of_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'comp.2.2)
  rcases rckBlockModel_PSp hf hsSp hsodd hε hJ'comp with
    ⟨t, m, g, κ, ht, hg, hκ⟩ | ⟨hF2, ⟨Φ⟩⟩ | ⟨m, Q, E, _, _, _, hm, -, Φ, -⟩
  · refine rckClassicalModelID_of_block hker' hJ'G hκ ht hg hJ'map' fun b hb => ?_
    exact rckLiftToBlock_PSp hker' hs₀ hε hJ'G hperf (hB₁N' hb) (hID' b hb) (hB₁e b hb)
      (hJ'map' ▸ hB₁K hb)
  · exact absurd (rckEq_of_block_Sp4Two hp hp2 hB₁ hDcard hB₁J hp4 hJK hKq hdD hJ hker' hs₀ hε
      hJ'G hJ'map' hB₁N' hID' hB₁e hF2 Φ) hKJ
  · exact absurd (rckEq_of_block_unitarySmall hp hp2 hB₁ hDcard hB₁J hp4 hJK hKq hdD hJ hker'
      hs₀ hε hJ'G hJ'map' hB₁N' hID' hB₁e hm Φ) hKJ

theorem rckClassicalCompModelAt_PSp : RCKClassicalCompModelAt .PSp := by
  intro X _ _ n f ψ p G₀ A B₁ D J L K e h hKJ hID
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, -, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, -, hB1J, hB1Jc, hp4, -, -, -, -, -,
      hJcompD, -, -, -, -, -, -, heD, he1, hKcomp, hJK, -⟩
  obtain ⟨hB₁K, d, hdD, -, hJd⟩ := le_normalizer_and_exists_isComponentOf_of_plane hp hAel hB1A
    hDB1 hDcard hAnorm hB1J hJcompD heD he1 hKcomp hJK
  exact rckClassicalModelID_PSp hGG.1.1.2.1 hGG.2.1.1 hGG.2.1.2 hp hp2 (hAel.mono hB1A) hDB1
    hDcard hB1Jc hp4 (hB1A.trans hAnorm) (fun b hb => hID b (hB1A hb)) heD hKcomp hJK hKJ hB₁K
    hdD hJd

end Genuine

end CFSG.StandardType.RCKRP
