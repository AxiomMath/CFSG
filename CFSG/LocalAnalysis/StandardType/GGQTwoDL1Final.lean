module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Local
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseO
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

section Inputs


theorem ggQTwoDL1InvFixInputOn_of_charts {R : ℕ → Prop} (hmod : QTwoDL1OrthModel)
    (hCh : GGQTwoDL1ChartInputOn R) : GGQTwoDL1InvFixInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM _ X hX t htC htN ht2
  rcases hCh G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX with
    ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, hfull⟩ | ⟨Φ, hF, h5, hZ⟩
  · exact qtwoDL1_invFix_unit hK h hrange hd hfull htC htN ht2
  · exact qtwoDL1_invFix_orth hmod (ggRouteCfg_prime hcfg.1).1 Φ hF h5 hZ htC htN ht2

theorem ggQTwoDL1InvFixInput_of_charts (hmod : QTwoDL1OrthModel) (hCh : GGQTwoDL1ChartInput) :
    GGQTwoDL1InvFixInput :=
  ggQTwoDL1InvFixInputOn_of_charts hmod hCh

theorem qtwoDL1_edgeBase_of_chartL {R : ℕ → Prop} (ha₀ : GGLNoncyclicInput)
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (_hmod : QTwoDL1OrthModel)
    (hfix : GGQTwoDL1InvFixInputOn R) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} {e' : Fin m ≃ ι} (hm : R m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hchart : QTwoDL1Chart p B Bs L) :
    ∃ r₀ ∈ ggCoxRefl M e, ∃ r₀' ∈ ggCoxRefl M e, r₀ * r₀' ≠ r₀' * r₀ ∧
      Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216 := by
  have hodd := qtwoDL1_odd_of_cfg ha₀ hL hP hfix hcfg hm hM
  have hroute := hcfg.1
  have hpres := hcfg.2.2.2.1
  have h3 := qtwo_label_le_three e' hM
  have hbase : ∃ r₀ ∈ ggAutomizer L Bs, GGIsReflection p r₀ ∧ ∃ r₀' ∈ ggAutomizer L Bs,
      GGIsReflection p r₀' ∧ r₀ * r₀' ≠ r₀' * r₀ ∧ Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216 := by
    rcases hchart with ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, hfull⟩ | ⟨Φ, hF, h5, hZ⟩
    · exact qtwoDL1_base_unit ha₀ hroute hodd hK h hrange hd hfull
    · exact qtwoDL1_base_orth ha₀ hroute hodd Φ hF hZ
  obtain ⟨r₀, hr₀A, hr₀, r₀', hr₀'A, hr₀', hne, hcard⟩ := hbase
  exact ⟨r₀, ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) hr₀,
    r₀', ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀'A) hr₀', hne, hcard⟩

theorem ggQTwoDL1EdgeBaseInput_of_charts (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hmod : QTwoDL1OrthModel) (hfix : GGQTwoDL1InvFixInput)
    (hChL : GGQTwoDL1ChartLInput) : GGQTwoDL1EdgeBaseInput :=
  fun G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM =>
    qtwoDL1_edgeBase_of_chartL ha₀ hL hP hmod hfix hcfg hm hM
      (hChL G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM)

theorem ggQTwoL1InputOn_of_charts {R : ℕ → Prop} (ha₀ : GGLNoncyclicInput)
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hCh : GGQTwoDL1ChartInputOn R) :
    GGQTwoL1InputOn R :=
  ggQTwoL1Input_of_invFix ha₀ hL hP (ggQTwoDL1InvFixInputOn_of_charts qtwoDL1OrthModel_holds hCh)

theorem ggQTwoL1Input_of_charts (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hCh : GGQTwoDL1ChartInput) :
    GGQTwoL1Input :=
  ggQTwoL1InputOn_of_charts ha₀ hL hP hCh

theorem ggQTwoEdgeAmbientInput_of_charts (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hCh : GGQTwoDL1ChartInput)
    (hW : QTwoDL1OrthPair) : GGQTwoEdgeAmbientInput :=
  ggQTwoEdgeAmbientInput_of_base_local
    (ggQTwoDL1EdgeBaseInput_of_charts ha₀ hL hP qtwoDL1OrthModel_holds
      (ggQTwoDL1InvFixInput_of_charts qtwoDL1OrthModel_holds hCh)
      (fun G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM =>
        hCh G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl)))
    (ggQTwoDL1EdgeLocalInput_of_charts hCh hW)

end Inputs

end CFSG.StandardType.QTwo

end
