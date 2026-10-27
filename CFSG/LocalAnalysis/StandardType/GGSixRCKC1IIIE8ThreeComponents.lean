module
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Transport
public import CFSG.LocalAnalysis.StandardType.GGE8TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Components
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section
namespace CFSG.StandardType.RCKC1
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType

theorem e8_three_compConfig_has_component_label
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 3 G₀ A B₁ D J L K e) :
    ∃ labK : LargeEvenLabel,
      labK ∈ [⟨.twE6, 0, 1⟩, ⟨.twA, 8, 1⟩, ⟨.E7, 0, 1⟩, ⟨.twD, 7, 1⟩] ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  have hdiag := RCKRP.rckRPConfigInnerDiag_holds X .E8 n 1 ψ 3 G₀ A B₁ D J L K e hcfg
  obtain ⟨hGG, -, -, -, hA, hBA, hDB, -, hAN, -, -, -, -, -, -, hfaith,
    -, -, -, -, -, -, -, -, -, heD, hene, hKcomp, -, -⟩ := hcfg
  have hn : n = 0 := hGG.1.1.2.2
  subst n
  have heA : e ∈ A := hBA (hDB heD)
  have heN : e ∈ Subgroup.normalizer (G₀ : Set X) := hAN heA
  let α : MulAut G₀ := G₀.normalizerMonoidHom ⟨e, heN⟩
  have hα3 : α ^ 3 = 1 := by
    have he3 : (⟨e, heN⟩ : Subgroup.normalizer (G₀ : Set X)) ^ 3 = 1 :=
      Subtype.ext (hA.2 e heA)
    change (G₀.normalizerMonoidHom ⟨e, heN⟩) ^ 3 = 1
    rw [← map_pow, he3, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have heC : e ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun β : MulAut G₀ => ((β ⟨x, hx⟩ : G₀) : X)) h1
      change e * x * e⁻¹ = x at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have heInf : e ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨heA, heC⟩
    rw [hfaith, Subgroup.mem_bot] at heInf
    exact hene heInf
  obtain ⟨g, hg0, hecg0⟩ := ggPsiDiagInner_E8 X 0 1 ψ G₀ hGG e heN (hdiag e heA)
  let g₀ : G₀ := ⟨g⁻¹, G₀.inv_mem hg0⟩
  have hαinner : α = MulAut.conj g₀ := by
    ext x
    change e * (x : X) * e⁻¹ = g⁻¹ * (x : X) * (g⁻¹)⁻¹
    rw [inv_inv]
    have hz : g⁻¹ * (x : X) * g ∈ G₀ :=
      G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg0) x.2) hg0
    have hc := Subgroup.mem_centralizer_iff.mp hecg0 _ hz
    calc
      e * (x : X) * e⁻¹ = (e * g) * (g⁻¹ * (x : X) * g) * (e * g)⁻¹ := by group
      _ = g⁻¹ * (x : X) * g := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hc.symm
  obtain ⟨hperf, lab, hΛ, hraw⟩ :=
    largeEvenMarking_of_lieModel_centerQuot hGG.2.2.1 hGG.2.2.2
  have hfirst := largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -, hdeg⟩ := hfirst
  have hlab : lab = ⟨.E8, 0, 1⟩ := by
    rcases lab with ⟨tag, rank, exponent⟩
    cases tag <;> simp_all [markTag, markDeg, LargeEvenInLambda2]
    all_goals split_ifs at htag
  subst lab
  have hrawI := ggRawInnFieldOn_excInn 3 (by decide) (by decide) ⟨.E8, 0, 1⟩ hΛ (by simp [GGRecipeExcInnLabel]) _ hraw
  have hmarked : LargeEvenRawDatum (⟨.E8, 0, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      ∃ θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y => y = α x) β := by
    apply largeEvenRawDatum_mono _ hrawI
    rintro R _ I F ⟨⟨hsimple, hnab, θ, -, -, -, -⟩, hI⟩
    let β : MulAut R := MulAut.conj (θ (QuotientGroup.mk g₀))
    refine ⟨θ, β, (hI hsimple hnab).2.2.1 _, ?_⟩
    intro x y hy
    subst y
    simp [β, hαinner]
  have hKle : K ≤ G₀ := hKcomp.1.trans inf_le_left
  obtain ⟨labK, hmem, hlabel⟩ := GGCompList.of_rawMarking E8TwoThree.ggE8TwoThreeComp_holds
    hperf hα3 hα1 hmarked (isComponentOf_subgroupOf_ggAutFixed heN hKle hKcomp)
  exact ⟨labK, hmem,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle) hlabel⟩

end CFSG.StandardType.RCKC1
