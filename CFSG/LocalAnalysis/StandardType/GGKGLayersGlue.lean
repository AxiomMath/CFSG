module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta
public import CFSG.LocalAnalysis.StandardType.GGKGLayersClauses

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgLayers_E6_of_adj (h1 : KGAdjL1) (h2 : KGAdjL2) (h3i : KGAdjL3i) (h3ii : KGAdjL3ii)
    (h4 : KGAdjL4) (hM : KGAdjM) (hfr : KGFrameE6) :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
      GGE6KGLayers (RecipeGroup Tag.E6 K) (RecipeID Tag.E6 K) := by
  intro K _ _ n hn hK h3
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hK
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ n := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardu : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have h3u : 3 ∣ Nat.card Kˣ := by rw [hcardu]; exact h3
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' 3 h3u
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  intro L' _ _ ψ A hTB hA
  obtain ⟨g, κ, hg, hκinj, hκrange, hconj, hweyl, hsimple⟩ :=
    hfr K n hn hK h3 ζ hζ hζo L' ψ A hTB hA
  have hF : KGAutFrame A κ := ⟨hA, hκinj, hκrange, hweyl, hsimple⟩
  have hconjΘ : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹ :=
    kgThetaHom_conj g ψ
      (fun a => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)))) hconj
  refine ⟨?_, ?_⟩
  · intro c hc
    exact kgL1_clause h1 hchar ψ A ζ hζ hζo g hg κ hF hTB.1 hconjΘ c hc
  · intro a b hab
    obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
    refine ⟨(rootSpan Tag.E6 K
        (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))})).comap (kgThetaHom g),
      (rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
         kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact kgL2_clause h2 hchar ψ A ζ hζ hζo g hg κ hF hTB.1 hconjΘ a b hab
    · exact kgL3i_clause h3i hchar ψ A ζ hζ hζo g hg κ hF hTB.1 hconjΘ a b hab
    · exact kgL3ii_clause h3ii hchar ψ A ζ hζ hζo g hg κ hF hTB.1 hTB.2.1 hTB.2.2.1 hconjΘ hab
    · exact kgL4_clause h4 hchar ψ A ζ hζ hζo g hg κ hF hTB.1 hTB.2.1 hTB.2.2.1 hconjΘ hab
    · intro N _ _ π hπ hk hp
      exact kgM_clause hM hchar ψ A ζ hζ hζo g hg κ hF α β hα hβ hαβ ha hb N π hπ hk hp

end CFSG.StandardType.KGL

end
