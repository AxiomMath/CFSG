module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmCore
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModel
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGPropFourOneTransfer

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTBJ_om_torusJNoncomm
    {p m r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 3 ≤ m)
    (hpq : p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1))
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RMinus K m b c)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RMinus K m b c)
      (Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
      L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hfix⟩ :=
    ggTBJ_om_stdModel hp hp2 hbc hm hpq ψ₀ A hA
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm K m b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm (K := K) m hbc
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qMinusForm K m b c v = 0 :=
    (OrthTorus.charSum_qMinusForm (K := K) m hbc).2 hm
  refine ggTBJ_om_torus_transport hp hp2 ψ₀ A hA Δ hE σ Θ hψσ hΘ hWeyl ?_ y hy hJ hcount
  intro f₀ J₀ hJ₀ hcount_core
  obtain ⟨a, P, hP, hswap, hmixed, hsign, hcent⟩ :=
    Δ.blockData hp2 hQ hT hE hfix f₀ ((isComponentOf_iff_open).mp hJ₀)
  exact ggTBJ_om_core hp hp2 (Δ.τΩ hE) f₀ J₀ a P hP hswap hmixed hsign hcent hcount_core

end CFSG.StandardType

end
