module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockG
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
import CFSG.RankThree.PartOne.S11d.OrthLayer
import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import Certificates.Certificate41501

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem component_cases (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))) :
    (∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
        J = (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)) ∨
      ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧
        F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
        (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
        (finrank K (fixedSpace (x : V ≃ₗ[K] V)) ≤ 4 ∨
          F = supportedFixedDerived Q (x : V ≃ₗ[K] V)) ∧
        J = F.subgroupOf (orthDerived Q) := by
  have hinj : Function.Injective (CFSG.RankThree.PartOne.piOrth Q) := by
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Subsingleton (V ≃ₗ[K] V) :=
        ⟨fun a b => LinearEquiv.ext fun v => Subsingleton.elim _ _⟩
      exact fun a b _ => Subtype.ext (Subsingleton.elim _ _)
    · exact CFSG.RankThree.PartOne.piOrth_injective hQ
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hFq, hFsup, hFn0, hFix⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.exists_fixedFactors' hx
  have hJT : CFSG.Open.IsComponentOf (J.map (CFSG.RankThree.PartOne.piOrth Q))
      (centralizerImage Q (x : V ≃ₗ[K] V)) := by
    rw [← CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x,
      ← CFSG.Assembly.isComponentOf_iff_open]
    exact isComponentOf_map_of_injective _ hinj hJ
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d.orth_component_cases hp hp2 hQ x hx
      hRep hFq hFsup hFn0 hJT with ⟨h, hh, hhX, hJh⟩ | ⟨i, hJi⟩
  · exact Or.inl ⟨h, hRep.1 hh, hhX, Subgroup.map_injective hinj hJh⟩
  · exact Or.inr ⟨F i, (hFq i).1, (hFq i).2.1, (hFq i).2.2, hFix i,
      Subgroup.map_injective hinj hJi⟩

theorem TBJOmData.blockG_orthDerived_pieces [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ a : ZMod p, a ≠ 0 ∧
      (∀ i, toAdd (f₀ i) ≠ 0 → Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h →
        toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a) ∧
      (∀ i k : Fin r, i ≠ k → toAdd (f₀ i) ≠ 0 →
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ k) ≠ 0 →
        Δ.F.U k ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ i) = toAdd (f₀ k) →
        ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
          ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f)) ∧
      (∀ i k : Fin r, toAdd (f₀ i) ≠ 0 →
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ k) ≠ 0 →
        Δ.F.U k ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ i) = a →
        toAdd (f₀ k) = -a →
        ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
          ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) (dinv i k f))) ∧
      (∀ f : Fin r → Multiplicative (ZMod p),
        (∃ m : ZMod p, ∀ i, toAdd (f₀ i) ≠ 0 →
          Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f i) = m * toAdd (f₀ i)) →
          ∀ j ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
            Δ.τΩ hA f * j = j * Δ.τΩ hA f) := by
  obtain ⟨a, ha, -, hval, hswap, hmixed, hcent⟩ := Δ.blockG_pieces hp2 hQ hA f₀ hh hX
  refine ⟨a, ha, hval, ?_, ?_, ?_⟩
  · rintro i k hik hi hUi hk hUk he
    obtain ⟨n, hn, hconj⟩ := hswap i k hik hi hUi hk hUk he
    exact ⟨⟨n, (Subgroup.mem_inf.mp hn).2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hn).1,
      fun f => Subtype.ext (hconj f)⟩
  · rintro i k hi hUi hk hUk hia hka
    obtain ⟨n, hn, hconj⟩ := hmixed i k hi hUi hk hUk hia hka
    exact ⟨⟨n, (Subgroup.mem_inf.mp hn).2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hn).1,
      fun f => Subtype.ext (hconj f)⟩
  · rintro f hf j hj
    exact Subtype.ext (hcent f hf (j : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hj))

theorem TBJOmData.blockG_orthDerived [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ (a : ZMod p) (P : Fin r → Prop), a ≠ 0 ∧
      (∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a) ∧
      (∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
        ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
          ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f)) ∧
      (∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
        ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
          ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) (dinv i k f))) ∧
      (∀ f : Fin r → Multiplicative (ZMod p),
        (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
          ∀ j ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
            Δ.τΩ hA f * j = j * Δ.τΩ hA f) := by
  obtain ⟨a, ha, hval, hswap, hmixed, hcent⟩ :=
    Δ.blockG_orthDerived_pieces hp2 hQ hA f₀ hh hX
  refine ⟨a, fun i => toAdd (f₀ i) ≠ 0 ∧ Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h,
    ha, ?_, ?_, ?_, ?_⟩
  · rintro i ⟨hi, hUi⟩
    exact hval i hi hUi
  · rintro i k hik ⟨hi, hUi⟩ ⟨hk, hUk⟩ he
    exact hswap i k hik hi hUi hk hUk he
  · rintro i k ⟨hi, hUi⟩ ⟨hk, hUk⟩ hia hka
    exact hmixed i k hi hUi hk hUk hia hka
  · rintro f ⟨m, hm⟩ j hj
    refine hcent f ⟨m, fun i hi hUi => hm i (And.intro hi hUi)⟩ j hj

end OrthTorus

end CFSG.StandardType

end
