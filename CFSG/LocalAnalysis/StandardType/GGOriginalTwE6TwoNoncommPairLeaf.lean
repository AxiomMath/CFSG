module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOriginalA2Pair
public noncomputable section

namespace CFSG.StandardType

open CFSG.StandardType.GGFinModel CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.GroupTheory

open CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.StandardType.TableBExc.E6Three
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag Tag.rank

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem GGOriginalTwE6TwoNoncommPairInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (X Bs : Subgroup G)
      (S : ℕ → LargeEvenLabel → Prop)
      (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
      (hmark : GGInnerDiagOnLabel S 3 Bs X) (D : TwE6CoverData hS hmark)
      (_hn1 : D.lab.n = 1)
      (_hmark1 : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X)
      (_hBs : IsElemAbelian 3 Bs) (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)),
      letI := D.fieldK
      letI := D.finiteK
      TwE6ToralCoords D.lab.n D.hEN D.ψ κ → GGNoTransvection 3 Bs →
      ∀ (r s : MulAut Bs), r ∈ ggAutomizer X Bs → GGIsReflection 3 r →
        s ∈ ggAutomizer X Bs → GGIsReflection 3 s → GGRk1ConclEx 3 Bs X r →
        r * s ≠ s * r →
        ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
          Nat.card K = (2 ^ f) ^ 2 →
          Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
          ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
            (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  intro G _ _ X Bs S hS hmark D hn1 hmark1 hBs κ
  letI := D.fieldK
  letI := D.finiteK
  letI : Fact (IsElemAbelian 3 Bs) := ⟨hBs⟩
  intro hκ hNT r s hrA hr hsA hs hR hrs
  let D1 := original_qTwo_cover_view D hn1 hmark1
  have hκ1 : TwE6ToralCoords 1 D.hEN D.ψ κ := by simpa only [hn1] using hκ
  have hfree := D1.twoKernelInG_inf_centralizer_eq_bot hR hκ1 hrA hr hsA hs
  obtain ⟨α, γ, hα, hγ, hHr, hHs, _⟩ := hκ1.exists_roots_ggHyperplane_iff hrA hr hsA hs
  obtain ⟨γ', hγ', hpair⟩ := hκ1.exists_isA2Pair_of_not_commute_of_ggHyperplane
    hNT hrA hr hsA hs hα hγ hHr hHs hrs
  have hHs' : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
      ∑ j, (γ' j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0 := by
    rcases hγ' with rfl | rfl
    · exact hHs
    · intro b
      simpa only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
        using hHs b
  exact original_qTwo_pair_forall_fields_of_same_cover D hn1 hmark1 hBs hκ
    r s α γ' hpair hHr hHs' hfree

end CFSG.StandardType
