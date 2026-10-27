module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause
import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
import CFSG.LocalAnalysis.StandardType.GGTCJLabel
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthA
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
import CFSG.HardMathSupport.Dickson.Sec6.I1431
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

section OrthTFixAux

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

private theorem orthTFix_rho_injective {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] :
    Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  have hZbot : ((scalars K V).subgroupOf (orthDerived Q)) = ⊥ :=
    CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  exact (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZbot])

private theorem orthTFix_supportedFactor_le_supportedFixedDerived
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))}
    (hJ : J ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
    supportedFactor hx J ≤ supportedFixedDerived Q x := by
  set e := (fixedBlockEquiv hx).symm with he
  have hmap : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype))).map e.toMonoidHom =
      commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  rw [supportedFactor, ← hSFD]
  exact Subgroup.map_mono (f := (supportedBlock Q x (X - 1)).subtype)
    ((Subgroup.map_mono (f := (fixedBlockEquiv hx).symm.toMonoidHom) hJ).trans (le_of_eq hmap))

private theorem orthTFix_supportedFactor_normal
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))}
    (hJ : J ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hJn : (J.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)))).Normal) :
    ((supportedFactor hx J).subgroupOf (supportedFixedDerived Q x)).Normal := by
  set e := (fixedBlockEquiv hx).symm with he
  have hmap : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype))).map e.toMonoidHom =
      commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  set LB : Subgroup ↥(supportedBlock Q x (X - 1)) := J.map e.toMonoidHom with hLBdef
  have hLBle : LB ≤ commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [hLBdef, ← hmap]
    exact Subgroup.map_mono hJ
  have hLBn : (LB.subgroupOf (commutator ↥(supportedBlock Q x (X - 1)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLBle]
    rintro _ k ⟨l, hl, rfl⟩ hk
    rw [← hmap] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have h1 := (Subgroup.normal_subgroupOf_iff hJ).mp hJn l c hl hc
    exact ⟨c * l * c⁻¹, h1, by simp⟩
  have hFdef : supportedFactor hx J = LB.map (supportedBlock Q x (X - 1)).subtype := by
    rw [supportedFactor, hLBdef]
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  rw [hFdef, ← hSFD]
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hLBle)]
  rintro _ k ⟨l, hl, rfl⟩ hk
  obtain ⟨c, hc, rfl⟩ := hk
  have h1 := (Subgroup.normal_subgroupOf_iff hLBle).mp hLBn l c hl hc
  exact ⟨c * l * c⁻¹, h1, by simp⟩

theorem orthTFix_ggHasLabel_of_orthRealized {G₀ : Type} [Group G₀] {J₀ : Subgroup G₀}
    (hq : CFSG.IsQuasisimple ↥J₀) {lab : LargeEvenLabel}
    (h : CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized lab J₀) :
    GGHasLabel lab (↥J₀ ⧸ Subgroup.center ↥J₀) := by
  refine CFSG.StandardType.TCJ.tcjLabel_rawDatum_canonical_to_legacy ?_
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ h
  rintro R _ I F ⟨hs, hna, Θ₁, hΘs, hΘk, -⟩
  have hZR : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b) a)
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.nonempty_centerQuotientEquiv_of_surjective hq.1 Θ₁ hΘs hΘk
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZR).trans QuotientGroup.quotientBot)⟩

private theorem orthTFix_quot_iso {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {F : Subgroup (V ≃ₗ[K] V)}
    (hFle : F ≤ supportedFixedDerived Q x) {L : Subgroup (ProjOrthDerived Q)}
    (hL : L = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥F ⧸ Subgroup.center ↥F) := by
  have hρinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) :=
    orthTFix_rho_injective (Q := Q) hQ
  have hFΩ : F ≤ orthDerived Q :=
    hFle.trans (OddOrderIsometry.supportedFixedDerived_le_orthDerived hx)
  let eFL : ↥F ≃* ↥L :=
    (Subgroup.subgroupOfEquivOfLe hFΩ).symm.trans
      ((Subgroup.equivMapOfInjective (F.subgroupOf (orthDerived Q))
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) hρinj).trans
        (MulEquiv.subgroupCongr hL).symm)
  exact ⟨QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥F) eFL.symm
    (Subgroup.map_center_eq eFL.symm)⟩

private theorem orthTFix_orthRealized_large_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n s : ℕ} (hs4 : 4 ≤ s)
    (hK : Nat.card K = 2 ^ n)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus s K))
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.D, s, n⟩ (supportedFixedDerived Q x) :=
  CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_fixed_plus hx hs4 hK ψ hq

private theorem orthTFix_orthRealized_large_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n s : ℕ} (hs4 : 4 ≤ s)
    (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (CFSG.LieType.Universal.Spin.quadMinus s K b c))
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.twD, s, n⟩ (supportedFixedDerived Q x) :=
  CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_fixed_minus hx hs4 hK hirr ψ hq

private theorem orthTFix_orthRealized_six_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hdim : Module.finrank K (fixedSpace x) = 6)
    (hT : ∃ U : Submodule K (fixedSpace x), Module.finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0)
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.A, 3, n⟩ (supportedFixedDerived Q x) := by
  obtain ⟨κ⟩ := CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_klein_commutator_six
    (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate hdim hT
  refine CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_of_inn ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  dsimp only
  exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_linear_inn_data hq (d := 4) (j := 2) rfl
    (by norm_num) (Or.inl (by norm_num)) hK
    ((supportedFixedDerivedEquiv hx).trans
      ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator
        (Q.comp (fixedSpace x).subtype)).symm.trans κ))

private theorem orthTFix_orthRealized_six_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hdim : Module.finrank K (fixedSpace x) = 6)
    (hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 3 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0)
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.twD, 3, n⟩ (supportedFixedDerived Q x) := by
  obtain ⟨E, hEfield, hEfin, hEcard, ⟨eΩ⟩⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six
      (f := n) hK hx.polarBilin_fixed_nondegenerate hdim hts
  haveI : CharP E 2 :=
    CFSG.RankThree.PartOne.charP_two_of_card_eq_pow (K := E) (f := 2 * n) (by
      rw [hEcard, ← pow_mul, mul_comm n 2])
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    norm_num at h2
  refine CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_of_inn ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  dsimp only
  simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
  exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_unitary4_inn_data hq (f := n) hn1 hEcard
    ((supportedFixedDerivedEquiv hx).trans eΩ)

private theorem orthTFix_orthRealized_four_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hdim : Module.finrank K (fixedSpace x) = 4)
    (hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0)
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.A, 1, 2 * n⟩
      (supportedFixedDerived Q x) := by
  obtain ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨eΩ⟩⟩ :=
    CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2
      (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate hdim hts
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    norm_num at h2
  have hEne2 : Nat.card E ≠ 2 := by
    rw [hEcard, hK]
    have h4 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    intro h
    nlinarith [h4]
  refine CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_of_inn ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  dsimp only
  exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_linear_inn_data hq (d := 2) (j := 1) rfl
    le_rfl (Or.inr hEne2) (N := 2 ^ (2 * n)) (by rw [hEcard, hK, ← pow_mul, mul_comm n 2])
    ((supportedFixedDerivedEquiv hx).trans
      (eΩ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E)))

private theorem orthTFix_orthRealized_four_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hdim : Module.finrank K (fixedSpace x) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace x), Module.finrank K S = 2 ∧
      ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.A, 1, n⟩ F := by
  set R := Q.comp (fixedSpace x).subtype with hRdef
  have hR : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hK3 : Nat.card K ≠ 3 := fun h3 => two_pow_ne_three n (by rw [← hK]; exact h3)
  have hK2 : Nat.card K ≠ 2 := by
    intro hK2
    haveI hFnt : Nontrivial ↥F := CFSG.LocalCores.isQuasisimple_nontrivial hFq
    have hsolvO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      CFSG.LocalAnalysis.GLTheoremA.T123CB.isSolvable_orthogonalGroup_of_card_two_of_plus
        R hR hK2 hdim ⟨hsplit.choose, by omega, hsplit.choose_spec.2⟩
    have hsolvΩ : Group.IsSolvable ↥(orthDerived R) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup R))
        (Subgroup.inclusion_injective _)
    have hsolvF : Group.IsSolvable ↥F :=
      Group.isSolvable_of_isSolvable_injective
        (f := (supportedFixedDerivedEquiv hx).toMonoidHom.comp (Subgroup.inclusion hFle))
        ((supportedFixedDerivedEquiv hx).injective.comp (Subgroup.inclusion_injective hFle))
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isSolvable_of_isQuasisimple
      hFq hsolvF
  obtain ⟨ψ, e, -, he, hsup, hLq', hRq', hLn', hRn', -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 R hR hdim hsplit
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hFB : F ≤ supportedBlock Q x (X - 1) :=
    hFle.trans supportedFixedDerived_le_supportedBlock
  have hCB : ∀ g : ↥(supportedBlock Q x (X - 1)), (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      g ∈ commutator ↥(supportedBlock Q x (X - 1)) := by
    intro g hg
    rw [← hSFD] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    rwa [show g = g' from Subtype.ext hgg.symm]
  have hmapC : (commutator ↥(supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := (fixedBlockEquiv hx).toMonoidHom)).2
        (fixedBlockEquiv hx).surjective]
  set L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    (F.subgroupOf (supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom with hL
  have hLle : L ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmapC]
    exact ⟨g, hCB g (hFle hg), rfl⟩
  have hLn : (L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle]
    rintro _ k ⟨g, hg, rfl⟩ hk
    rw [← hmapC] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    refine ⟨c * g * c⁻¹, ?_, by simp⟩
    have hcS : (c : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := hSFD ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hFle).1 hFn _ _ hg hcS
  set eFL : ↥F ≃* ↥L := (Subgroup.subgroupOfEquivOfLe hFB).symm.trans
    ((F.subgroupOf (supportedBlock Q x (X - 1))).equivMapOfInjective
      (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective) with heFL
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.LocalCores.isQuasisimple_of_mulEquiv eFL hFq
  haveI : Finite (fixedSpace x) := Module.finite_of_finite K
  haveI : Finite ((fixedSpace x) ≃ₗ[K] (fixedSpace x)) :=
    Finite.of_injective
      (fun g : (fixedSpace x) ≃ₗ[K] (fixedSpace x) => (g : fixedSpace x → fixedSpace x))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  set Lf := (CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).map
    e.symm.toMonoidHom with hLf
  set Rf := (CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor K).map
    e.symm.toMonoidHom with hRf
  have hLfC : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hsup]; exact le_sup_left
  have hRfC : Rf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hsup]; exact le_sup_right
  have hFc : ∀ i, CFSG.Open.IsComponentOf (![Lf, Rf] i)
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    intro i
    fin_cases i
    · exact ⟨hLfC, CFSG.Open.IsSubnormal.step hLfC hLn' (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq'⟩
    · exact ⟨hRfC, CFSG.Open.IsSubnormal.step hRfC hRn' (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hRq'⟩
  have hperf : ∀ P : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R),
      P ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) → commutator ↥P = ⊤ →
      P ≤ ⨆ i, ![Lf, Rf] i := by
    intro P hP _
    refine hP.trans (hsup.le.trans (sup_le ?_ ?_))
    · exact le_iSup (fun i => ![Lf, Rf] i) 0
    · exact le_iSup (fun i => ![Lf, Rf] i) 1
  have hLc : CFSG.Open.IsComponentOf L
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
    ⟨hLle, CFSG.Open.IsSubnormal.step hLle hLn (CFSG.Open.IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq⟩
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors _ hFc hperf hLc
  have key : ∀ Fac : Subgroup ↥(DeterminantIsometries K),
      (Fac = CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K ∨
        Fac = CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor K) →
      L = Fac.map e.symm.toMonoidHom →
      CFSG.LocalAnalysis.GLTheoremA.K155XOr.OrthRealized ⟨.A, 1, n⟩ F := by
    intro Fac hFac hLFac
    set eLFac : ↥L ≃* ↥Fac := (MulEquiv.subgroupCongr hLFac).trans
      (Fac.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm with heLFac
    set eF : ↥F ≃* ↥(CFSG.Open.StatedSL 2 K) := eFL.trans (eLFac.trans
      ((CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_nonempty_mulEquiv_determinantFactor
          Fac hFac).some.symm.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))) with heF
    refine CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthRealized_of_inn ?_
    unfold CFSG.Assembly.LargeEvenRawDatum
    dsimp only
    exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_linear_inn_data hFq (d := 2) (j := 1) rfl
      le_rfl (Or.inr hK2) hK eF
  fin_cases i
  · exact key _ (Or.inl rfl) hi
  · exact key _ (Or.inr rfl) hi

end OrthTFixAux

theorem orthT_fixedLabel {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    {L : Subgroup (ProjOrthDerived Q)}
    (hL : L = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :
    ∃ s : ℕ, Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 2 * s ∧
      ((4 ≤ s ∧ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          GGHasLabel ⟨.D, s, n⟩ (L ⧸ Subgroup.center L)) ∨
        (4 ≤ s ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          GGHasLabel ⟨.twD, s, n⟩ (L ⧸ Subgroup.center L)) ∨
        (s = 3 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          GGHasLabel ⟨.A, 3, n⟩ (L ⧸ Subgroup.center L)) ∨
        (s = 3 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          GGHasLabel ⟨.twA, 3, n⟩ (L ⧸ Subgroup.center L)) ∨
        (s = 2 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          GGHasLabel ⟨.A, 1, 2 * n⟩ (L ⧸ Subgroup.center L)) ∨
        (s = 2 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          2 ≤ n ∧ GGHasLabel ⟨.A, 1, n⟩ (L ⧸ Subgroup.center L))) := by
  classical
  haveI hFnt : Nontrivial ↥F := CFSG.LocalCores.isQuasisimple_nontrivial hFq
  haveI hVnt : Nontrivial V := by
    obtain ⟨f, hf⟩ := exists_ne (1 : ↥F)
    have hfL : (f : V ≃ₗ[K] V) ≠ 1 := fun h => hf (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v : V, (f : V ≃ₗ[K] V) v ≠ v := by
      by_contra h
      push Not at h
      exact hfL (LinearEquiv.ext h)
    exact ⟨0, v, fun h0 => hv (by rw [← h0, map_zero])⟩
  let R := Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.even_finrank_fixed hx
  have hsolvF : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) → False := by
    intro hO
    have hΩ : Group.IsSolvable ↥(orthDerived R) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup R))
        (Subgroup.inclusion_injective _)
    have hF : Group.IsSolvable ↥F :=
      Group.isSolvable_of_isSolvable_injective
        (f := (supportedFixedDerivedEquiv hx).toMonoidHom.comp (Subgroup.inclusion hFle))
        ((supportedFixedDerivedEquiv hx).injective.comp (Subgroup.inclusion_injective hFle))
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isSolvable_of_isQuasisimple hFq hF
  refine ⟨s, by omega, ?_⟩
  by_cases hsle : s ≤ 1
  · exfalso
    exact hsolvF
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_isSolvable_orthogonalGroup_of_finrank_le_two
        hRnd (by omega))
  · have hs2 : 2 ≤ s := by omega
    by_cases hsplit4 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType R
    · obtain ⟨hdim4, hplus⟩ := hsplit4
      obtain ⟨S, hS2, hS0⟩ := hplus
      have hs_eq : s = 2 := by omega
      have hK2 : Nat.card K ≠ 2 := by
        intro hK2
        exact hsolvF
          (CFSG.LocalAnalysis.GLTheoremA.T123CB.isSolvable_orthogonalGroup_of_card_two_of_plus
            R hRnd hK2 (by omega) ⟨S, hS2, hS0⟩)
      have hn2 : 2 ≤ n := by
        have hn1 : 1 ≤ n := by
          by_contra hn
          have hn0 : n = 0 := by omega
          subst hn0
          have h2 : 1 < Nat.card K := Finite.one_lt_card
          rw [hK] at h2
          norm_num at h2
        by_contra hn
        have hn1' : n = 1 := by omega
        exact hK2 (by rw [hK, hn1']; norm_num)
      have hraw := orthTFix_orthRealized_four_plus hx hK (by omega) ⟨S, by omega, hS0⟩ hFq hFle hFn
      have hlab := orthTFix_ggHasLabel_of_orthRealized hFq hraw
      obtain ⟨e⟩ := orthTFix_quot_iso hQ hx hFle hL
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hs_eq, ⟨S, hS2, hS0⟩, hn2, ggHasLabel_of_mulEquiv e.symm hlab⟩))))
    · have hns : ¬ (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
          ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), Module.finrank K S = 2 ∧
            ∀ y ∈ S, R y = 0) := by
        rintro ⟨hd4, S, hS2, hS0⟩
        exact hsplit4 ⟨hd4, ⟨S, by omega, hS0⟩⟩
      have hnexc : ¬ SmallFixedException R := by
        rintro (⟨h3, hK3⟩ | ⟨⟨hd4, S, hS2, hS0⟩, hK2 | hK3⟩)
        · omega
        · exact hsplit4 ⟨hd4, ⟨S, by omega, hS0⟩⟩
        · exact two_pow_ne_three n (by rw [← hK]; exact hK3)
      have h3 : 3 ≤ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) := by omega
      have hC : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
        CFSG.RankThree.PartOne.KCOrthogonal.orthogonal_regular_space_derived_quasisimple
          R hRnd h3 hnexc hns
      have hFeq : F = supportedFixedDerived Q (x : V ≃ₗ[K] V) :=
        CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_eq_supportedFixedDerived hx hFq hFle hFn hC
      have hqW : CFSG.IsQuasisimple ↥(supportedFixedDerived Q (x : V ≃ₗ[K] V)) := hFeq ▸ hFq
      have htrans : ∀ {lab : LargeEvenLabel},
          GGHasLabel lab (↥(supportedFixedDerived Q (x : V ≃ₗ[K] V)) ⧸
            Subgroup.center ↥(supportedFixedDerived Q (x : V ≃ₗ[K] V))) →
          GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
        intro lab h
        obtain ⟨e1⟩ := orthTFix_quot_iso hQ hx hFle hL
        have e2 : ↥F ⧸ Subgroup.center ↥F ≃*
            ↥(supportedFixedDerived Q (x : V ≃ₗ[K] V)) ⧸
              Subgroup.center ↥(supportedFixedDerived Q (x : V ≃ₗ[K] V)) :=
          QuotientGroup.congr (Subgroup.center ↥F)
            (Subgroup.center ↥(supportedFixedDerived Q (x : V ≃ₗ[K] V)))
            (MulEquiv.subgroupCongr hFeq) (Subgroup.map_center_eq _)
        exact ggHasLabel_of_mulEquiv e1.symm (ggHasLabel_of_mulEquiv e2.symm h)
      by_cases hs4 : 4 ≤ s
      · by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R
        · refine Or.inl ⟨hs4, hplus, ?_⟩
          obtain ⟨ψ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
            (n := s) hRnd (by omega) hplus
          exact htrans (orthTFix_ggHasLabel_of_orthRealized hqW
            (orthTFix_orthRealized_large_plus hx hs4 hK ψ hqW))
        · refine Or.inr (Or.inl ⟨hs4, hplus, ?_⟩)
          rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
              (n := s) R hRnd (by omega) (by omega) with hψ | ⟨b, c, hirr, hψ⟩
          · obtain ⟨ψ⟩ := hψ
            exact absurd (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv ψ.symm
              (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K s)) hplus
          · obtain ⟨ψ⟩ := hψ
            exact htrans (orthTFix_ggHasLabel_of_orthRealized hqW
              (orthTFix_orthRealized_large_minus hx hs4 hK hirr ψ hqW))
      · by_cases hs3 : s = 3
        · have hdim6 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 6 := by omega
          by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R
          · have hT : ∃ U : Submodule K (fixedSpace (x : V ≃ₗ[K] V)),
                Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0 := by
              obtain ⟨S, hS, hS0⟩ := hplus
              exact ⟨S, by omega, hS0⟩
            refine Or.inr (Or.inr (Or.inl ⟨hs3, hplus, ?_⟩))
            exact htrans (orthTFix_ggHasLabel_of_orthRealized hqW
              (orthTFix_orthRealized_six_plus hx hK hdim6 hT hqW))
          · have hts : ∀ U : Submodule K (fixedSpace (x : V ≃ₗ[K] V)),
                Module.finrank K U = 3 → ∃ u ∈ U, R u ≠ 0 := by
              intro U hU
              by_contra hcon
              push Not at hcon
              exact hplus ⟨U, by omega, hcon⟩
            refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hs3, hplus, ?_⟩)))
            exact htrans (orthTFix_ggHasLabel_of_orthRealized hqW
              (orthTFix_orthRealized_six_minus hx hK hdim6 hts hqW))
        · have hs_eq : s = 2 := by omega
          have hdim4 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 := by omega
          have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R := by
            intro hp
            exact hsplit4 ⟨hdim4, hp⟩
          have hts : ∀ U : Submodule K (fixedSpace (x : V ≃ₗ[K] V)),
              Module.finrank K U = 2 → ∃ u ∈ U, R u ≠ 0 := by
            intro U hU
            by_contra hcon
            push Not at hcon
            exact hsplit4 ⟨hdim4, ⟨U, by omega, hcon⟩⟩
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs_eq, hminus, ?_⟩))))
          exact htrans (orthTFix_ggHasLabel_of_orthRealized hqW
            (orthTFix_orthRealized_four_minus hx hK hdim4 hts hqW))

theorem orthT_fixedExists {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    (h4 : 4 ≤ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)))
    (hsmall : ¬ (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧ n = 1)) :
    ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧ F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
      (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
      (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 →
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) →
        ∃ F' : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F' ∧
          F' ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
          (F'.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
          (F'.subgroupOf (orthDerived Q)).map
              (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ≠
            (F.subgroupOf (orthDerived Q)).map
              (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  classical
  set W := fixedSpace (x : V ≃ₗ[K] V) with hW
  set QW := Q.comp W.subtype with hQW
  have hQWnd : (QuadraticMap.polarBilin QW).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  haveI hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by
    have := Submodule.finrank_le W
    omega)
  by_cases hsplit4 : Module.finrank K W = 4 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType QW
  · obtain ⟨hd4, hplus⟩ := hsplit4
    obtain ⟨S, hS2, hS0⟩ := hplus
    have hn1 : n ≠ 1 := fun hn => hsmall ⟨hd4, ⟨S, by omega, hS0⟩, hn⟩
    have hK2 : Nat.card K ≠ 2 := by
      intro h2
      have h2' : 2 ^ n = 2 ^ 1 := by rw [← hK, h2]; norm_num
      exact hn1 (Nat.pow_right_injective (le_refl 2) h2')
    have hK3 : Nat.card K ≠ 3 := fun h3 => two_pow_ne_three n (by rw [← hK]; exact h3)
    obtain ⟨ψ, e, hψ, he, hsup, hqL, hqR, hnL, hnR, hcomm, hperf, hsq⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 QW hQWnd hd4
        ⟨S, by omega, hS0⟩
    let L : Fin 2 → Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW) :=
      ![ (CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).map
          e.symm.toMonoidHom,
        (CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor K).map
          e.symm.toMonoidHom ]
    have hLq : ∀ i, CFSG.IsQuasisimple ↥(L i) := by
      intro i; fin_cases i
      · exact hqL
      · exact hqR
    have hLle : ∀ i, L i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup QW) := by
      intro i; fin_cases i
      · show (CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).map
          e.symm.toMonoidHom ≤ _
        rw [hsup]; exact le_sup_left
      · show (CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor K).map
          e.symm.toMonoidHom ≤ _
        rw [hsup]; exact le_sup_right
    have hLn : ∀ i, ((L i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup QW))).Normal := by
      intro i; fin_cases i
      · show (((CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).map
          e.symm.toMonoidHom).subgroupOf _).Normal
        exact hnL
      · show (((CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor K).map
          e.symm.toMonoidHom).subgroupOf _).Normal
        exact hnR
    have hLcomm : ∀ i j, i ≠ j → ∀ u ∈ L i, ∀ v ∈ L j, u * v = v * u := by
      intro i j hij u hu v hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm u hu v hv
      · exact (hcomm v hv u hu).symm
      · exact absurd rfl hij
    have hsupL : (⨆ i : Fin 2, L i) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup QW) := by
      have h01 : (⨆ i : Fin 2, L i) = L 0 ⊔ L 1 := by
        refine le_antisymm (iSup_le ?_) (sup_le (le_iSup L 0) (le_iSup L 1))
        intro i
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      rw [h01]
      exact hsup.symm
    have hfam := hx.fixedFactorImage_family L hsupL (fun i => ⟨hLq i, hLle i, hLn i⟩) hLcomm
    obtain ⟨-, hC, hcommC⟩ := hfam
    let ρ := QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
    have hρinj : Function.Injective ρ := orthTFix_rho_injective (Q := Q) hQ
    refine ⟨supportedFactor hx (L 0), ?_, ?_, ?_, ?_⟩
    · refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_ (hC 0).2.1
      exact (Subgroup.equivMapOfInjective _ ρ hρinj).symm.trans
        ((supportedFactor hx (L 0)).subgroupOfEquivOfLe (hC 0).1)
    · exact orthTFix_supportedFactor_le_supportedFixedDerived hx (hLle 0)
    · exact orthTFix_supportedFactor_normal hx (hLle 0) (hLn 0)
    · intro hd4' hplus'
      refine ⟨supportedFactor hx (L 1), ?_, ?_, ?_, ?_⟩
      · refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_ (hC 1).2.1
        exact (Subgroup.equivMapOfInjective _ ρ hρinj).symm.trans
          ((supportedFactor hx (L 1)).subgroupOfEquivOfLe (hC 1).1)
      · exact orthTFix_supportedFactor_le_supportedFixedDerived hx (hLle 1)
      · exact orthTFix_supportedFactor_normal hx (hLle 1) (hLn 1)
      · intro hEq
        have hJ0q : CFSG.IsQuasisimple ↥(fixedFactorImage hx (L 0)) := (hC 0).2.1
        have hperf0 : ⁅fixedFactorImage hx (L 0), fixedFactorImage hx (L 0)⁆ =
            fixedFactorImage hx (L 0) := (Subgroup.isPerfect_iff).1 hJ0q.1
        have hdisj : ⁅fixedFactorImage hx (L 0), fixedFactorImage hx (L 1)⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (hcommC 0 1 (by decide) z hz y hy).symm
        have hEq' : fixedFactorImage hx (L 0) = fixedFactorImage hx (L 1) := hEq.symm
        have hbot : fixedFactorImage hx (L 0) = ⊥ := by
          rw [← hEq'] at hdisj
          rw [← hperf0]
          exact hdisj
        exact ne_bot_of_isQuasisimple hJ0q hbot
  · have hns : ¬ (Module.finrank K W = 4 ∧
        ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ s ∈ S, QW s = 0) := by
      rintro ⟨hd4, S, hS2, hS0⟩
      exact hsplit4 ⟨hd4, ⟨S, by omega, hS0⟩⟩
    have hnexc : ¬ SmallFixedException QW := by
      rintro (⟨h3, hK3⟩ | ⟨⟨hd4, S, hS2, hS0⟩, hK2 | hK3⟩)
      · omega
      · have hn1 : n = 1 := by
          have h2 : 2 ^ n = 2 ^ 1 := by rw [← hK]; rw [hK2]; norm_num
          exact Nat.pow_right_injective (le_refl 2) h2
        exact hsmall ⟨hd4, ⟨S, by omega, hS0⟩, hn1⟩
      · exact two_pow_ne_three n (by rw [← hK]; exact hK3)
    have h3 : 3 ≤ Module.finrank K W := by omega
    have hqOW : CFSG.IsQuasisimple ↥(orthDerived QW) := by
      refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_
        (orthogonal_regular_space_derived_quasisimple QW hQWnd h3 hnexc hns)
      exact (Subgroup.equivMapOfInjective (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
        (TauCeti.QuadraticMap.orthogonalGroup QW).subtype
        (TauCeti.QuadraticMap.orthogonalGroup QW).subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))
    refine ⟨supportedFixedDerived Q (x : V ≃ₗ[K] V), ?_, le_rfl, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm
        (hW ▸ hQW ▸ hqOW)
    · rw [Subgroup.subgroupOf_self]; infer_instance
    · intro hd hplus
      exact absurd ⟨hd, hplus⟩ hsplit4

private theorem orthTFix_fixed_special_disjoint {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) :
    Disjoint (supportedBlock Q x (X - 1)) (specialBlock Q x h) := by
  have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne1 (by
    rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  have hfix₁ : ∀ v ∈ othersSpace x.toLinearMap (X - 1), g v = v :=
    (mem_supportedBlock.mp hg).2
  have hfixh : ∀ v ∈ othersSpace x.toLinearMap h, g v = v :=
    (mem_supportedBlock.mp (specialBlock_le_supportedBlock h hg')).2
  apply LinearEquiv.toLinearMap_injective
  refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
  show g v = v
  by_cases hah : a = h ∨ a = reciprocalPolynomial h
  · refine hfix₁ v ?_
    rcases hah with h1 | h1
    · exact Submodule.mem_iSup_of_mem h (Submodule.mem_iSup_of_mem
        ⟨h1 ▸ ha, hne1, by rw [reciprocalPolynomial_X_sub_one]; exact hne1⟩ (h1 ▸ hv))
    · exact Submodule.mem_iSup_of_mem (reciprocalPolynomial h) (Submodule.mem_iSup_of_mem
        ⟨h1 ▸ ha, hne1', by rw [reciprocalPolynomial_X_sub_one]; exact hne1'⟩ (h1 ▸ hv))
  · refine hfixh v (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem
      ⟨ha, (fun e => hah (Or.inl e)), (fun e => hah (Or.inr e))⟩ hv))

theorem orthT_fixed_ne_block {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V)) :
    (F.subgroupOf (orthDerived Q)).map (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ≠
      componentImage Q (x : V ≃ₗ[K] V) h := by
  haveI hnt : Nontrivial ↥F := CFSG.LocalCores.isQuasisimple_nontrivial hFq
  haveI hVnt : Nontrivial V := by
    obtain ⟨f, hf⟩ := exists_ne (1 : ↥F)
    have hfL : (f : V ≃ₗ[K] V) ≠ 1 := fun h => hf (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v : V, (f : V ≃ₗ[K] V) v ≠ v := by
      by_contra h
      push Not at h
      exact hfL (LinearEquiv.ext h)
    exact ⟨0, v, fun h0 => hv (by rw [← h0, map_zero])⟩
  have hZbot : ((scalars K V).subgroupOf (orthDerived Q)) = ⊥ :=
    CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hρinj : Function.Injective ρ :=
    (MonoidHom.ker_eq_bot_iff ρ).1 (by rw [QuotientGroup.ker_mk', hZbot])
  intro hEq
  obtain ⟨f, hf⟩ := exists_ne (1 : ↥F)
  have hf1 : (f : V ≃ₗ[K] V) ≠ 1 := fun h => hf (Subtype.ext h)
  have hford : (f : V ≃ₗ[K] V) ∈ orthDerived Q :=
    OddOrderIsometry.supportedFixedDerived_le_orthDerived hx (hFle f.2)
  let fΩ : ↥(orthDerived Q) := ⟨(f : V ≃ₗ[K] V), hford⟩
  have hfΩ : fΩ ∈ F.subgroupOf (orthDerived Q) := Subgroup.mem_subgroupOf.mpr f.2
  have hmem : ρ fΩ ∈ ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map ρ := by
    have h1 : ρ fΩ ∈ componentImage Q (x : V ≃ₗ[K] V) h := by
      rw [← hEq]
      exact Subgroup.mem_map_of_mem ρ hfΩ
    simpa only [componentImage] using h1
  obtain ⟨s, hs, hsf⟩ := Subgroup.mem_map.mp hmem
  have hsval : (s : V ≃ₗ[K] V) = (f : V ≃ₗ[K] V) := congrArg Subtype.val (hρinj hsf)
  have hfspec : (f : V ≃ₗ[K] V) ∈ specialBlock Q (x : V ≃ₗ[K] V) h :=
    hsval ▸ Subgroup.mem_subgroupOf.mp hs
  have hffix : (f : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) :=
    supportedFixedDerived_le_supportedBlock (hFle f.2)
  exact hf1 ((Subgroup.disjoint_def.mp (orthTFix_fixed_special_disjoint hx hh hne1))
    hffix hfspec)

end CFSG.StandardType.TablePThreeKG

end
