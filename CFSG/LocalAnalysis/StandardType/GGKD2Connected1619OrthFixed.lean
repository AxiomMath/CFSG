module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed
public import CFSG.GroupTheory.Fitting.LayerContainment
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Basic
public import CFSG.GH74.Generic.S3.LyB2Dickson
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockResidual
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import Certificates.Certificate41501

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d
open CFSG.ComponentClassification.AssemblyBPredicates
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped Classical

private theorem ltromf_isSolvable_supportedFixedDerived_of_finrank_le_two
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (h2 : Module.finrank K (fixedSpace x) ≤ 2) :
    Group.IsSolvable ↥(supportedFixedDerived Q x) := by
  classical
  set R := Q.comp (fixedSpace x).subtype with hR
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  haveI : Group.IsSolvable ↥(orthDerived R) := by
    rcases Nat.lt_or_ge (Module.finrank K (fixedSpace x)) 2 with h1 | h2'
    · refine CFSG.GH74.Generic.S3.isSolvable_of_comm fun a b => ?_
      have ha1 : (a : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd a.2)
      have hb1 : (b : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd b.2)
      refine Subtype.ext ?_
      show (a : fixedSpace x ≃ₗ[K] fixedSpace x) * b = b * a
      rw [ha1, hb1]
    · have hdim : Module.finrank K (fixedSpace x) = 2 := by omega
      refine CFSG.GH74.Generic.S3.isSolvable_of_comm fun a b => ?_
      have ha : dicksonHom R hRnd
          ⟨(a : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup a.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd a.2
      have hb : dicksonHom R hRnd
          ⟨(b : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup b.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd b.2
      exact Subtype.ext (commute_of_dicksonHom_eq_one hRnd hdim
        (orthDerived_le_orthogonalGroup a.2) (orthDerived_le_orthogonalGroup b.2) ha hb)
  refine Group.isSolvable_of_isSolvable_injective
    (f := (supportedFixedDerivedEquiv hx).toMonoidHom) ?_
  exact (supportedFixedDerivedEquiv hx).injective

private theorem ltromf_supportedFixedDerived_le_sup_centralizer
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hlist : FixedLayerListed Q x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    supportedFixedDerived Q x ≤ F ⊔ Subgroup.centralizer (F : Set (V ≃ₗ[K] V)) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨n, Ff, hFf, hcomm, hsup, -⟩ := exists_fixedFactors_comm hx
  have hFcomp : CFSG.Open.IsComponentOf F (supportedFixedDerived Q x) :=
    ⟨hFle, CFSG.Open.IsSubnormal.step hFle hFn (CFSG.Open.IsSubnormal.refl _),
      (isQuasisimple_iff_open ↥F).1 ((isQuasisimple_iff_native ↥F).2 hFq)⟩
  have hFfcomp : ∀ i, CFSG.Open.IsComponentOf (Ff i) (supportedFixedDerived Q x) := by
    intro i
    have hq := (isQuasisimple_iff_open ↥(Ff i)).1
      ((isQuasisimple_iff_native ↥(Ff i)).2 (hFf i).1)
    exact ⟨(hFf i).2.1, CFSG.Open.IsSubnormal.step (hFf i).2.1 (hFf i).2.2
      (CFSG.Open.IsSubnormal.refl _), hq⟩
  have hperf : ∀ P : Subgroup (V ≃ₗ[K] V), P ≤ supportedFixedDerived Q x →
      commutator ↥P = ⊤ → P ≤ ⨆ i, Ff i := by
    intro P hP _
    rw [hsup hlist]
    exact hP
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors Ff hFfcomp
      hperf hFcomp
  rw [← hsup hlist]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [hi]
    exact le_sup_left
  · refine le_sup_of_le_right ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hi] at ha
    exact (hcomm j i hji b hb a ha).symm

theorem orthFixedBlock_action {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 8 ≤ Module.finrank F V)
    {x : ↥(orthDerived Q)} (hx : orderOf x = 3) {G : Subgroup (V ≃ₗ[F] V)}
    (hGq : CFSG.IsQuasisimple ↥G) (hGle : G ≤ supportedFixedDerived Q (x : V ≃ₗ[F] V))
    (hGn : (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))).Normal)
    (hGdim : Module.finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 4 ∨
      G = supportedFixedDerived Q (x : V ≃ₗ[F] V))
    {L : Subgroup ↥(orthDerived Q)} (hL : L = G.subgroupOf (orthDerived Q))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    {y : ↥(orthDerived Q)} (hxy : x * y = y * x) (hyL : ∀ c ∈ L, MulAut.conj y c ∈ L) :
    QuotientInner L (MulAut.conj y) := by
  classical
  have hpl : (3 : ℕ) ≠ ringChar F := by rw [ringChar.eq F 2]; norm_num
  have hxodd : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx
  have hyΩ : (y : V ≃ₗ[F] V) ∈ orthDerived Q := y.2
  have hyc : (y : V ≃ₗ[F] V) ∈ isometryCentralizer Q (x : V ≃ₗ[F] V) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hyΩ,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (show (y : V ≃ₗ[F] V) * (x : V ≃ₗ[F] V) = (x : V ≃ₗ[F] V) * (y : V ≃ₗ[F] V)
          from congrArg Subtype.val hxy.symm)⟩
  have hFq' : CFSG.IsQuasisimple ↥(G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hGle).symm hGq
  have hdim3 : 3 ≤ Module.finrank F (fixedSpace (x : V ≃ₗ[F] V)) := by
    by_contra hlt
    push Not at hlt
    have h2 : Module.finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 2 := by omega
    haveI hsol := ltromf_isSolvable_supportedFixedDerived_of_finrank_le_two hxodd h2
    exact (CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.not_isQuasisimple_of_isSolvable
      (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V)))) hFq'
  have hlist : FixedLayerListed Q (x : V ≃ₗ[F] V) := by
    refine ⟨hdim3, ?_⟩
    intro hS
    haveI hsol := isSolvable_supportedFixedDerived_of_smallFixedException hxodd hdim3 hS
    exact (CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.not_isQuasisimple_of_isSolvable
      (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V)))) hFq'
  have hX1 : (X - 1 : F[X]) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap :=
    X_sub_one_mem_of_fixed (x := (x : V ≃ₗ[F] V)) (by omega)
  set yW : V ≃ₗ[F] V :=
    (blockComponent hxodd ⟨(y : V ≃ₗ[F] V), (Subgroup.mem_inf.mp hyc).2⟩ (X - 1)).1 with hyWdef
  have hyWblock : yW ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1) :=
    hxodd.blockComponent_mem hyc hX1
  have hQW :
      (QuadraticMap.polarBilin (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    hxodd.polarBilin_fixed_nondegenerate
  obtain ⟨Rep, hRep⟩ := hxodd.exists_orbitRepresentatives
  have hδ := hxodd.dickson_restrict_eq_one (by norm_num : Odd 3) hQ hRep hyc hyΩ
  have hrestrict : restrictFixed Q (x : V ≃ₗ[F] V) ⟨yW, hyWblock⟩ =
      isometryRestrictFixed Q (x : V ≃ₗ[F] V) ⟨(y : V ≃ₗ[F] V), hyc⟩ := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simp only [coe_restrictFixed, coe_isometryRestrictFixed]
    have h := blockComponent_fixed_apply hxodd hyc (X - 1 : F[X]) hX1 (w : V)
      (by simpa [fixedSpace_eq_primaryComponent] using w.2)
    simpa [hyWdef] using h
  have hω : restrictFixed Q (x : V ≃ₗ[F] V) ⟨yW, hyWblock⟩ ∈
      omegaGroup (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) hQW := by
    have hk : (⟨restrictFixed Q (x : V ≃ₗ[F] V) ⟨yW, hyWblock⟩,
        restrictFixed_mem_orthogonalGroup _⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype))) ∈
        (dicksonHom (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) hQW).ker := by
      rw [MonoidHom.mem_ker]
      have hsub : (⟨restrictFixed Q (x : V ≃ₗ[F] V) ⟨yW, hyWblock⟩,
            restrictFixed_mem_orthogonalGroup _⟩ :
            ↥(TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype))) =
          ⟨isometryRestrictFixed Q (x : V ≃ₗ[F] V) ⟨(y : V ≃ₗ[F] V), hyc⟩,
            isometryRestrictFixed_mem_orthogonalGroup _⟩ :=
        Subtype.ext hrestrict
      rw [hsub]
      exact hδ
    rw [dicksonHom_ker] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  have hyWP : yW ∈ supportedFixedDerived Q (x : V ≃ₗ[F] V) :=
    mem_supportedFixedDerived.mpr ⟨hyWblock,
      omegaGroup_le_orthDerived_of_listed _ hQW hlist.1 hlist.2 hω⟩
  have hle_sup : supportedFixedDerived Q (x : V ≃ₗ[F] V) ≤
      G ⊔ Subgroup.centralizer (G : Set (V ≃ₗ[F] V)) :=
    ltromf_supportedFixedDerived_le_sup_centralizer hxodd hlist hGq hGle hGn
  obtain ⟨f, hfG, hfconj⟩ :=
    CFSG.GroupTheory.exists_forall_conj_eq_of_mem_sup_centralizer (C := G) (k := yW) (hle_sup hyWP)
  have hfOr : f ∈ orthDerived Q := hxodd.supportedFixedDerived_le_orthDerived (hGle hfG)
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥L) ⟨⟨f, hfOr⟩, hL.symm ▸
    Subgroup.mem_subgroupOf.mpr hfG⟩, ?_⟩
  intro c c' hcc'
  have hcG : ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ G :=
    Subgroup.mem_subgroupOf.mp (hL.le c.2)
  have hconjV : (y : V ≃ₗ[F] V) * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
        (y : V ≃ₗ[F] V)⁻¹ =
      yW * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * yW⁻¹ :=
    blockComponent_fixed_conj_eq hxodd hyc
      (supportedFixedDerived_le_supportedBlock (hGle hcG))
  have hconjV2 : yW * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * yW⁻¹ =
      f * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * f⁻¹ :=
    hfconj ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) hcG
  have hconj_eq : (MulAut.conj y c : ↥(orthDerived Q)) =
      (⟨f, hfOr⟩ : ↥(orthDerived Q)) * c * (⟨f, hfOr⟩ : ↥(orthDerived Q))⁻¹ := by
    apply Subtype.ext
    change (y : V ≃ₗ[F] V) * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * (y : V ≃ₗ[F] V)⁻¹ =
      f * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * f⁻¹
    rw [hconjV, hconjV2]
  have hLval : c' = ⟨⟨f, hfOr⟩, hL.symm ▸ Subgroup.mem_subgroupOf.mpr hfG⟩ * c *
      ⟨⟨f, hfOr⟩, hL.symm ▸ Subgroup.mem_subgroupOf.mpr hfG⟩⁻¹ := by
    apply Subtype.ext
    show (c' : ↥(orthDerived Q)) =
      (⟨f, hfOr⟩ : ↥(orthDerived Q)) * (c : ↥(orthDerived Q)) *
        (⟨f, hfOr⟩ : ↥(orthDerived Q))⁻¹
    rw [← hcc', hconj_eq]
  rw [hLval]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply]

end S2MathAs3_1619Final

end
