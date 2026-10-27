module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdKernel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4Sp
import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdClasses
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
import CFSG.LieType.Universal.Symplectic
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoClass
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.CompSLOB
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.Quasithin.Background.A3Structure314Defs
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecAVi2
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.LangRat

open CFSG CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

section Aux

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem langF4_comp_kernelB_finish {R : Type} [Group R] {F : Type} [Field F] {q : ℕ}
    (hfin : Finite F) (hF2 : Nat.card F = 2) (hq2 : q = 2)
    (g : StatedSp 3 F →* R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (StatedSp 3 F)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = q ∧
      Nonempty (R ⧸ Subgroup.center R ≃* LargeEvenProj (LargeEvenSpGroup E 3)) := by
  have hperf : Group.IsPerfect (StatedSp 3 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 3 F (Or.inr (Or.inr ⟨hF2, by norm_num⟩))
  obtain ⟨e1⟩ := CFSG.StandardType.nonempty_centerQuotEquiv_aux hperf g hg hgk
  exact ⟨F, inferInstance, hfin, hF2.trans hq2.symm,
    ⟨e1.symm.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 3 F)⟩⟩

private theorem langF4_comp_kernelB_aux
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hak : ∀ j, a j = ω ^ k j) (hk : KSF4Std.KernelB k)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = S.D.q ∧
      Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSpGroup F 3)) := by
  classical
  have h2dvd : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
  obtain ⟨f, hfpos, hqf⟩ : ∃ f, 0 < f ∧ 2 ^ f = S.D.q := by
    obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff S.D.q).1 S.hqpow.1
    have h2p : 2 = p :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp (by rw [← hpn] at h2dvd; exact h2dvd)
    exact ⟨n, hn, by rw [h2p]; exact hpn⟩
  have hq : S.D.q = 2 ^ f := hqf.symm
  by_cases hf2 : 2 ≤ f
  ·
    obtain ⟨-, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S265.SG.rationalComponent_model_of_kernelB S hT hap hf2 hq
        hω3 hω1 hak hk i
    obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hmodel
    exact ⟨K, hKfield, hKfin, hKcard.trans hq.symm, ⟨e⟩⟩
  ·
    have hf1 : f = 1 := by omega
    have hq2 : S.D.q = 2 := by rw [hq, hf1, pow_one]
    have hpL : ((3 : ℕ) : L) ≠ 0 := by
      have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
      intro h
      have h3 : ((3 : ℕ) : L) = 3 := by norm_num
      rw [h3] at h
      have : (1 : L) = 0 := by linear_combination h - h2
      exact one_ne_zero this
    have hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := KSF4Std.rootDiagUnit_pow_eq_one hap
    obtain ⟨v, -, -, c, -, hc, -, -, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
        hpL hT3 i
    have hn18 := KSF4Std.ncard_componentRoots_of_kernelB hω3 hω1 hak hk i
    have hc18 : c = [1, 2, 3] ∨ c = [2, 3, 4] :=
      KSF4Std.f4_count18 c hc (hncard.symm.trans hn18)
    have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one S hT i
        (KSF4Std.rho_image_eq_of_kernelB S hT hω3 hω1 hak hk i)
    rcases hc18 with rfl | rfl
    · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
      have hroots' : componentRoots (rootCharHom a) i =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 := by
        rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
          (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
      have hinner := KSF4Std.twistInner_of_rank3_card18 S hT i hr3 hn18
      obtain ⟨F₀, hfin, hF2, g, hg, hgk⟩ :=
        CFSG.HardMathSupport.Dickson.Bal207.FamF42.exists_sp3_cover S hq2 hT i v (Or.inl rfl)
          hroots' hinner hs1
      exact langF4_comp_kernelB_finish hfin hF2 hq2 g hg hgk
    · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
      have hroots' : componentRoots (rootCharHom a) i =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
        rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
          (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
      have hinner := KSF4Std.twistInner_of_rank3_card18 S hT i hr3 hn18
      obtain ⟨F₀, hfin, hF2, g, hg, hgk⟩ :=
        CFSG.HardMathSupport.Dickson.Bal207.FamF42.exists_sp3_cover S hq2 hT i v (Or.inr rfl)
          hroots' hinner hs1
      exact langF4_comp_kernelB_finish hfin hF2 hq2 g hg hgk

end Aux

theorem langF4_comp_kernelB
       {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ j, a j = ω ^ k j)
    (hk : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Std.KernelB k)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = S.D.q ∧
      Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSpGroup F 3)) := by
  exact langF4_comp_kernelB_aux S hT hap hω3 hω1 hak hk i

end CFSG.StandardType.LangRat

end
