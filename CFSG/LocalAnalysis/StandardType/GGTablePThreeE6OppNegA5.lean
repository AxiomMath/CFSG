module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Kind
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompKac
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate10050
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8117
public import Certificates.Certificate9
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open CFSG.StandardType.TableCRes

set_option synthInstance.maxSize 1024 in
private theorem kc_a5 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3 →
    ∀ x ∈ zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ),
      szF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ)) x = 30 →
      cmpF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ)) x = sA5a ∨
      cmpF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ)) x = sA5b ∨
      cmpF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ)) x = sA5c := by
  decide +kernel

private def a5VecA : Fin Tag.E6.rank → ℤ := ![5, 0, 4, 3, 2, 1]

private def a5VecB : Fin Tag.E6.rank → ℤ := ![-5, -6, -10, -12, -8, -4]

private def a5VecC : Fin Tag.E6.rank → ℤ := ![-4, -6, -8, -12, -10, -5]

private theorem a5VecA_self : iform a5VecA a5VecA = 30 := by decide +kernel

private theorem a5VecB_self : iform a5VecB a5VecB = 30 := by decide +kernel

private theorem a5VecC_self : iform a5VecC a5VecC = 30 := by decide +kernel

private theorem a5VecA_dvd : ∀ x ∈ sA5a, (6 : ℤ) ∣ iform a5VecA (e6ExtVec x) := by decide +kernel

private theorem a5VecB_dvd : ∀ x ∈ sA5b, (6 : ℤ) ∣ iform a5VecB (e6ExtVec x) := by decide +kernel

private theorem a5VecC_dvd : ∀ x ∈ sA5c, (6 : ℤ) ∣ iform a5VecC (e6ExtVec x) := by decide +kernel

private theorem extRoot_mem_span
    {C : Finset (Option (Fin Tag.E6.rank))} {x : Option (Fin Tag.E6.rank)} (hx : x ∈ C) :
    e6ExtVec x ∈ Submodule.span ℤ (kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank)))) := by
  rw [← kacE6_extRoot]
  exact Submodule.subset_span (extRoot_mem_rootsOf kacE6 (Finset.mem_coe.2 hx))

private theorem a5VecA_mem :
    a5VecA ∈ Submodule.span ℤ (kacE6.rootsOf (↑sA5a : Set (Option (Fin Tag.E6.rank)))) := by
  have h : a5VecA = (5 : ℤ) • e6ExtVec (some 0) + (4 : ℤ) • e6ExtVec (some 2) +
      (3 : ℤ) • e6ExtVec (some 3) + (2 : ℤ) • e6ExtVec (some 4) +
      (1 : ℤ) • e6ExtVec (some 5) := by decide +kernel
  rw [h]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5a) (x := some 0) (by decide)))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5a) (x := some 2) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5a) (x := some 3) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5a) (x := some 4) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5a) (x := some 5) (by decide)))

private theorem a5VecB_mem :
    a5VecB ∈ Submodule.span ℤ (kacE6.rootsOf (↑sA5b : Set (Option (Fin Tag.E6.rank)))) := by
  have h : a5VecB = (5 : ℤ) • e6ExtVec none + (4 : ℤ) • e6ExtVec (some 1) +
      (3 : ℤ) • e6ExtVec (some 3) + (2 : ℤ) • e6ExtVec (some 4) +
      (1 : ℤ) • e6ExtVec (some 5) := by decide +kernel
  rw [h]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5b) (x := none) (by decide)))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5b) (x := some 1) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5b) (x := some 3) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5b) (x := some 4) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5b) (x := some 5) (by decide)))

private theorem a5VecC_mem :
    a5VecC ∈ Submodule.span ℤ (kacE6.rootsOf (↑sA5c : Set (Option (Fin Tag.E6.rank)))) := by
  have h : a5VecC = (5 : ℤ) • e6ExtVec none + (4 : ℤ) • e6ExtVec (some 1) +
      (3 : ℤ) • e6ExtVec (some 3) + (2 : ℤ) • e6ExtVec (some 2) +
      (1 : ℤ) • e6ExtVec (some 0) := by decide +kernel
  rw [h]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5c) (x := none) (by decide)))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5c) (x := some 1) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5c) (x := some 3) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5c) (x := some 2) (by decide))))
    (Submodule.smul_mem _ _ (extRoot_mem_span (C := sA5c) (x := some 0) (by decide)))

private theorem dvd_iform_of_mem_rootsOf_six
    {C : Finset (Option (Fin Tag.E6.rank))}
    {Ω : Fin Tag.E6.rank → ℤ} (h6 : ∀ x ∈ C, (6 : ℤ) ∣ iform Ω (e6ExtVec x))
    {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank)))) :
    (6 : ℤ) ∣ iform Ω γ := by
  obtain ⟨-, n, hn, hγn⟩ := hγ
  have hsum : ∀ m : Option (Fin Tag.E6.rank) → ℕ, (∀ x, m x ≠ 0 → x ∈ C) →
      (6 : ℤ) ∣ iform Ω (kacE6.combo m) := by
    intro m hm
    rw [iform_comm, kacE6.iform_combo_left]
    refine Finset.dvd_sum fun x _ => ?_
    by_cases hx : m x = 0
    · rw [hx]
      simp
    · rw [iform_comm, kacE6_extRoot]
      exact Dvd.dvd.mul_left (h6 x (hm x hx)) _
  have hn' : ∀ x, n x ≠ 0 → x ∈ C := fun x hx => by simpa using hn x hx
  rcases hγn with rfl | rfl
  · exact hsum n hn'
  · rw [iform_neg_right_E6]
    exact (dvd_neg).2 (hsum n hn')

private theorem a5VecA_dvd_roots :
    ∀ γ ∈ kacE6.rootsOf (↑sA5a : Set (Option (Fin Tag.E6.rank))),
      (6 : ℤ) ∣ iform a5VecA γ :=
  fun _ hγ => dvd_iform_of_mem_rootsOf_six a5VecA_dvd hγ

private theorem a5VecB_dvd_roots :
    ∀ γ ∈ kacE6.rootsOf (↑sA5b : Set (Option (Fin Tag.E6.rank))),
      (6 : ℤ) ∣ iform a5VecB γ :=
  fun _ hγ => dvd_iform_of_mem_rootsOf_six a5VecB_dvd hγ

private theorem a5VecC_dvd_roots :
    ∀ γ ∈ kacE6.rootsOf (↑sA5c : Set (Option (Fin Tag.E6.rank))),
      (6 : ℤ) ∣ iform a5VecC γ :=
  fun _ hγ => dvd_iform_of_mem_rootsOf_six a5VecC_dvd hγ

private theorem iform_neg_sub_self
    (x : Fin Tag.E6.rank → ℤ) : iform x (-x - x) = -2 * iform x x := by
  rw [iform_sub_right, iform_neg_right_E6]
  ring

private theorem smul_mem_span_smul {s : Set (Fin Tag.E6.rank → ℤ)} {μ : Fin Tag.E6.rank → ℤ}
    (h : μ ∈ Submodule.span ℤ s) (v : WeylGroup Tag.E6) :
    v • μ ∈ Submodule.span ℤ ((fun x => v • x) '' s) := by
  refine Submodule.span_induction (p := fun z _ => v • z ∈ Submodule.span ℤ ((fun x => v • x) '' s))
    ?_ ?_ ?_ ?_ h
  · intro z hz
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [smul_add]
    exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [smul_comm]
    exact Submodule.smul_mem _ a hz

private theorem not_exists_neg_of_disc
    {C : Finset (Option (Fin Tag.E6.rank))} {μ : Fin Tag.E6.rank → ℤ}
    (hμ : μ ∈ Submodule.span ℤ (kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank)))))
    (hμd : ∀ γ ∈ kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))), (6 : ℤ) ∣ iform μ γ)
    (hself : iform μ μ = 30) (v : WeylGroup Tag.E6) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun α => v • α) ''
        kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))),
        w • γ = -γ := by
  set Ψ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))) with hΨ
  have hroot : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 v
  have hsl : ∀ γ ∈ Ψ, iform γ γ = 2 := by
    rintro _ ⟨α, hα, rfl⟩
    rw [iform_smul]
    exact iform_self_E6 hα.1
  have hmem : v • μ ∈ Submodule.span ℤ Ψ := by
    rw [hΨ]
    exact smul_mem_span_smul hμ v
  have hdvd : ∀ γ ∈ Ψ, (6 : ℤ) ∣ iform (v • μ) γ := by
    rintro _ ⟨α, hα, rfl⟩
    rw [iform_smul]
    exact hμd α hα
  have hself' : iform (v • μ) (v • μ) = 30 := by
    rw [iform_smul, hself]
  have hnot : ¬ twistInner Ψ (fun γ => -γ) := by
    refine not_twistInner_of_disc hroot hsl (-AddMonoidHom.id (Fin Tag.E6.rank → ℤ)) hmem hdvd
      hdvd ?_
    change ¬ 6 * 6 ∣ iform (v • μ) (-(v • μ) - v • μ)
    rw [iform_neg_sub_self, hself']
    norm_num
  intro hcon
  apply hnot
  obtain ⟨w, hw, hwγ⟩ := hcon
  exact ⟨w, hw, fun γ hγ => (hwγ γ hγ).symm⟩

private theorem not_exists_neg_of_labelled_A5
    {C : Finset (Option (Fin Tag.E6.rank))}
    (hC : C = sA5a ∨ C = sA5b ∨ C = sA5c) (v : WeylGroup Tag.E6) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun α => v • α) ''
        kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))),
        w • γ = -γ := by
  rcases hC with rfl | rfl | rfl
  · exact not_exists_neg_of_disc a5VecA_mem a5VecA_dvd_roots a5VecA_self v
  · exact not_exists_neg_of_disc a5VecB_mem a5VecB_dvd_roots a5VecB_self v
  · exact not_exists_neg_of_disc a5VecC_mem a5VecC_dvd_roots a5VecC_self v

theorem not_exists_neg_of_e6Class_A5
    {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hap : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard = 30) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
        ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = -γ := by
  obtain ⟨ζ, u, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hsz : szF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ)
      ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ)) x = 30 := by
    rw [← hncard]
    exact hn
  have hC := kc_a5 m0 m1 m2 m3 m4 m5 hsum x hx hsz
  rw [hroots]
  exact not_exists_neg_of_labelled_A5 hC u⁻¹

end CFSG.StandardType.TablePThreeKG

end
