module

public import CFSG.ClassicalInvolution.Q3.Q3PlanKronecker
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action
public import CFSG.LieType.Steinberg.Classical.SpinOdd.Frame
public import CFSG.Quasithin.Background.SmithCurtisChevAmb
public import CFSG.RankThree.PartOne.KE6.Phi3Kernel
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart20
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBIE6FiniteLayers
public import CFSG.RankThree.Classical2.TwistedE6Phi3Lines
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Orbit
public import CFSG.RankThree.PartOne.KE6.Phi3Std
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi3Transport
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate1953
public import Certificates.Certificate1954

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk
universe u
variable {τ : Tag}

namespace AdjData
variable (D : AdjData τ)
variable {D}
variable (D) (R : Type*) [CommRing R]
variable {D R}

theorem rootOp_bracket_without117
    (hD : D.Valid) (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    ∀ γ : {v : Fin τ.rank → ℤ // IsRoot τ v}, γ.1 ≠ -β.1 →
      (∀ h : IsRoot τ (β.1 + γ.1), ∃ N : ℤ,
        N.natAbs = stringNorm β.1 γ.1 ∧
          ∀ (R : Type u) [CommRing R],
            D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β =
              (N : R) • D.rootOp R ⟨β.1 + γ.1, h⟩) ∧
        (¬IsRoot τ (β.1 + γ.1) → ∀ (R : Type u) [CommRing R],
          D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β = 0) := by
  obtain ⟨v, hv⟩ := β
  induction hv with
  | basis j => exact fun γ hγ => rootOp_bracket_single_without117 hD j γ hγ
  | @reflect i v hv ih =>
    intro γ hγ
    set β : {v : Fin τ.rank → ℤ // IsRoot τ v} := ⟨v, hv⟩
    set γ' := sRoot i γ with hγ'_def
    have hγγ' : γ = sRoot i γ' := (sRoot_sRoot_without117 i γ).symm
    have hne : γ'.1 ≠ -β.1 := by
      intro h
      apply hγ
      rw [hγγ']
      change reflect τ i γ'.1 = -reflect τ i v
      rw [h, CFSG.Quasithin.SmithCurtis.Chev.reflect_neg']
    obtain ⟨ih₁, ih₂⟩ := ih γ' hne
    have hsum : reflect τ i v + γ.1 = reflect τ i (β.1 + γ'.1) := by
      rw [reflect_add_without117, hγγ']
      rfl
    have hdiff : γ.1 - reflect τ i v = reflect τ i (γ'.1 - β.1) := by
      rw [reflect_sub_without117, hγγ']
      rfl
    have hsβ : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) =
        sRoot i β := rfl
    have key : ∀ (R : Type u) [CommRing R],
        D.rootOp R ⟨reflect τ i v, IsRoot.reflect i hv⟩ * D.rootOp R γ -
            D.rootOp R γ * D.rootOp R ⟨reflect τ i v, IsRoot.reflect i hv⟩ =
          ((D.rootSign β i * D.rootSign γ' i : ℤ) : R) •
            ((weylElt τ R i 1 : Module.End R (RootModule τ R)) *
              (D.rootOp R β * D.rootOp R γ' - D.rootOp R γ' * D.rootOp R β) *
              (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
                Module.End R (RootModule τ R))) := by
      intro R _
      rw [hsβ, units_conj_comm_without117, rootOp_reflect_without117 hD, hγγ',
          rootOp_reflect_without117 hD, smul_mul_smul_comm,
        smul_mul_smul_comm, mul_comm (D.rootSign γ' i : R) (D.rootSign β i : R), ← smul_sub,
        Int.cast_mul]
    refine ⟨fun h => ?_, fun hnr R _ => ?_⟩
    · have h' : IsRoot τ (β.1 + γ'.1) := by
        rw [← isRoot_reflect_iff i, ← hsum]
        exact h
      obtain ⟨N, hN, hbr⟩ := ih₁ h'
      refine ⟨D.rootSign β i * D.rootSign γ' i * D.rootSign ⟨_, h'⟩ i * N, ?_, fun R _ => ?_⟩
      · rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, hN, hγγ']
        change _ = stringNorm (reflect τ i v) (reflect τ i γ'.1)
        rw [stringNorm_reflect_without117]
        rcases rootSign_eq_without117 (D := D) β i with h1 | h1 <;>
          rcases rootSign_eq_without117 (D := D) γ' i with h2 | h2 <;>
          rcases rootSign_eq_without117 (D := D) (⟨_, h'⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) i
            with h3 | h3 <;> simp [h1, h2, h3, β]
      · rw [key, hbr R, mul_smul_comm, smul_mul_assoc, rootOp_weyl_without117 hD, smul_smul,
          smul_smul,
          rootOp_congr_without117 (R := R) (β := ⟨reflect τ i v + γ.1, h⟩) hsum.symm]
        push_cast
        ring_nf
    · have h' : ¬IsRoot τ (β.1 + γ'.1) := by
        rw [← isRoot_reflect_iff i, ← hsum]
        exact hnr
      rw [key, ih₂ h' R, mul_zero, zero_mul, smul_zero]

end AdjData

end CFSG.LieType.Steinberg.Adjoint

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open scoped Nat

variable {τ : Tag}

theorem simple_smul_eq_sRoot_without117 (i : Fin τ.rank) (α : Root τ) : simple τ i • α = sRoot i
    α :=
  Subtype.ext (simple_smul i α.1)

theorem sign_cast_eq_without117 {R : Type*} [CommRing R] {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (s : R) * (s : R) = 1 := by
  rcases hs with rfl | rfl <;> norm_num

namespace RootOperatorFamily'

variable {D : AdjData τ}

theorem exists_D_one_eq_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (α : Root τ) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∀ (R : Type) [CommRing R], F.D R α 1 = (δ : R) • D.rootOp R α := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun R _ => ?_⟩
    rw [Int.cast_one, one_smul, show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) =
      simpleRoot τ j from rfl, F.D_simple, xCoeff_one]
    exact (AdjData.rootOp_simple_without117 hD j).symm
  | @reflect i v hv ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    refine ⟨F.sign i ⟨v, hv⟩ * δ * D.rootSign ⟨v, hv⟩ i,
      CFSG.LieType.Steinberg.SpinOdd.sign_mul_sign_eq
          (CFSG.LieType.Steinberg.SpinOdd.sign_mul_sign_eq (F.sign_eq i _) hδ)
        (AdjData.rootSign_eq_without117 _ i),
      fun R _ => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot_without117 i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, pow_one, h R, mul_smul_comm, smul_mul_assoc, ← weylElt_inv,
      AdjData.rootOp_weyl_without117 hD, smul_smul, smul_smul, simple_smul_eq_sRoot_without117]
    push_cast
    ring_nf

theorem bracket_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (β γ : Root τ) (hγ : γ.1 ≠ -β.1) :
    (∀ h : IsRoot τ (β.1 + γ.1), ∃ N : ℤ, N.natAbs = stringNorm β.1 γ.1 ∧
      ∀ (R : Type) [CommRing R],
        F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = (N : R) • F.D R ⟨β.1 + γ.1, h⟩ 1) ∧
      (¬IsRoot τ (β.1 + γ.1) → ∀ (R : Type) [CommRing R],
        F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = 0) := by
  let delta : Root τ → ℤ := fun a => (exists_D_one_eq_without117 F hD a).choose
  have hdelta : ∀ a, delta a = 1 ∨ delta a = -1 := fun a =>
    (exists_D_one_eq_without117 F hD a).choose_spec.1
  have hE : ∀ a (R : Type) [CommRing R], F.D R a 1 = (delta a : R) • D.rootOp R a :=
    fun a R _ => (exists_D_one_eq_without117 F hD a).choose_spec.2 R
  have hErev : ∀ a (R : Type) [CommRing R], D.rootOp R a = (delta a : R) • F.D R a 1 := by
    intro a R _
    rw [hE a, smul_smul, sign_cast_eq_without117 (hdelta a), one_smul]
  obtain ⟨h₁, h₂⟩ := AdjData.rootOp_bracket_without117.{0} hD β γ hγ
  have key : ∀ (R : Type) [CommRing R], F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 =
      ((delta β * delta γ : ℤ) : R) •
        (D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β) := by
    intro R _
    rw [hE β, hE γ, smul_mul_smul_comm, smul_mul_smul_comm,
      mul_comm (delta γ : R), ← smul_sub, Int.cast_mul]
  refine ⟨fun h => ?_, fun hn R _ => by rw [key, h₂ hn R, smul_zero]⟩
  obtain ⟨N, hN, hbr⟩ := h₁ h
  refine ⟨delta β * delta γ * delta ⟨_, h⟩ * N, ?_, fun R _ => ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, hN]
    rcases hdelta β with h1 | h1 <;> rcases hdelta γ with h2 | h2 <;>
      rcases hdelta (⟨_, h⟩ : Root τ) with h3 | h3 <;> simp [h1, h2, h3]
  · rw [key, hbr R, hErev, smul_smul, smul_smul]
    push_cast
    ring_nf

end RootOperatorFamily'

end CFSG.LieType.Steinberg.Adjoint

end

public section

namespace CFSG.StandardType.F4ExplicitPos.CentralizerGuard

open CFSG.Blueprint.Chevalley

abbrev F4End (K : Type*) [Field K] : Type _ :=
  (Module.End K (RootModule Tag.F4 K))ˣ

theorem commute_pinnedX_of_commute_subfield
    (K : Type*) [Field K] (E : Subfield K) [Fintype E]
    (hE : 4 ≤ Fintype.card E) (α : Fin Tag.F4.rank → ℤ) (g : F4End K)
    (hg : ∀ c : E, g * pinnedX Tag.F4 K α (c : K) =
      pinnedX Tag.F4 K α (c : K) * g) :
    ∀ c : K, g * pinnedX Tag.F4 K α c = pinnedX Tag.F4 K α c * g := by
  classical
  let S : Finset K := Finset.univ.image fun c : E => (c : K)
  have hScard : S.card = Fintype.card E := by
    rw [show S = Finset.univ.image (fun c : E => (c : K)) from rfl]
    rw [Finset.card_image_of_injective Finset.univ
      (f := fun c : E => (c : K)) Subtype.val_injective, Finset.card_univ]
  have hS : Fintype.card E ^ 1 ≤ S.card := by
    rw [pow_one, hScard]
  have hmain := CFSG.ClassicalInvolution.Q3.commute_unit_family
    (k := K) (V := RootModule Tag.F4 K)
    (Fintype.card E) hE 1 S hS
    (fun _ s => pinnedX Tag.F4 K α s)
    (fun _ m => pinnedCoeff Tag.F4 K α m)
    (fun _ => pinnedCoeff_zero Tag.F4 K α)
    (fun _ s => pinnedX_eq_sum Tag.F4 K α s)
    g ?_
  · intro c
    exact hmain 0 Nat.zero_lt_one c
  · intro c hc
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hc
    simpa using hg e

theorem commute_pinnedX_of_commute_subfield_charTwo
    (K : Type*) [Field K] [CharP K 2] (E : Subfield K) [Fintype E]
    (hE : 4 ≤ Fintype.card E) (α : Fin Tag.F4.rank → ℤ) (g : F4End K)
    (hg : ∀ c : E, g * pinnedX Tag.F4 K α (c : K) =
      pinnedX Tag.F4 K α (c : K) * g) :
    ∀ c : K, g * pinnedX Tag.F4 K α c = pinnedX Tag.F4 K α c * g :=
  commute_pinnedX_of_commute_subfield K E hE α g hg

noncomputable def subfieldRootSpan
    (K : Type*) [Field K] (E : Subfield K)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Subgroup (F4End K) :=
  Subgroup.closure {x | ∃ α ∈ Ψ, ∃ c : E, x = pinnedX Tag.F4 K α (c : K)}

theorem subfieldRootSpan_le_rootSpan
    (K : Type*) [Field K] (E : Subfield K)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    subfieldRootSpan K E Ψ ≤ rootSpan Tag.F4 K Ψ := by
  rw [subfieldRootSpan, Subgroup.closure_le]
  rintro x ⟨α, hα, c, rfl⟩
  rw [rootSpan]
  exact Subgroup.mem_iSup_of_mem α
    (Subgroup.mem_iSup_of_mem hα
      (Subgroup.subset_closure ⟨(c : K), rfl⟩))

theorem centralizer_subfieldRootSpan_eq
    (K : Type*) [Field K] (E : Subfield K) [Fintype E]
    (hE : 4 ≤ Fintype.card E) (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    Subgroup.centralizer ((subfieldRootSpan K E Ψ : Subgroup (F4End K)) : Set (F4End K)) =
      Subgroup.centralizer ((rootSpan Tag.F4 K Ψ : Subgroup (F4End K)) : Set (F4End K)) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro h hh
    have hguard : ∀ α ∈ Ψ, ∀ c : K,
        g * pinnedX Tag.F4 K α c = pinnedX Tag.F4 K α c * g := by
      intro α hα
      refine commute_pinnedX_of_commute_subfield K E hE α g ?_
      intro c
      have hmem : pinnedX Tag.F4 K α (c : K) ∈ subfieldRootSpan K E Ψ :=
        Subgroup.subset_closure ⟨α, hα, c, rfl⟩
      exact (hg (pinnedX Tag.F4 K α (c : K)) hmem).symm
    have hle : rootSpan Tag.F4 K Ψ ≤ Subgroup.centralizer ({g} : Set (F4End K)) := by
      rw [rootSpan]
      apply iSup_le; intro α
      apply iSup_le; intro hα
      rw [rootSubgroup, Subgroup.closure_le]
      rintro y ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hguard α hα c).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  · exact Subgroup.centralizer_le fun x hx => subfieldRootSpan_le_rootSpan K E Ψ hx

theorem centralizer_subfieldRootSpan_eq_charTwo
    (K : Type*) [Field K] [CharP K 2]
    (E : Subfield K) [Fintype E] (hE : 4 ≤ Fintype.card E)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    Subgroup.centralizer ((subfieldRootSpan K E Ψ : Subgroup (F4End K)) : Set (F4End K)) =
      Subgroup.centralizer ((rootSpan Tag.F4 K Ψ : Subgroup (F4End K)) : Set (F4End K)) :=
  centralizer_subfieldRootSpan_eq K E hE Ψ

theorem center_subfieldRootSpan_eq
    (K : Type*) [Field K] (E : Subfield K) [Fintype E]
    (hE : 4 ≤ Fintype.card E) (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    (Subgroup.center ↥(subfieldRootSpan K E Ψ)).map
        (subfieldRootSpan K E Ψ).subtype =
      subfieldRootSpan K E Ψ ⊓
        Subgroup.centralizer
          ((rootSpan Tag.F4 K Ψ : Subgroup (F4End K)) : Set (F4End K)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_inf]
    refine ⟨z.2, ?_⟩
    have hguard : ∀ α ∈ Ψ, ∀ c : K,
        (z : F4End K) * pinnedX Tag.F4 K α c =
          pinnedX Tag.F4 K α c * (z : F4End K) := by
      intro α hα
      refine commute_pinnedX_of_commute_subfield K E hE α (z : F4End K) ?_
      intro c
      have hmem : pinnedX Tag.F4 K α (c : K) ∈ subfieldRootSpan K E Ψ :=
        Subgroup.subset_closure ⟨α, hα, c, rfl⟩
      have hcz := Subgroup.mem_center_iff.mp hz
        ⟨pinnedX Tag.F4 K α (c : K), hmem⟩
      exact (congrArg Subtype.val hcz).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : rootSpan Tag.F4 K Ψ ≤
        Subgroup.centralizer ({↑z} : Set (F4End K)) := by
      rw [rootSpan]
      apply iSup_le; intro α
      apply iSup_le; intro hα
      rw [rootSubgroup, Subgroup.closure_le]
      rintro y ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hguard α hα c).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH0, hxcent⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH0⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : F4End K)
      (subfieldRootSpan_le_rootSpan K E Ψ y.2)

theorem center_subfieldRootSpan_eq_charTwo
    (K : Type*) [Field K] [CharP K 2]
    (E : Subfield K) [Fintype E] (hE : 4 ≤ Fintype.card E)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    (Subgroup.center ↥(subfieldRootSpan K E Ψ)).map
        (subfieldRootSpan K E Ψ).subtype =
      subfieldRootSpan K E Ψ ⊓
        Subgroup.centralizer
          ((rootSpan Tag.F4 K Ψ : Subgroup (F4End K)) : Set (F4End K)) :=
  center_subfieldRootSpan_eq K E hE Ψ

end CFSG.StandardType.F4ExplicitPos.CentralizerGuard

end

end

end

end

end

end

end

end
