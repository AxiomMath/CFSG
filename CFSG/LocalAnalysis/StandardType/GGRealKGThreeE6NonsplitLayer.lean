module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitSimple
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitReflection
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitReference
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitConjugation
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggKGRootDatumAt_e6QPlusThree
    (D : E6QPlusThreeFrame K) (F : ExcFrame .E6 K 3 D.frame.range)
    (hw : F.w = e6W0) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.frame s : ModGL .E6 K) = F.D.g0 * e6ThreeDiag ζ hζ s * F.D.g0⁻¹)
    (hq : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    (hsurj : Function.Surjective D.weyl) :
    GGKGRootDatumAt 3 D.frame.range := by
  classical
  intro w₀ hrefl
  obtain ⟨w, hw2, hfix, hact_w⟩ := exists_weyl_of_GGKGIsReflAt D hrefl
  obtain ⟨v, i, hwconj⟩ := f4_involution_fixed_hyperplane_conj_simple hw2 hfix
  obtain ⟨r, J, hrJ, hact_r, hcomp, hdvd⟩ :=
    exists_component_of_conj_simple D hsurj
      (fun a => exists_simple_realization D F hw hζo hζ hcoord hq h3 a) hwconj
  have hfix_set :
      ((D.frame.range ⊓
        Subgroup.centralizer ({r} : Set (adjointGroup .E6 K)) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) =
        SuSplitRootGen.torusFix D.frame (TableBExc.torusAct .F4 3 w) := by
    ext e
    constructor
    · intro he
      change e ∈ (D.frame.range ⊓
        Subgroup.centralizer ({r} : Set (adjointGroup .E6 K)) :
          Subgroup (adjointGroup .E6 K)) at he
      rw [Subgroup.mem_inf] at he
      obtain ⟨heE, heC⟩ := he
      obtain ⟨x, rfl⟩ := heE
      rw [SuSplitRootGen.torusFix]
      refine ⟨x, ?_, rfl⟩
      have hcomm : D.frame x * r = r * D.frame x :=
        Subgroup.mem_centralizer_singleton_iff.mp heC
      have hfix_r : r * D.frame x * r⁻¹ = D.frame x := by
        calc
          r * D.frame x * r⁻¹ = (r * D.frame x) * r⁻¹ := by group
          _ = (D.frame x * r) * r⁻¹ := by rw [hcomm.symm]
          _ = D.frame x := by group
      have hvec : TableBExc.torusAct .F4 3 w (Multiplicative.toAdd x) =
          Multiplicative.toAdd x := by
        apply D.frame_injective
        calc
          D.frame (Multiplicative.ofAdd
              (TableBExc.torusAct .F4 3 w (Multiplicative.toAdd x))) =
              r * D.frame (Multiplicative.ofAdd (Multiplicative.toAdd x)) * r⁻¹ :=
                (hact_r (Multiplicative.toAdd x)).symm
          _ = r * D.frame x * r⁻¹ := by rw [ofAdd_toAdd]
          _ = D.frame x := hfix_r
          _ = D.frame (Multiplicative.ofAdd (Multiplicative.toAdd x)) := by
                rw [ofAdd_toAdd]
      exact hvec
    · intro he
      rw [SuSplitRootGen.torusFix] at he
      obtain ⟨x, hx, rfl⟩ := he
      change D.frame x ∈ (D.frame.range ⊓
        Subgroup.centralizer ({r} : Set (adjointGroup .E6 K)) :
          Subgroup (adjointGroup .E6 K))
      rw [Subgroup.mem_inf]
      refine ⟨⟨x, rfl⟩, ?_⟩
      have hfix_r : r * D.frame x * r⁻¹ = D.frame x := by
        calc
          r * D.frame x * r⁻¹ =
              r * D.frame (Multiplicative.ofAdd (Multiplicative.toAdd x)) * r⁻¹ := by
                rw [ofAdd_toAdd]
          _ = D.frame (Multiplicative.ofAdd
              (TableBExc.torusAct .F4 3 w (Multiplicative.toAdd x))) :=
                hact_r (Multiplicative.toAdd x)
          _ = D.frame (Multiplicative.ofAdd (Multiplicative.toAdd x)) := by rw [hx]
          _ = D.frame x := by rw [ofAdd_toAdd]
      have hcomm : D.frame x * r = r * D.frame x := by
        calc
          D.frame x * r = (r * D.frame x * r⁻¹) * r := by rw [hfix_r]
          _ = r * D.frame x := by group
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  refine ⟨r, ?_, J, hrJ, ?_, hdvd, ?_⟩
  · intro e he
    obtain ⟨x, rfl⟩ := he
    rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from
      (ofAdd_toAdd x).symm]
    rw [hact_r (Multiplicative.toAdd x), ← hact_w (Multiplicative.toAdd x)]
  · have hcomp' : Assembly.IsComponentOf J
        (Subgroup.centralizer ((D.frame.range ⊓
          Subgroup.centralizer ({r} : Set (adjointGroup .E6 K)) :
            Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) := by
      simpa only [← hfix_set] using hcomp
    exact hcomp'
  · intro a ha har
    have haFix : a ∈ SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 w) := by
      rw [← hfix_set]
      exact Subgroup.mem_inf.mpr
        ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr har.symm⟩
    have hJa : J ≤ Subgroup.centralizer ({a} : Set (adjointGroup .E6 K)) := by
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hx)) a haFix).symm
    have hap : a ^ 3 = 1 :=
      (CFSG.StandardType.ExcFrames.isElemAbelian_range_frame D.frame).2 a ha
    have hJperf : ⁅J, J⁆ = J :=
      CFSG.LocalAnalysis.ComponentInitial.commutator_self_of_commutator_eq_top
        hcomp.2.2.1
    have : Finite (ModGL .E6 K) := finite_modGL
    have : Finite ↥(adjointGroup .E6 K) :=
      Finite.of_injective (Subtype.val : ↥(adjointGroup .E6 K) → ModGL .E6 K)
        Subtype.val_injective
    obtain ⟨hS, hnc⟩ := LayerCores.adjointGroup_isSimple_nonabelian
      (τ := .E6) (Or.inr (Or.inl rfl)) K
    have hchev := LayerCores.isChevSimple_adjointGroup_charTwo
      (τ := .E6) (Or.inr (Or.inl rfl)) K
    exact ggKG_layer_of_chevSimple (p := 3) hS hnc hchev Nat.prime_three
      (by norm_num) hap hJperf hJa

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
