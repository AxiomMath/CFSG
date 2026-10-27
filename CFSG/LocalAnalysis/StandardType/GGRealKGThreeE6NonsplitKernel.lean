module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenComp
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality

section Components

theorem isComponentOf_comap_rootSpan_familyKernel {τ : Tag} {L : Type} [Field L]
    {R : Type*} [Group R] {ι : Type} (Y : R →* ModGL τ L) (hY : Function.Injective Y)
    (hYC : ∀ r, Y r ∈ adjointGroup τ L) (T : ι → R) (a : ι → Fin τ.rank → Lˣ)
    (hT : ∀ i, Y (T i) = rootDiagUnit τ (a i))
    (hQ : CFSG.IsQuasisimple ((rootSpan τ L (familyKernel a)).comap Y)) :
    CFSG.Assembly.IsComponentOf ((rootSpan τ L (familyKernel a)).comap Y)
      (Subgroup.centralizer (Set.range T)) := by
  classical
  let J := (rootSpan τ L (familyKernel a)).comap Y
  let C := Subgroup.centralizer (Set.range T)
  have hJC : J ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    apply hY
    rw [map_mul, map_mul, hT]
    exact (Subgroup.mem_centralizer_iff.mp
      (rootSpan_le_centralizer (a i) (fun β hβ => ⟨hβ.1, hβ.2 i⟩) hx)) _
      (Set.mem_singleton _)
  have hCn : C ≤ Subgroup.normalizer (J : Set R) := by
    refine le_trans ?_ (Subgroup.le_normalizer_comap Y)
    intro x hx
    apply familyCentralizer_le_normalizer_rootSpan a
    rw [mem_familyCentralizer]
    refine ⟨hYC x, fun i => ?_⟩
    have hc := congrArg Y ((Subgroup.mem_centralizer_iff.mp hx) (T i) (Set.mem_range_self i))
    rw [map_mul, map_mul, hT] at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨hJC, CFSG.Assembly.IsSubnormal.step hJC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hCn)
    (CFSG.Assembly.IsSubnormal.refl C), ⟨hQ.1.commutator_eq_top, hQ.2.1⟩⟩

end Components

theorem familyKernel_twE6ThreeFrame {L : Type} [Field L]
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (a : Fin Tag.F4.rank) :
    familyKernel (fun s : {s : Fin Tag.F4.rank → ZMod 3 //
        TableBExc.torusAct .F4 3 (simple Tag.F4 a) s = s} =>
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)) =
      signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa only [twE6ThreeFrame, twE6SplitTheta, TwistTag.tag] using
    TwE6SplitRootGen.familyKernel_frameCoord_twE6Split (by decide : (3 : ℕ) ≠ 2) hζo hζ a

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
