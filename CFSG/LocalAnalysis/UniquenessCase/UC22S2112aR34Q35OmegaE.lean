module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35ClassicalE
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaCore
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaFrame
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K3Transport
import CFSG.Blueprint.OddStandardExact
import CFSG.Blueprint.RecognitionDefs
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeMat
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutStd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open CFSG.Blueprint CFSG.GroupTheory CFSG.OddStandard.SmallF3.Omega

theorem omega7_three_sylowPQMaximal_of_lieModel
    (hE5 : ∀ (X : Type) [Group X], LieModel X .PSp 2 3 1 → SylowPQMaximal 2 5 X)
    (hE6 : ∀ (X : Type) [Group X], LieModel X .PSU 4 3 1 → SylowPQMaximal 2 5 X)
    {K : Type} [Field K] (hK : Nat.card K = 3) :
    SylowPQMaximal 2 5 (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) := by
  obtain ⟨fr⟩ := sec4I_exists_frame
  have hE : SylowPQMaximal 2 5 (omegaGroup sec4IQ_nondegenerate) :=
    sylowPQMaximal_omegaGroup_seven_of_twoSubgroup sec4IQ_nondegenerate sec4IQ_finrank
      (frameSignGroup fr) (frameSignGroup_le_omegaGroup sec4IQ_nondegenerate fr)
      (isPGroup_frameSignGroup fr) (fun W h0 h1 hW =>
        exists_split_of_frameSignGroup_invariant hE5 hE6 sec4IQ_nondegenerate fr W h0 h1 hW)
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨e₁⟩ := nonempty_statedOmega_quadOdd_mulEquiv (K := K) (L := ZMod 3)
    (by rw [hK, Nat.card_zmod]) 3
  have hcoe : CFSG.Open.StatedQuadOdd 3 (ZMod 3) = ⇑Sec4IQ :=
    (CFSG.LieType.Universal.Spin.coe_quadOdd 3 (ZMod 3)).symm
  let e₂ := MulEquiv.subgroupCongr (congrArg CFSG.Open.StatedOmega hcoe)
  let e₃ := statedOmegaMulEquivOmegaGroup Sec4IQ sec4IQ_nondegenerate (by decide)
  exact SylowPQMaximal.of_mulEquiv (e₁.trans (e₂.trans e₃)).symm hE

theorem omega7_three_sylowPQMaximal_of_covers
    (hSp3 : ∀ (K : Type) [Field K], Nat.card K = 3 →
      SylowPQMaximal 2 5 (CFSG.Open.StatedSp 2 K))
    (hSU : ∀ (K : Type) [Field K], Nat.card K = 9 →
      SylowPQMaximal 2 5 (CFSG.Open.StatedSU 4 3 K))
    {K : Type} [Field K] (hK : Nat.card K = 3) :
    SylowPQMaximal 2 5 (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) :=
  omega7_three_sylowPQMaximal_of_lieModel
    (fun _ _ hX => uc22s2112r34q35_sylowPQMaximal_psp (Or.inl rfl) hX hSp3)
    (fun _ _ hX => uc22s2112r34q35_sylowPQMaximal_psu hX hSU) hK

theorem omega7_three_sylowPQMaximal {K : Type} [Field K]
    (hK : Nat.card K = 3) :
    CFSG.GroupTheory.SylowPQMaximal 2 5
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) :=
  omega7_three_sylowPQMaximal_of_covers
    (fun _ _ hK => Q35Natural.sp4_three_sylowPQMaximal hK)
    (fun _ _ hK => Q35Natural.su4_three_sylowPQMaximal hK) hK

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7
