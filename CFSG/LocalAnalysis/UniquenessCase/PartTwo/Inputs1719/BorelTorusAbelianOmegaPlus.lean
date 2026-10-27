module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open scoped commutatorElement

theorem isMulCommutative_normalizerQuotient_plusProjectiveUnipotent {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n) :
    IsMulCommutative (normalizerQuotient (plusProjectiveUnipotent n K)) :=
  CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_borel
    (plusProjectiveUnipotent_normalizer n K hn)
    fun _ hb _ hc => CFSG.AGLEmbedding.ParabAutIrr.plus_commutator_mem_unipotent n hn hb hc

theorem k_BorelSimple_POmegaPlus : KBorelSimple .POmegaPlus := by
  intro Y _ _ m f hadm hY S hS
  have hm4 : 4 ≤ m := by simpa only [CFSG.Open.StatedLieAdmissible] using hadm.2.2
  have hf1 : 1 ≤ f := hadm.2.1
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
    hY.statedClassicalModel (t := .POmegaPlus) (by decide)
  have hchar : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hf1 hKcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hchar ▸ ringChar.charP K
  obtain ⟨P, hP⟩ := plusProjectiveUnipotent_isSylow (n := m) (K := K) 2 (by omega)
  have hU : IsSylowTwoOf (plusProjectiveUnipotent m K) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hcomm : IsMulCommutative (normalizerQuotient (plusProjectiveUnipotent m K)) :=
    isMulCommutative_normalizerQuotient_plusProjectiveUnipotent (K := K) (by omega)
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e hS hU
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm hcomm

theorem k_BorelTorusAbelian_POmegaPlus_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_POmegaPlus :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .POmegaPlus (by decide)
    k_BorelSimple_POmegaPlus (k_BorelTorusAbelian_centerTwo_of_griess hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
