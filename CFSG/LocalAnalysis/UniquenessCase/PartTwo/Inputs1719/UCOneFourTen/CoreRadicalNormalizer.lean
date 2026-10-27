module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.AlmostSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.QuotientBasic
import CFSG.GroupTheory.SylowIntersectionControl.RadicalHull
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools
import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.ModO2Iso
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410.CoreSetup

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem exists_radical_normalizer (h : CoreSetup X K L T Y n)
    (hL2 : CFSG.Open.pCoreOf 2 L ≠ ⊥) :
    ∃ U : Subgroup X, U ≠ ⊥ ∧ U ≤ K ∧ CFSG.Open.pCoreOf 2 L ≤ U ∧
      CFSG.Open.pCoreOf 2 (K ⊓ normalizer (U : Set X)) = U ∧
      normalizer (L : Set X) ≤ normalizer (U : Set X) ∧ normalizer (U : Set X) ≠ ⊤ ∧
      T ≤ normalizer (U : Set X) ∧
      CFSG.Open.IsSubnormal L (K ⊓ normalizer (U : Set X)) ∧
      L ⊓ U = CFSG.Open.pCoreOf 2 L ∧
      CFSG.Open.IsComponentOf
        ((L.subgroupOf (K ⊓ normalizer (U : Set X))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊓ normalizer (U : Set X))))) ⊤ ∧
      Nonempty (↥((L.subgroupOf (K ⊓ normalizer (U : Set X))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊓ normalizer (U : Set X))))) ≃* Bar2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNK : normalizer (L : Set X) ≤ normalizer (K : Set X) := by
    rw [normalizer_eq_top_iff.mpr h.normal]
    exact le_top
  obtain ⟨U, hO2U, hUK, hUcore, hNLU, -⟩ :=
    CFSG.GroupTheory.exists_pCoreOf_inf_normalizer_eq (p := 2) hNK
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.le)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hU1 : U ≠ ⊥ := fun hU => hL2 (le_bot_iff.mp (hU ▸ hO2U))
  have hU2 : IsPGroup 2 U := hUcore ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNU : normalizer (U : Set X) ≠ ⊤ := by
    intro htop
    have hle : U ≤ CFSG.pCore 2 X :=
      CFSG.LieType.BorelTits.le_pCore 2 (normalizer_eq_top_iff.mp htop) hU2
    rw [h.pCore_eq_bot, le_bot_iff] at hle
    exact hU1 hle
  have hLN : L ≤ normalizer (U : Set X) := le_normalizer.trans hNLU
  have hTN : T ≤ normalizer (U : Set X) := h.T_le_normalizer.trans hNLU
  set P : Subgroup X := K ⊓ normalizer (U : Set X) with hP
  have hLP : L ≤ P := le_inf h.le hLN
  have hsub : CFSG.Open.IsSubnormal L P :=
    isSubnormal_mono (h.subnormal_of_le _ hNU hLN hTN) hLP inf_le_right
  have hLU : L ⊓ U = CFSG.Open.pCoreOf 2 L := by
    refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hO2U)
    have hle := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLP
    rwa [hUcore] at hle
  set Ls : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    (L.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) with hLs
  have hsubs : CFSG.Open.IsSubnormal Ls ⊤ := by
    have hmap := isSubnormal_map (H := P) hsub
    rwa [subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
  have htop : CFSG.Open.pCoreOf 2 (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) = ⊥ := by
    have hn : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P))).Normal :=
      normalizer_eq_top_iff.mp (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
    rwa [pCore_quotient_eq_bot, le_bot_iff] at hle
  have hcore : CFSG.pCore 2 ↥Ls = ⊥ := by
    have hle := CFSG.LocalAnalysis.GLTheoremB.pCoreOf_le_of_isSubnormal 2 hsubs
    rw [htop, le_bot_iff] at hle
    exact (map_eq_bot_iff_of_injective _ Ls.subtype_injective).mp hle
  obtain ⟨e₀⟩ := CFSG.Quasithin.Stellmacher.CD.L3YC.modO2_modO2Image_equiv (H := P) hLP
  let e : ↥Ls ≃* Bar2 L :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm.trans e₀
  have hSz := h.sz
  have : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have : IsSimpleGroup ↥Ls := e.isSimpleGroup
  have hnc : ∃ a b : ↥Ls, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
    refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
    simpa using congrArg e hc
  have hq : CFSG.Open.IsQuasisimple ↥Ls :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  exact ⟨U, hU1, hUK, hO2U, hUcore, hNLU, hNU, hTN, hsub, hLU, ⟨le_top, hsubs, hq⟩, ⟨e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410.CoreSetup
