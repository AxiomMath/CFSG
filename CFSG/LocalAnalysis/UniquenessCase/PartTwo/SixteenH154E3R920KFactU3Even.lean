module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem kFactL28_U3_even {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hQ : LieModel Q .PSU 3 2 f)
    {X W T : Subgroup Q} (c : KCfgL28 X W T) : W = ⊤ := by
  haveI : IsSimpleGroup Q := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hQ
  have hB : fusionIsBenderGroup Q := uc22p2214_bor_bender_U3 hQ
  have hBor : fusionBenderBorel Q (2 ^ f) 3 :=
    CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_PSU3 hQ
  obtain ⟨S, hS⟩ := uc22p2214_bor_sylow c.T_sylow
  by_contra hW
  have hQle : (S : Subgroup Q) ≤ W := hS ▸ c.T_le
  have hle : W ≤ Subgroup.normalizer ((S : Subgroup Q) : Set Q) :=
    CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB S hQle hW
  have hsolvN : Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q)) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_normalizer_of_benderBorel hBor S
  have hsolvW : Group.IsSolvable ↥W := by
    haveI := hsolvN
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion c.X_le)
      (Subgroup.inclusion_injective c.X_le)
  have hcard504 : Nat.card (Bar2 X) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) c.isL2
  haveI : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal (p := 2) (G := ↥X)
  have hsolvBar : Group.IsSolvable (Bar2 X) := by
    haveI := hsolvX
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  have hcomm : ∀ a b : Bar2 X, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hsolvBar
  have hprime : (Nat.card (Bar2 X)).Prime := by
    haveI : IsMulCommutative (Bar2 X) := IsMulCommutative.of_comm hcomm
    exact (Group.is_simple_iff_prime_card (α := Bar2 X)).mp hsimple
  rw [hcard504] at hprime
  norm_num at hprime

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
