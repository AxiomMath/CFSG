module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentOmegaMinusFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pow_eq_one_of_commute_barSub_1755 (D : Data G)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hB : IsBasicModule (Mbar D.M ⊥ V hV))
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G)) {n : ℕ}
    (h143 : IsL2 ↥(barSub ⊥ V hV L) n ∧
      (BinaryNaturalSL (barSub ⊥ V hV L) ⊤ (fixV (barSub ⊥ V hV L)) 2 n ∨
        (Even n ∧ NatOmegaMinus (barSub ⊥ V hV L) ⊤ ⊥ 4 (n / 2))))
    {c : MulAut (Vtil ⊥ V hV)} (hcL : ∀ l ∈ barSub ⊥ V hV L, c * l = l * c) :
    c ^ (2 ^ n - 1) = 1 := by
  have hW : ∀ w : Vtil (⊥ : Subgroup G) V hV, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨-, hcase⟩ := h143
  rcases hcase with hnat | ⟨hev, hom⟩
  · have hcomm := commV_eq_top_of_isBasicModule hB (barSub_mono ⊥ V hV hLM)
      (barSub_subgroupOf_mbar_normal hV hLM hNL) hnat
    exact pow_eq_one_of_commute_binaryNaturalSL (barSub ⊥ V hV L) n hnat hcomm c hcL
  · have h1 := Inputs1719.k_CentOmegaMinus4 _ hW _ (n / 2) hom c hcL
    obtain ⟨a, rfl⟩ := hev
    have ha : (a + a) / 2 = a := by omega
    rw [ha] at h1
    have hdvd : 2 ^ a - 1 ∣ 2 ^ (a + a) - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro 2 (mul_two a))
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, h1, one_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
