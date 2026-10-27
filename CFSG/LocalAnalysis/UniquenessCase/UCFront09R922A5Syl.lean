module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09e
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
import CFSG.Quasithin.H13.NQBlockResidualSupplement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_pCoreOf_sup_I9 {D : Data G} {Y H D₃ S : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5) (hSH : IsSylowOf 2 S H) :
    IsSylowOf 2 (pCoreOf 2 Y) (pCoreOf 2 Y ⊔ I9 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYH : Y ≤ H := hY.1.2.1.1
  have hSY : IsSylowOf 2 S Y := hY.2.2.2
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hIH : I9 H ≤ H := map_subtype_le _
  have hHI : H ≤ normalizer (I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hRS : pCoreOf 2 Y ≤ S := by
    have h := hSY.eq_of_le le_sup_left (sup_le hSY.le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
      (IsPGroup.to_sup_of_normal_right' hSY.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
        (hSY.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)))
    exact le_sup_right.trans h.le
  have hXI : Opp 3 Y ⊓ I9 H ≤ pCoreOf 2 Y :=
    (inf_I9_le_pCoreOf le_rfl (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm hA5
      (hXY.trans hYH)).trans
      (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hXY (le_normalizer_opp_self 3 Y))
  have key : ∀ x ∈ Opp 3 Y, ∀ u ∈ S ⊓ I9 H, x * u * x⁻¹ ∈ S ⊓ I9 H := by
    intro x hx u hu
    have hxu : x * u * x⁻¹ ∈ I9 H := (mem_normalizer_iff.1 (hHI (hYH (hXY hx))) u).1 hu.2
    have hc : x * u * x⁻¹ * u⁻¹ ∈ Opp 3 Y ⊓ I9 H := by
      refine mem_inf.2 ⟨?_, (I9 H).mul_mem hxu ((I9 H).inv_mem hu.2)⟩
      simpa [mul_assoc] using
        (Opp 3 Y).mul_mem hx (conj_mem_opp_self (hSY.le hu.1) ((Opp 3 Y).inv_mem hx))
    exact mem_inf.2 ⟨by simpa using S.mul_mem (hRS (hXI hc)) hu.1, hxu⟩
  have hXN : Opp 3 Y ≤ normalizer ((S ⊓ I9 H : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff.2 fun u => ⟨key x hx u, fun h => by
      simpa [mul_assoc] using key x⁻¹ ((Opp 3 Y).inv_mem hx) _ h⟩
  have hSN : S ≤ normalizer ((S ⊓ I9 H : Subgroup G) : Set G) :=
    (le_inf le_normalizer (hSH.le.trans hHI)).trans inf_normalizer_le_normalizer_inf
  have hSIR : S ⊓ I9 H ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hSY.le)
      (le_of_le_of_isSylowOf hXN hSN hSY hY.2.1.1.2.2.2.2) (hSY.isPGroup.to_le inf_le_left)
  have hRI : pCoreOf 2 Y ⊓ I9 H = S ⊓ I9 H :=
    le_antisymm (inf_le_inf_right _ hRS) (le_inf hSIR inf_le_right)
  rw [sup_comm]
  exact CFSG.Quasithin.H13.NQBlock.isSylowOf_sup_of_inf
    ((hRS.trans hSY.le).trans (hYH.trans hHI)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    (hRI ▸ hSH.inf_of_le_normalizer hIH hHI)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
