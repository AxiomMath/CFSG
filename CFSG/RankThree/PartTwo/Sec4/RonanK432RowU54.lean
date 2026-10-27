module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432E9Rot
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofU54Datum
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4.Res417Four

theorem ab_comm_u54 :
    (U54.α : projSU 5 2 2) * (U54.β : projSU 5 2 2) =
      (U54.β : projSU 5 2 2) * (U54.α : projSU 5 2 2) := by
  have hc : Commute ((U54.w, 1) : Item434SmallTwoOther.UTools.Z₃ × Item434SmallTwoOther.UTools.Z₃)
    (1, U54.w) := Commute.all _ _
  exact (hc.map U54.δ).eq

theorem closure_αβ_eq :
    Subgroup.closure ({(U54.α : projSU 5 2 2), (U54.β : projSU 5 2 2)} : Set (projSU 5 2 2)) =
      (Item434SmallTwoOther.UTools.P₀U 5 (by norm_num) : Subgroup (projSU 5 2 2)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact U54.α.2
    · exact U54.β.2
  · intro x hx
    obtain ⟨i, j, hij⟩ := U54.exists_zpow_mul ⟨x, hx⟩
    have hx' : x = (U54.α : projSU 5 2 2) ^ i * (U54.β : projSU 5 2 2) ^ j := by
      have := congrArg Subtype.val hij
      simpa only [Subgroup.coe_mul, Subgroup.coe_zpow] using this
    rw [hx']
    have ha : (U54.α : projSU 5 2 2) ∈
        Subgroup.closure ({(U54.α : projSU 5 2 2), (U54.β : projSU 5 2 2)} : Set (projSU 5 2 2)) :=
      Subgroup.subset_closure (by simp)
    have hb : (U54.β : projSU 5 2 2) ∈
        Subgroup.closure ({(U54.α : projSU 5 2 2), (U54.β : projSU 5 2 2)} : Set (projSU 5 2 2)) :=
      Subgroup.subset_closure (by simp)
    exact mul_mem (zpow_mem ha i) (zpow_mem hb j)

theorem card_closure_αβ :
    Nat.card (Subgroup.closure ({(U54.α : projSU 5 2 2), (U54.β : projSU 5 2 2)} :
      Set (projSU 5 2 2))) = 9 := by
  rw [closure_αβ_eq]
  exact Item434SmallTwoOther.UTools.card_P₀U (by norm_num)

theorem not_27_dvd_card_u54 : ¬ 27 ∣ Nat.card (projSU 5 2 2) := by
  intro h
  have hne : Nat.card (projSU 5 2 2) ≠ 0 := by
    intro h0
    have h2 := Item434SmallTwoOther.U54.factorization_card_U54
    rw [h0, Nat.factorization_zero] at h2
    simp at h2
  have h3 : 3 ^ 3 ∣ Nat.card (projSU 5 2 2) := h
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h3
  rw [Item434SmallTwoOther.U54.factorization_card_U54] at h4
  omega

theorem rot_α : (U54.nR : projSU 5 2 2) * (U54.α : projSU 5 2 2) *
    (U54.nR : projSU 5 2 2)⁻¹ = (U54.β : projSU 5 2 2) := by
  rw [← U54.nmh_apply]
  exact congrArg Subtype.val U54.ρA_α

theorem rot_β : (U54.nR : projSU 5 2 2) * (U54.β : projSU 5 2 2) *
    (U54.nR : projSU 5 2 2)⁻¹ = (U54.α : projSU 5 2 2)⁻¹ := by
  rw [← U54.nmh_apply]
  have h := congrArg Subtype.val U54.ρA_β
  rw [Subgroup.coe_inv] at h
  exact h

theorem listRow_u54 [Finite (projSU 5 2 2)] : ListRow (projSU 5 2 2) :=
  listRow_of_E9_rotation (a := (U54.α : projSU 5 2 2)) (b := (U54.β : projSU 5 2 2))
    (r := (U54.nR : projSU 5 2 2)) ab_comm_u54 rot_α rot_β card_closure_αβ not_27_dvd_card_u54

theorem outerRow_u54 [Finite (projSU 5 2 2)] : OuterRow (projSU 5 2 2) :=
  outerRow_of_not_three_dvd_outer outU54_holds

theorem row_u54 : RowOf (projSU 5 2 2) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSU 5 2 2) := Item434SmallTwoOther.UTools.finite_projSU_gf16 5
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_u54, outerRow_u54⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
