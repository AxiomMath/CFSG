module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.Quasithin.Vol2.Ch3B513NC1SL2
import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16jp_row_SL2 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2) :
    rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 := by
  obtain ⟨_, hBN⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
  letI := hKf
  letI := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  haveI : Group.IsPerfect (FFModel.nat (StatedSL 2 K)).Gam :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := π) hπ.1
  have hmem : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup W), l y ∈ (⊤ : Subgroup W) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hinv : ∀ x ∈ L, ∀ v ∈ commSub ⊤ L, x v ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) hmem
  have hcomm : XMod.commOf ↥L (commSub ⊤ L) = commSub ⊤ L := by
    rw [commOf_eq_commSub, s16jp_commSub_commSub hperf (Y := ⊤) hmem]
  have hreal' : (FFModel.nat (StatedSL 2 K)).Realizes L (commSub ⊤ L)
      (fixV L ⊓ commSub ⊤ L) := by
    rw [inf_comm]
    exact ⟨π, hπ⟩
  have hcard : Nat.card ↥(fixV L ⊓ commSub ⊤ L) ≤ 2 ^ 2 :=
    B513N.card_fixV_le_of_sl2 hW2 L (commSub ⊤ L) hinv hcomm (n := 2) le_rfl hKcard hreal'
  rw [inf_comm] at hcard
  change padicValNat 2 (Nat.card ↥(commSub ⊤ L ⊓ fixV L)) ≤ 2
  calc padicValNat 2 (Nat.card ↥(commSub ⊤ L ⊓ fixV L))
      ≤ Nat.log 2 (Nat.card ↥(commSub ⊤ L ⊓ fixV L)) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ 2) := Nat.log_mono_right hcard
    _ = 2 := Nat.log_pow (by norm_num) 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
