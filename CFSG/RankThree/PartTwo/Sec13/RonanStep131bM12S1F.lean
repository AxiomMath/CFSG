module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvA
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvTools
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open M12Inv in
theorem s1f_of (hA : InvPartA) : S1F := by
  intro G _ _ A c L E F a b R Y hY hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Sec13Data G F b Y := hY.hD
  obtain ⟨-, hbY, hF9⟩ := hA G F b Y hD hM
  refine ⟨?_, (Item131bProof.inf_thetaQuotCentralizer_eq hD).le⟩
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hD.isElemAbelian
  have hF27 : Nat.card F = 27 := hD.card_eq
  have hbF : b ∈ F := hD.mem_A
  have hb3 : b ^ 3 = 1 := hFe.2 b hbF
  have hb1 : b ≠ 1 := hD.ne_one
  have hbc : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hy)
  have hle : Subgroup.zpowers b ⊔ (F ⊓ Y) ≤ F :=
    sup_le (Subgroup.zpowers_le.mpr hbF) inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ (F ⊓ Y : Subgroup G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hbc y hy.2).symm j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf : Subgroup.zpowers b ⊓ (F ⊓ Y) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (zpowers_inf_eq_bot' hb3 hbY).le)
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have h27 : Nat.card (Subgroup.zpowers b ⊔ (F ⊓ Y) : Subgroup G) = 27 := by
    rw [hinf, Subgroup.card_bot, mul_one, hcardb, hF9] at hcard
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF27, h27])).symm

theorem s1f_holds
    (h131a : Item131a) : S1F :=
  s1f_of (invPartA_of h131a sporadicModels131)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
