module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofInner
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Eng
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem res3L125_isPGroup_two_outer_ON
    {S : Type} [Group S] (e : S ≃* Blueprint.NativeSporadic.ON) : IsPGroup 2 (Outer S) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [pow_one]
    exact CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e⟩)

theorem res3L125_exists_exponent_three_le_centralizer_ON
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.ON) {x : S}
    (hx : orderOf x = 3) :
    ∃ T : Subgroup S, T ≤ Subgroup.centralizer {x} ∧ (∀ t ∈ T, t ^ 3 = 1) ∧
      Nat.card T = 81 := by
  have hP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simp [Nat.card_zpowers, hx])
  obtain ⟨T, hxT, hcard, hT⟩ := CFSG.RankThree.PartTwo.Sec14.Res9ON.exists_elemAbelian_le_ON e hP
  have hxmem : x ∈ T := hxT (Subgroup.mem_zpowers x)
  refine ⟨T, fun t ht => ?_, hT.2, hcard⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hT.1.is_comm.comm ⟨t, ht⟩ ⟨x, hxmem⟩)

theorem res3NoDatumON_holds :
    Res3NoDatumON := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  have hZ : Nat.card (Subgroup.center J) ≤ 3 :=
    Nat.le_of_dvd (by norm_num)
      (CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_ON hq
        hd.center_pGroup e)
  refine res3L125_false_of_rows hq (MulEquiv.refl (J ⧸ Subgroup.center J))
    (res3L125_isPGroup_two_outer_ON e) (fun x hx => Or.inr (Or.inl ?_)) hd
  obtain ⟨T, hTx, hT3, hTc⟩ := res3L125_exists_exponent_three_le_centralizer_ON e hx
  exact ⟨T, hTx, hT3, by omega⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
