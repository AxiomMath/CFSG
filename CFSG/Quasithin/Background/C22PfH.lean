module

public import CFSG.Quasithin.Background.C22PfG
public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.Chevalley

namespace C22Pf

theorem radicalParabolicU33_holds :
    RadicalParabolicU33 := by
  intro X _ _ hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨eA⟩ := SmithC27.nonempty_quasithinG2_mulEquiv_adjointGroup_two hF
  have hH : Holds ↥(quasithinG2 (ZMod 2)) 2 :=
    (holds_adjointGroup_tag .G2 (ZMod 2) 2).of_mulEquiv eA.symm
  have hD : IsPSU 3 3 1 ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
    SmithC27.isPSU_of_equiv_g2Derived hF (MulEquiv.refl _)
  obtain ⟨eD⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hD
  obtain ⟨eX⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hX
  have hcardΓ : Nat.card ↥(quasithinG2 (ZMod 2)) = 12096 := by
    rw [SmithC27.card_quasithinG2' (n := 1) (by rw [hF, pow_one]), hF]
    norm_num
  have hcardC : Nat.card (commutator ↥(quasithinG2 (ZMod 2))) = 6048 := by
    rw [← Nat.card_congr (commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).toEquiv]
    exact SBc11.card_of_isPSU_three_three hD
  have hq : IsPGroup 2 (↥(quasithinG2 (ZMod 2)) ⧸ commutator ↥(quasithinG2 (ZMod 2))) := by
    refine IsPGroup.of_card (n := 1) ?_
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (commutator ↥(quasithinG2 (ZMod 2)))
    rw [hcardΓ, hcardC] at h
    rw [pow_one]
    omega
  have hT : HoldsTits (commutator ↥(quasithinG2 (ZMod 2))) 2 :=
    holdsTits_of_normal_of_isPGroup_quotient hq hH
  have hTX : HoldsTits X 2 :=
    hT.of_mulEquiv ((commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).symm.trans
      (eD.trans eX.symm))
  obtain ⟨eU⟩ := u33Pres_mulEquiv_PSU3
  have hNU : Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G) ≤ u33SylowT := by
    rw [coe_u33SylowT, u33Extra.normalizer_T]
  exact SmithC27.isRadicalParabolic_top_of_holds (holds_of_holdsTits hTX
    (normalizer_le_of_mulEquiv (eX.trans eU.symm) u33SylowT hNU))

end C22Pf

end CFSG.Quasithin
