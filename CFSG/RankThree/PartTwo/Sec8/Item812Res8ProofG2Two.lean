module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.FFC2G2
public import CFSG.Quasithin.Recognition.CertU33Simple

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley

namespace Item812Res8

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.QuasithinUnique.Bridge.Alt57Model CFSG.Open in
theorem nonempty_commutator_g2_two_equiv
    {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) :
    Nonempty (↥⁅H, H⁆ ≃* U33G) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := CFSG.Quasithin.nonempty_commutator_equiv e
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  exact ⟨(((f1.trans f2).trans f3).trans u33EquivSubG2.symm)⟩

open CFSG.Quasithin in
theorem twoLocalThree_u33 :
    TwoLocalThree U33G := by
  have hs : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have h3 : 3 ∣ Nat.card U33G := by rw [card_u33Pres]; norm_num
  have hZ : Subgroup.center U33G = ⊥ := by
    rcases (Subgroup.center U33G).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := u33Pres_nonabelian
      have hu : u ∈ Subgroup.center U33G := by rw [h]; exact Subgroup.mem_top u
      exact huv ((Subgroup.mem_center_iff.mp hu v).symm)
  have hx1 : u33Data.x ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := u33Extra.xN
    exact hi i (by rw [h]; group)
  refine ⟨noThetaNormal_of_isSimpleGroup h3, u33Data.x, u33Extra.PA, u33Data.hx, ?_,
    u33Extra.PA_ne, u33Extra.PA_p, u33Extra.PA_norm u33Data.x_mem_A⟩
  rw [hZ, Subgroup.mem_bot]
  exact hx1

end Item812Res8


open Item812Res8 in
theorem kF89G2TwoTwoLocal_holds :
    KF89G2TwoTwoLocal := by
  intro k _ _ hk
  set H := adjointGroup .G2 k
  obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hk
  obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hk (Subgroup.topEquiv.trans E)
  obtain ⟨F⟩ := nonempty_commutator_g2_two_equiv hk (Subgroup.topEquiv.trans E)
  have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
    Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
  have heq : perfectResidual H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
    le_antisymm (perfectResidual_le_commutator H)
      (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
  exact TwoLocalThree.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans F) twoLocalThree_u33

end CFSG.RankThree.PartTwo.Sec8
