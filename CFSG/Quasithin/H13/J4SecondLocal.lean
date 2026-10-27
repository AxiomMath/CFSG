module

public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.J4Image

public noncomputable section

namespace CFSG.Quasithin.H13.J4

theorem ker_rho_eq_and_card_range
    :
    rho.ker = P.subgroupOf W ∧ Nat.card rho.range = 2661120 := by
  have hPW : Nat.card (P.subgroupOf W) = 8192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_W).toEquiv, card_P]
    norm_num
  have hW : Nat.card rho.ker * Nat.card rho.range = 21799895040 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup, card_W]
  have hk : 8192 ≤ Nat.card rho.ker := hPW ▸ Subgroup.card_le_of_le P_le_ker_rho
  have hr := le_card_range_rho
  have hk' : Nat.card rho.ker = 8192 := by
    refine le_antisymm ?_ hk
    have h1 : Nat.card rho.ker * 2661120 ≤ 8192 * 2661120 := by
      calc Nat.card rho.ker * 2661120 ≤ Nat.card rho.ker * Nat.card rho.range :=
            Nat.mul_le_mul_left _ hr
        _ = 8192 * 2661120 := by rw [hW]
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  refine ⟨?_, ?_⟩
  · exact (Subgroup.eq_of_le_of_card_ge P_le_ker_rho (by rw [hk', hPW])).symm
  · rw [hk'] at hW
    omega

instance P_normal
    : (P.subgroupOf W).Normal :=
  ker_rho_eq_and_card_range.1 ▸ rho.normal_ker

theorem secondLocal_extraspecial :
    (Subgroup.center P).map P.subtype = Subgroup.zpowers t ∧
      (commutator P).map P.subtype = Subgroup.zpowers t ∧
      (frattini P).map P.subtype = Subgroup.zpowers t ∧
      IsExtraspecialPGroup 2 P ∧ Nat.card P = 2 ^ 13 := by
  have hE := isExtraspecialPGroup_P
  refine ⟨map_center_P, ?_, ?_, hE, card_P⟩
  · rw [hE.2.1, map_center_P]
  · rw [hE.2.2.1, map_center_P]

end CFSG.Quasithin.H13.J4
