
module

public import CFSG.Monster.B.TwoA.Base.Par45ABase
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.SevenPairCBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem natCard_zpowers_xhat : Nat.card (Subgroup.zpowers xhat) = 2 ^ 1 :=
  (Nat.card_zpowers xhat).trans (orderOf_xhat.trans (pow_one 2).symm)

theorem natCard_Vhat_pow : Nat.card Vhat = 2 ^ 2 :=
  isKleinFour_Vhat.card_four.trans (by norm_num)

theorem lt_of_le_of_natCard_eq {H K : Subgroup Dfull} (hle : H ≤ K) {a b : ℕ}
    (ha : Nat.card H = a) (hb : Nat.card K = b) (hab : a < b) : H < K :=
  lt_of_le_of_natCard_lt hle (by rw [ha, hb]; exact hab)

theorem zpowers_xhat_lt_Vhat : Subgroup.zpowers xhat < Vhat :=
  lt_of_le_of_natCard_eq (Subgroup.zpowers_le.2 xhat_mem_Vhat) natCard_zpowers_xhat
    natCard_Vhat_pow (by norm_num)

theorem Vhat_lt_E3 :
    Vhat < E3 :=
  lt_of_le_of_natCard_eq Vhat_le_E3 natCard_Vhat_pow natCard_E3_pow (by norm_num)

theorem normalizer_zpowers_xhat :
    Subgroup.normalizer (Subgroup.zpowers xhat : Set Dfull) = Jhat := by
  apply le_antisymm
  · intro g hg
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * xhat * g⁻¹ ∈ Subgroup.zpowers xhat :=
      conj_mem_of_normalizer hg (Subgroup.mem_zpowers _)
    rcases (CFSG.Monster.B.Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xhat).1 h1 with
      h | h
    · rw [mul_inv_eq_one] at h
      exact absurd (mul_left_cancel (h.trans (mul_one g).symm)) xhat_ne_one
    · rw [mul_inv_eq_iff_eq_mul] at h
      exact h
  · intro g hg
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff] at hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [(Commute.zpow_right (show Commute g xhat from hg) k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _

instance isElementaryAbelian_Vhat :
    CFSG.IsElementaryAbelian 2 Vhat where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
    (EU_comm qV_Uplane (E3_eq_EU ▸ Vhat_le_E3 a.2) (E3_eq_EU ▸ Vhat_le_E3 b.2))⟩⟩
  exponent_dvd_p := dvd_of_eq isKleinFour_Vhat.exponent_two

theorem natCard_mulAut_Vhat : Nat.card (MulAut Vhat) = 6 := by
  rw [Nat.card_congr (mulAutEquivGL natCard_Vhat_pow).toEquiv, natCard_GL_two]

theorem conjE_Vhat_surjective :
    Function.Surjective (conjE Vhat) := by
  refine conjE_surjective_of_card ?_
  change Nat.card Ntwo = Nat.card (MulAut Vhat) * Nat.card Ctwo
  rw [natCard_Ntwo, natCard_mulAut_Vhat, natCard_Ctwo]

@[expose] def Echain : ℕ → Subgroup Dfull
  | 1 => Subgroup.zpowers xhat
  | 2 => Vhat
  | 3 => E3
  | 4 => E4
  | 5 => E5
  | _ => ⊥

abbrev Kchain (i : ℕ) : Subgroup Dfull := Subgroup.normalizer (Echain i : Set Dfull)

theorem Kchain_one : Kchain 1 = Jhat := normalizer_zpowers_xhat

theorem Kchain_two : Kchain 2 = Ntwo := rfl

theorem natCard_subspaceDim_fin {i j : ℕ} (hji : j ≤ i) :
    Nat.card (SubspaceDim (ZMod 2) (Fin i → ZMod 2) j) = qBinom 2 i j := by
  rw [card_subspaces (by rw [Module.finrank_fin_fun]; exact hji), ZMod.card,
    Module.finrank_fin_fun]

theorem qBinom_values :
    [qBinom 2 2 1, qBinom 2 3 1, qBinom 2 3 2, qBinom 2 4 1, qBinom 2 4 2, qBinom 2 4 3,
      qBinom 2 5 1, qBinom 2 5 2, qBinom 2 5 3, qBinom 2 5 4] =
      [3, 7, 7, 15, 35, 15, 31, 155, 155, 31] := by
  decide

end CFSG.Monster.B.TwoA
