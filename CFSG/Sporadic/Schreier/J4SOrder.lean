
module

public import CFSG.Sporadic.Schreier.J4SOrderBase1

public import CFSG.Sporadic.Schreier.J4SOrbitCheck
public import CFSG.Sporadic.Schreier.J4SChain
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem stabilizer_v_eq_Hj : MulAction.stabilizer J v = Hj := by
  have hv : v = toRow Native.rootV.toVec := by rw [v, toVecD_rootBits]
  ext g
  rw [MulAction.mem_stabilizer_iff, hv]
  exact ⟨fun h => j4Facts.stab g h, fun h => Hj_fix_root j4Facts.mat g h⟩

theorem card_H_le :
    Nat.card H ≤ 501397585920 := by
  rw [← card_Hj j4Facts, ← stabilizer_v_eq_Hj]
  exact Subgroup.card_le_of_le H_le_stabilizer_v

theorem counting :

    Nat.card ρH.ker = 2 ^ 11 ∧ ρH.range = P ∧ Nat.card P = 244823040 := by
  have hk : 2 ^ 11 ≤ Nat.card ρH.ker := by
    rw [← card_N, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_H).toEquiv]
    exact Subgroup.card_le_of_le N_le_ker_ρH
  have hr : Nat.card P ≤ Nat.card ρH.range := Subgroup.card_le_of_le P_le_range_ρH
  have hp := card_P_ge
  have hH := card_H_le
  rw [← card_ker_mul_card_range ρH] at hH
  have hpos : 0 < Nat.card ρH.range := Nat.card_pos
  have e1 : Nat.card ρH.ker = 2 ^ 11 := by
    by_contra hne
    have : 2 ^ 11 + 1 ≤ Nat.card ρH.ker := by omega
    have := Nat.mul_le_mul this (hp.trans hr)
    omega
  rw [e1] at hH
  have e2 : Nat.card ρH.range = 244823040 := by omega
  have e3 : Nat.card P = 244823040 := by omega
  refine ⟨e1, ?_, e3⟩
  exact (Subgroup.eq_of_le_of_card_ge P_le_range_ρH (by rw [e2, e3])).symm

theorem ker_ρH :
    ρH.ker = N.subgroupOf H := by
  refine (Subgroup.eq_of_le_of_card_ge N_le_ker_ρH ?_).symm
  rw [counting.1, ← card_N, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_H).toEquiv]

theorem ρK_injective :
    Function.Injective ρK := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker, ρK_eq] at hk
  have h1 : Subgroup.inclusion K_le_H k ∈ N.subgroupOf H := by rw [← ker_ρH]; exact hk
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (k : J) ∈ K ⊓ N := ⟨k.2, h1⟩
  rw [K_inf_N, Subgroup.mem_bot] at h2
  exact (Subgroup.mem_bot).2 (Subtype.ext h2)

theorem card_K :
    Nat.card K = 244823040 := by
  rw [← counting.2.2, ← Nat.card_congr (MonoidHom.ofInjective ρK_injective).toEquiv]

theorem card_H :
    Nat.card H = 501397585920 := by
  rw [← card_ker_mul_card_range ρH, counting.1, counting.2.1, counting.2.2]
  norm_num

theorem exists_mul_of_mem_H
    {h : J} (hh : h ∈ H) : ∃ n ∈ N, ∃ k ∈ K, h = n * k := by
  obtain ⟨k, hk⟩ : ρH ⟨h, hh⟩ ∈ P := counting.2.1 ▸ ⟨⟨h, hh⟩, rfl⟩
  rw [ρK_eq] at hk
  have hker : ⟨h, hh⟩ * (Subgroup.inclusion K_le_H k)⁻¹ ∈ ρH.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, mul_inv_cancel]
  rw [ker_ρH, Subgroup.mem_subgroupOf] at hker
  refine ⟨h * (k : J)⁻¹, hker, k, k.2, ?_⟩
  rw [inv_mul_cancel_right]

theorem N_sup_K :
    N ⊔ K = H := by
  refine le_antisymm (sup_le N_le_H K_le_H) fun h hh => ?_
  obtain ⟨n, hn, k, hk, rfl⟩ := exists_mul_of_mem_H hh
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hk)

end CFSG.Sporadic.J4Schreier
