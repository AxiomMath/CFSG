module

public import CFSG.Quasithin.Vol2.GoldschmidtRes2WPsl2
public import CFSG.Quasithin.Vol2.Ch3E215MF

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem e215ConclW_of_pair {H T M V K : Subgroup G} (hS : Ch3E213M.Setting H T M V K)
    {T' : Sylow 2 ↥H} (hT' : (T' : Subgroup H) = T.subgroupOf H)
    (hP : Ch3E213M.SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H)) : E215ConclW H T M V := by
  intro hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨m, g, hm, hgI, hVI, hsyl, hNI, hMI, hJ1, hcharI, L, ψ, hψs, hψk, k', _, hk', eL,
    hBor⟩ := hP
  rw [hT'] at hsyl hMI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hMI]
    exact le_inf (fun x hx => hS.hyp.le_T hx) le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := Ch3E213M.pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hsyl (fun x hx => (hNI ⟨hx.2, hx.1⟩).1) hVMI hJ1
  obtain ⟨hc2, hne⟩ := Ch3E213M.charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψk, hJ1, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [hker, ← hIX, Ch3E213M.relIndex_pCoreOf_map_subtype,
      Ch3E213M.SL2Pair.card_quotient_pCore_eq hψs hψk', Nat.card_congr eL.toEquiv,
      Ch3E213M.card_projectiveSL_two_pow hk']
  have h9 : m = 3 → ∃ c ∈ Ch3n.pairI V (g : G)⁻¹, orderOf c = 9 := fun hm3 => by
    subst hm3
    obtain ⟨c, hc9⟩ := Ch3E213M.exists_orderOf_nine_projectiveSL hk'
    obtain ⟨x, hx, hx9⟩ := Ch3E213M.SL2Pair.exists_orderOf_nine_of_surjective hψs
      (c := eL.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
    exact ⟨x, hIX ▸ hx, hx9⟩
  have hVM : V.subgroupOf H ≤ M.subgroupOf H :=
    hVMI.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hker' : ψ.ker ≤ (M.subgroupOf H ⊓ (V.subgroupOf H ⊔
      CFSG.conjugate (V.subgroupOf H) g)).subgroupOf
        (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := fun x hx => by
    rw [hψk] at hx
    exact Subgroup.mem_subgroupOf.2 (kerIn_le (Subgroup.mem_subgroupOf.1 hx))
  obtain ⟨hBru, hidx⟩ := Ch3E215M.bruhat_of_qrc_psl2 hMH rfl hgI hVM ψ hψs hker' hk' eL hBor
  rw [hIX] at hBru hidx
  have hJ2 : IsPGroup 2 ↥(kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)) := by
    rw [hker]
    exact pCoreOf_isPGroup 2 _
  exact ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne,
    Ch3E213M.relIndex_le_of_psl2 hpair hc2 hm hcard h9,
    e215DataW_of_psl2 hpair hc2 hm hcard h9 hBru hidx hJ2
      (relIndex_le_four hpair hc2 hne inf_le_left hb)⟩

end CFSG.Quasithin.Res2
