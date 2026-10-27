module

public import CFSG.Quasithin.Vol2.Ch3E213MSL2Pair
public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.Vol2.Ch3E213MFam

public section

namespace CFSG.Quasithin.Ch3E213M.SL2Pair

open CFSG.Open CFSG.QuasithinUnique B6

theorem card_quotient_pCore_eq {I L : Type*} [Group I] [Group L] {ψ : I →* L}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = CFSG.pCore 2 I) :
    Nat.card (I ⧸ CFSG.pCore 2 I) = Nat.card L :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).toEquiv

theorem exists_orderOf_nine_of_surjective {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {I : Subgroup H} {L : Type*} [Group L] {ψ : I →* L} (hψ : Function.Surjective ψ) {c : L}
    (hc : orderOf c = 9) : ∃ x ∈ I.map H.subtype, orderOf x = 9 := by
  obtain ⟨y, rfl⟩ := hψ c
  have hdvd : 9 ∣ orderOf y := hc ▸ orderOf_map_dvd ψ y
  have hz : orderOf (y ^ (orderOf y / 9)) = 9 := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  refine ⟨((y ^ (orderOf y / 9) : I) : H), ⟨_, (y ^ (orderOf y / 9)).2, rfl⟩, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem e213Concl_of_pair {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) {T' : Sylow 2 ↥H} (hT' : (T' : Subgroup H) = T.subgroupOf H)
    (hP : Pair T' (M.subgroupOf H) (V.subgroupOf H)) : E213Concl H T M V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨m, g, hm, hgI, hVI, hsyl, hNI, hMI, hJ1, hcharI, L, ψ, hψs, hψk, k', _, hk', eL, -⟩ :=
    hP
  rw [hT'] at hsyl hMI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hMI]
    exact le_inf (fun x hx => hS.hyp.le_T hx) le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hsyl (fun x hx => (hNI ⟨hx.2, hx.1⟩).1) hVMI hJ1
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψk, hJ1, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = Nat.card L := by
    rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, card_quotient_pCore_eq hψs hψk']
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, ?_⟩
  have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
  refine relIndex_le_of_psl2 hpair hc2 hm ?_ fun hm3 => ?_
  · rw [hcard, Nat.card_congr eL.toEquiv, card_projectiveSL_two_pow hk']
  · subst hm3
    obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
    obtain ⟨x, hx, hx9⟩ := exists_orderOf_nine_of_surjective hψs
      (c := eL.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
    exact ⟨x, hIX ▸ hx, hx9⟩

end CFSG.Quasithin.Ch3E213M.SL2Pair
