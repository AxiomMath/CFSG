module

public import CFSG.Quasithin.Vol2.Ch3E215ME

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6

theorem e215Concl_of_relIndex_eq_two {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}
    (hyp : E2.Hyp28 H T M V) (hchar : CharTwo H) (h2 : (V ⊓ pCoreOf 2 H).relIndex V = 2) :
    E215Concl H T M V := by
  have hmp := hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hyp.le_H
  obtain ⟨T', hT', hcharH, -, hTM', -, -, hel, hVT', hTV', hVM', -⟩ :=
    Ch3E213M.qrcHyp_of_hyp28 hyp hchar
  have := hel
  obtain ⟨p, a, hp, hp2, ha, g, I, hI, hVI, hgI, -, -, hcharI, hsyl, hMI, hNI, hVMI, hJ, -, ⟨eD⟩,
    -⟩ := SteinbergBS.qrc_order_two_original_core_image_produces_dihedral_pair hcharH T' hTM' hVT'
      hTV' hVM' ((Ch3E213M.relIndex_subgroupOf_inf_pCore hVH).trans h2)
  rw [hT'] at hsyl hMI hNI
  obtain ⟨hIX, hpair, hker⟩ := Ch3E213M.pair_of_qrc hTH hMH hyp.le_T hyp.normal_T hyp.elem hI hgI
    hsyl (by rw [hNI, ← hMI]; exact inf_le_left) hVMI hJ
  obtain ⟨hc2, hne⟩ := Ch3E213M.charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = 2 * p ^ a := by
    rw [hker, ← hIX, Ch3E213M.relIndex_pCoreOf_map_subtype, Nat.card_congr eD.toEquiv,
      DihedralGroup.nat_card]
  have hc : ∃ c ∈ Ch3n.pairI V (g : G)⁻¹, orderOf c = p ^ a := by
    obtain ⟨x, hx, hxo⟩ := exists_orderOf_of_surjective
      (ψ := eD.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 I)))
      (eD.surjective.comp (QuotientGroup.mk'_surjective _)) (c := DihedralGroup.r 1)
      DihedralGroup.orderOf_r_one
    exact ⟨x, hIX ▸ hx, hxo⟩
  exact ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne,
    Ch3E213M.relIndex_le_of_dihedral hpair hc2 hp hp2 ha hcard,
    e215DataOf_of_dihedral hpair hc2 hne hp hp2 ha hcard hc⟩

end CFSG.Quasithin.Ch3E215M
