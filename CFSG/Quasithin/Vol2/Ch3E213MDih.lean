module

public import CFSG.Quasithin.Vol2.Ch3E213MTr
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.SteinbergBSDihedralPair

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6

theorem e213Member_of_relIndex_eq_two {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}
    (hyp : E2.Hyp28 H T M V) (hchar : CharTwo H) (h2 : (V ⊓ pCoreOf 2 H).relIndex V = 2) :
    ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
      CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
      (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤
        (V ⊓ conjSub g V).relIndex (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V) := by
  have hmp := hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hyp.le_H
  obtain ⟨T', hT', hcharH, -, hTM', -, -, hel, hVT', hTV', hVM', -⟩ := qrcHyp_of_hyp28 hyp hchar
  have := hel
  obtain ⟨p, a, hp, hp2, ha, g, I, hI, hVI, hgI, -, -, hcharI, hsyl, hMI, hNI, hVMI, hJ, -, ⟨eD⟩,
    -⟩ := SteinbergBS.qrc_order_two_original_core_image_produces_dihedral_pair hcharH T' hTM' hVT'
      hTV' hVM' ((relIndex_subgroupOf_inf_pCore hVH).trans h2)
  rw [hT'] at hsyl hMI hNI
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc hTH hMH hyp.le_T hyp.normal_T hyp.elem hI hgI hsyl
    (by rw [hNI, ← hMI]; exact inf_le_left) hVMI hJ
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, relIndex_le_of_dihedral hpair hc2 hp hp2 ha ?_⟩
  rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]

end CFSG.Quasithin.Ch3E213M
