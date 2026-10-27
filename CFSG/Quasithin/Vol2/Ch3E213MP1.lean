module

public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.H13.QRCPairedSection

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

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

theorem pkgL2Paired
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : PkgL2Paired := by
  intro G _ _ H T M V K hS h1 n hn hPSL hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_projectiveSL_of_isPSL hPSL
  obtain ⟨K₁, K₂, hK, hc, hd, ⟨φ₁⟩, ⟨φ₂⟩⟩ := exists_paired_of_case1 h38 hS h1
  have hQRC :=
    H13.QRC.qrc_paired_even_linear_sections_produce_original_pair_with_full_second_projection_core
      hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQ' hk hn hK hc hd
      ⟨φ₁.trans θ⟩ ⟨φ₂.trans θ⟩
  obtain ⟨-, R, θ₁, θ₂, -, -, -, -, -, -, -, -, r, hr1, -, -, L₁, g, -, -, -, hgI, -, hVI, -, -,
    -, hm, hr1c, -, -, -, -, -, -, hsyl, -, -, hJ1, hJ2, -, -, -, hcharI, hMI, hNI, ψ, hψs, hψk,
    -⟩ := hQRC
  rw [hT'] at hsyl hMI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hMI]
    exact le_inf (hT' ▸ hVT') le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hsyl (fun x hx => (hNI ⟨hx.2, hx.1⟩).1) hVMI (hJ1.symm.trans hJ2)
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψk, hJ2, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = Nat.card L₁ := by
    rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, card_quotient_pCore_eq hψs hψk']
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, ?_⟩
  rcases Nat.lt_or_ge r 2 with hr | hr
  · obtain ⟨-, -, p, hp, hp2, ⟨eD⟩, -⟩ := hr1c (by omega)
    refine relIndex_le_of_dihedral hpair hc2 hp hp2 (a := 1) le_rfl ?_
    rw [hcard, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, pow_one]
  · obtain ⟨m, hm2, -, -, k', _, hk', e, -⟩ := hm hr
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    refine relIndex_le_of_psl2 hpair hc2 hm2 ?_ fun hm3 => ?_
    · rw [hcard, Nat.card_congr e.toEquiv, card_projectiveSL_two_pow hk']
    · subst hm3
      obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
      obtain ⟨x, hx, hx9⟩ := exists_orderOf_nine_of_surjective hψs
        (c := e.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
      exact ⟨x, hIX ▸ hx, hx9⟩

end CFSG.Quasithin.Ch3E213M
