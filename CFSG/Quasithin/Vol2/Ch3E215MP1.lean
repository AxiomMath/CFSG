module

public import CFSG.Quasithin.Vol2.Ch3E213MP1
public import CFSG.Quasithin.Vol2.Ch3E215ME
public import CFSG.Quasithin.Vol2.Ch3E215MF

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL projUpperTriangular)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

theorem pkgL2Paired215
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : PkgL2Paired215 := by
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
    -, hψB, -⟩ := hQRC
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
  ·
    obtain ⟨-, -, p, hp, hp2, ⟨eD⟩, -⟩ := hr1c (by omega)
    have hcardD : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
        (Ch3n.pairI V (g : G)⁻¹) = 2 * p ^ 1 := by
      rw [hcard, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, pow_one]
    have : Fact p.Prime := ⟨hp⟩
    have hpX : p ∣ Nat.card (Ch3n.pairI V (g : G)⁻¹) :=
      (Dvd.intro_left 2 (by rw [hcardD, pow_one])).trans (Subgroup.relIndex_dvd_card _ _)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpX
    exact ⟨relIndex_le_of_dihedral hpair hc2 hp hp2 le_rfl hcardD,
      e215DataOf_of_dihedral hpair hc2 hne hp hp2 le_rfl hcardD
        ⟨x, x.2, by rw [pow_one, Subgroup.orderOf_coe, hx]⟩⟩
  ·
    obtain ⟨m, hm2, -, -, k', _, hk', e, heB, -⟩ := hm hr
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    have hcardL : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
        (Ch3n.pairI V (g : G)⁻¹) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [hcard, Nat.card_congr e.toEquiv, card_projectiveSL_two_pow hk']
    have h9 : m = 3 → ∃ c ∈ Ch3n.pairI V (g : G)⁻¹, orderOf c = 9 := fun hm3 => by
      subst hm3
      obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
      obtain ⟨x, hx, hx9⟩ := exists_orderOf_nine_of_surjective hψs
        (c := e.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
      exact ⟨x, hIX ▸ hx, hx9⟩
    have hVM : V.subgroupOf H ≤ M.subgroupOf H :=
      hVMI.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
    have hker' : ψ.ker ≤ (M.subgroupOf H ⊓ (V.subgroupOf H ⊔
        CFSG.conjugate (V.subgroupOf H) g)).subgroupOf
          (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := fun x hx => by
      rw [hψk, hJ1] at hx
      exact Subgroup.mem_subgroupOf.2 (kerIn_le (Subgroup.mem_subgroupOf.1 hx))
    have hBor : ((M.subgroupOf H ⊓ (V.subgroupOf H ⊔
        CFSG.conjugate (V.subgroupOf H) g)).subgroupOf
          (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)).map (e.toMonoidHom.comp ψ) =
            projUpperTriangular 2 k' := by
      rw [← Subgroup.map_map, hψB, heB]
    obtain ⟨hBru, hidx⟩ := bruhat_of_qrc_psl2 hMH rfl hgI hVM ψ hψs hker' hk' e hBor
    rw [hIX] at hBru hidx
    exact ⟨relIndex_le_of_psl2 hpair hc2 hm2 hcardL h9,
      e215DataOf_of_psl2 hpair hc2 hm2 hcardL h9 hBru hidx⟩

end CFSG.Quasithin.Ch3E215M
