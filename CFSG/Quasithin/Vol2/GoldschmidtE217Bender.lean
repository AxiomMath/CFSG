module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Lie
public import CFSG.Quasithin.Vol2.Ch3E213MP4C7
public import CFSG.Quasithin.Vol2.Ch3E213MP4A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F B6 E2 Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

namespace E217R1

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem false_of_benderU3
    (hS : Setting H T M V K)
    (h2 : Case2 H T M K) {n : ℕ} (hn : 2 ≤ n) (hU : IsPSU 3 2 n ↥(E2.star M H K))
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
  obtain ⟨T', hT', hP⟩ := P4C.pair_of_u3 hS h2 hn hU
  exact false_of_pair hS hT' hP hV16 hq

theorem false_of_benderL2Sz
    (hS : Setting H T M V K)
    (h2 : Case2 H T M K) {n : ℕ} (hn : 2 ≤ n)
    (hBK : IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
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
  obtain ⟨eK⟩ := P4.nonempty_equiv_star_of_case2 hS h2
  obtain ⟨k, _, _, hk, hK⟩ : ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
      ((2 ≤ n ∧ Nonempty (↥((oddResidualPreimage H).map
          (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) ≃* projectiveSL 2 k)) ∨
        ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (↥((oddResidualPreimage H).map
          (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) ≃* CFSG.Blueprint.suzukiGroup a k)) := by
    rcases hBK with hL | hSz
    · obtain ⟨k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_projectiveSL_of_isPSL hL
      exact ⟨k, inferInstance, inferInstance, hk, Or.inl ⟨hn, ⟨eK.trans θ⟩⟩⟩
    · obtain ⟨a, ha, hna, k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_suzukiGroup_of_isSz hSz
      exact ⟨k, inferInstance, inferInstance, hk, Or.inr ⟨a, ha, hna, ⟨eK.trans θ⟩⟩⟩
  have hQRC := H13.QRC.qrc_single_Bender_section_produces_original_higher_image_pair
    hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQ' hk hK
  obtain ⟨-, -, m, L, g, hm1, -, -, hgI, -, hVI, -, -, -, -, -, -, -, -, -, hsyl, hNI, hMI, hJ1,
    -, -, -, hcharI, ψ, hψs, hψk, -, -, -, -, -, -, hlin, hsz⟩ := hQRC
  rw [hT'] at hsyl hMI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hMI]
    exact le_inf (hT' ▸ hVT') le_sup_left
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
    rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, P4.card_quotient_pCore_eq hψs hψk']
  have hXH := pairI_le hVH (H.inv_mem g.2)
  rcases hK with ⟨-, hKL⟩ | hKS
  · obtain ⟨k', _, hk', e, -⟩ := hlin hn hKL
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    have hcard' : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
        (Ch3n.pairI V (g : G)⁻¹) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [hcard, Nat.card_congr e.toEquiv, card_projectiveSL_two_pow hk']
    have hstar := relIndex_le_of_psl2 hpair hc2 (by omega : 2 ≤ m) hcard' fun hm3 => by
      subst hm3
      obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
      obtain ⟨x, hx, hx9⟩ := P4.exists_orderOf_nine_of_surjective hψs
        (c := e.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
      exact ⟨x, hIX ▸ hx, hx9⟩
    refine false_of_member hS.hyp.elem hpair hc2 hne hXH hV16 hq hstar ?_
    rw [hcard']
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega : 2 ≤ m) : 2 ^ 2 ∣ 2 ^ m) _
  · obtain ⟨-, hm3, b, k', _, hmb, hk', e, -⟩ := hsz hKS
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    have hcard' : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
        (Ch3n.pairI V (g : G)⁻¹) = (2 ^ m) ^ 2 * (((2 ^ m) ^ 2 + 1) * (2 ^ m - 1)) := by
      rw [hcard, Nat.card_congr e.toEquiv]
      subst hmb
      rw [CFSG.LieType.Ree.suzuki_order hk']
      ring
    have hstar := relIndex_le_of_sz hpair hc2 hm3 hcard'
    refine false_of_member hS.hyp.elem hpair hc2 hne hXH hV16 hq hstar ?_
    rw [hcard']
    have h4' : 2 ^ 2 ∣ (2 ^ m) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact Dvd.dvd.mul_right h4' _

end E217R1

end CFSG.Quasithin
