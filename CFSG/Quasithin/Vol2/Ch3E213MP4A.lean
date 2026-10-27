module

public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.H13.QRCBenderSection

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

namespace P4

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

theorem nonempty_equiv_star_of_case2 {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (h2 : Case2 H T M K) :
    Nonempty (↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) ≃*
      ↥(E2.star M H K)) := by
  rw [map_oddResidualPreimage_eq_of_case2 hS h2]
  exact nonempty_mulEquiv_star hS.hyp.minParabolic.maximal.1.le K

end P4

theorem pkgBenderL2Sz :
    ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
      Case2 H T M K → ∀ n : ℕ, 2 ≤ n →
      (IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) →
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V := by
  intro G _ _ H T M V K hS h2 n hn hBK _
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
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, ?_⟩
  rcases hK with ⟨-, hKL⟩ | hKS
  ·
    obtain ⟨k', _, hk', e, -⟩ := hlin hn hKL
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    refine relIndex_le_of_psl2 hpair hc2 (by omega : 2 ≤ m) ?_ fun hm3 => ?_
    · rw [hcard, Nat.card_congr e.toEquiv, card_projectiveSL_two_pow hk']
    · subst hm3
      obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
      obtain ⟨x, hx, hx9⟩ := P4.exists_orderOf_nine_of_surjective hψs
        (c := e.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
      exact ⟨x, hIX ▸ hx, hx9⟩
  ·
    obtain ⟨-, hm3, b, k', _, hmb, hk', e, -⟩ := hsz hKS
    have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
    refine relIndex_le_of_sz hpair hc2 hm3 ?_
    rw [hcard, Nat.card_congr e.toEquiv]
    subst hmb
    rw [CFSG.LieType.Ree.suzuki_order hk']
    ring

end CFSG.Quasithin.Ch3E213M
