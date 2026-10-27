module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Mem
public import CFSG.Quasithin.Vol2.Ch3E213MSL2PairE
public import CFSG.Quasithin.Vol2.Ch3E213MP5L
public import CFSG.Quasithin.Vol2.Ch3E213MP6AC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F B6 E2 Ch3E213M

namespace E217R1

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

omit [Finite G] in
theorem pairI_le {g : G} (hVH : V ≤ H) (hg : g ∈ H) : Ch3n.pairI V g ≤ H := by
  refine sup_le hVH fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := hw
  exact H.mul_mem (H.mul_mem hg (hVH hv)) (H.inv_mem hg)

theorem false_of_pair (hS : Setting H T M V K) {T' : Sylow 2 ↥H}
    (hT' : (T' : Subgroup H) = T.subgroupOf H)
    (hP : SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H)) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
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
  have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, SL2Pair.card_quotient_pCore_eq hψs hψk',
      Nat.card_congr eL.toEquiv, card_projectiveSL_two_pow hk']
  have hstar := relIndex_le_of_psl2 hpair hc2 hm hcard fun hm3 => by
    subst hm3
    obtain ⟨c, hc9⟩ := exists_orderOf_nine_projectiveSL hk'
    obtain ⟨x, hx, hx9⟩ := SL2Pair.exists_orderOf_nine_of_surjective hψs
      (c := eL.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
    exact ⟨x, hIX ▸ hx, hx9⟩
  have h4 : 4 ∣ (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) := by
    rw [hcard]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 hm : 2 ^ 2 ∣ 2 ^ m) _
  exact false_of_member hS.hyp.elem hpair hc2 hne (pairI_le hVH (H.inv_mem g.2)) hV16 hq hstar h4

theorem false_of_sp4Member {g : G} {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
    (hel : IsElemAbelian 2 V) (hV16 : Nat.card V = 2 ^ 4) (hVH : V ≤ H)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hel H))
    (h : Sp4Member H T M V g F₀) : False := by
  obtain ⟨hg, hpair, hc2, hne, -, ⟨ψ, hψs, hψk⟩, hVB⟩ := h
  obtain ⟨e, he1, hq'⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_card_eq_two_pow (K := F₀)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) =
      Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp F₀) := by
    rw [Subgroup.relIndex, Subgroup.index, ← hψk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv
  have hcard' : (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) =
      (2 ^ e) ^ 4 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1)) := by
    rw [hcard, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.card_antiSp hq']
  have hstar := relIndex_le_of_sp4 hpair hc2 he1 (by
      rw [hcard']
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
      have h4 : (2 ^ e) ^ 4 - 1 = ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 2 + 1) := by
        have h1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        zify [h1, Nat.one_le_pow 4 (2 ^ e) (by positivity)]
        ring
      rw [h4]
      exact Dvd.intro_left _ rfl) (by
      calc (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤ Nat.card F₀ ^ 2 := hVB
        _ = 2 ^ (2 * e) := by rw [hq', ← pow_mul, mul_comm])
  have h4 : 4 ∣ (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) := by
    rw [hcard']
    refine Dvd.dvd.mul_right ?_ _
    have : 2 ^ 2 ∣ (2 ^ e) ^ 4 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact this
  exact false_of_member hel hpair hc2 hne (pairI_le hVH hg) hV16 hq hstar h4


theorem false_of_l3
    (hS : Setting H T M V K)
    (h2 : Case2 H T M K) {n : ℕ} (hn : 1 ≤ n) (hPSL : IsPSL 3 2 n ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
  obtain ⟨T', hT', hP⟩ := pair_of_l3 hS h2 hn hPSL hD hB
  exact false_of_pair hS hT' hP hV16 hq

end E217R1

end CFSG.Quasithin
