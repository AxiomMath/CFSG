module

public import CFSG.Quasithin.Background.SmithC27AltK1
public import CFSG.Quasithin.Background.SmithC27AltK3
public import CFSG.Quasithin.Background.SmithC27Exc
public import CFSG.Quasithin.Vol2.Ch3B513NAltB
public import CFSG.Quasithin.Background.C124BlkL2
public import CFSG.Quasithin.Background.C124BlkA7
public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm
public import CFSG.Quasithin.Background.C124AsmClassify

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm C124 C124.YZ

section Degree

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

omit [Finite G] in
theorem nonempty_quotEquiv_of_isAltType {m : ℕ} (htype : IsAltType K m) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin m)) := by
  obtain ⟨α, hα, hker, -⟩ := htype
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

theorem five_or_seven_of_isAltType (h : Hyp27 H R M K) {m : ℕ} (hm : Odd m)
    (htype : IsAltType K m) : m = 5 ∨ m = 7 := by
  obtain ⟨e⟩ := nonempty_quotEquiv_of_isAltType htype
  have hq := h.quasi
  by_cases hsmall : m ≤ 3
  · exfalso
    have hcomm : ∀ a b : alternatingGroup (Fin m), a * b = b * a := by
      obtain ⟨j, rfl⟩ := hm
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> decide
    have hQcomm : ∀ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b = b * a := fun a b =>
      e.injective (by rw [map_mul, map_mul, hcomm])
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hQcomm])
  by_cases hbig : 9 ≤ m
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hsq : IsSQTKIn K := h.hyp.sqtk.mono h.K_le
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 2 :=
      sqt_iff.mp hsq.1 3 Nat.prime_three (by norm_num)
    have h2 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥K) := by
      have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hp
      rw [ha]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have h3 := SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥K) h2
    have h4 := SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have h5 := AGLEmbeddingD2.three_le_pRank_alternatingGroup Nat.prime_three (by norm_num)
      (show 3 * 3 ≤ m by omega)
    omega
  · rcases hm with ⟨j, rfl⟩
    omega

end Degree

section Fix

variable {G : Type} [Group G] [Finite G]

theorem fix_eq_one_of_realizes {V L : Subgroup G} (hV : IsElemAbelian 2 V) {n : ℕ}
    (hn : n = 5 ∨ n = 7) {π : ↥(alternatingGroup (Fin n)) →* ↥(autI hV L)}
    (hr : (FFModel.altDn n).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π)
    (hirr : commV (autI hV L) ∈ IrrPlus (autI hV L) ⊤) :
    ∀ u ∈ commV (autI hV L), u ∈ fixV (autI hV L) → u = 1 := by
  intro u hu hfix
  obtain ⟨p, E⟩ := B513N.extBot_of_realizes (fun w => IntMod.sq_eq_one w) hr
  have hA : (fixV (autI hV L) ⊓ commV (autI hV L)).subgroupOf (commV (autI hV L)) ≤
      B3.commG (B513N.actU π) := by
    rw [B513N.commG_actU_eq_top hr.1 hirr.2.2.1]
    exact le_top
  have h0 := B3.eq_bot_of_zeroClass (by rcases hn with rfl | rfl <;> norm_num) E hA
    (B3.H1_natural_odd hn)
  have hmem : (⟨u, hu⟩ : ↥(commV (autI hV L))) ∈
      (fixV (autI hV L) ⊓ commV (autI hV L)).subgroupOf (commV (autI hV L)) :=
    Subgroup.mem_subgroupOf.2 ⟨hfix, hu⟩
  rw [h0, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Fix

section Excl

variable {G : Type} [Group G]

theorem card_evenWeight_seven : Nat.card (evenWeight 7) = 64 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 7 → ZMod 2 =>
    (show x ∈ evenWeight 7 ↔ ∑ i, x i = 0 from Iff.rfl)))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem index_blockZ_of_isAltType {K : Subgroup G} {m : ℕ} (htype : IsAltType K m) :
    ((blockZ K).subgroupOf (blockU K)).index = Nat.card (evenWeight m) := by
  obtain ⟨-, -, -, β, hβs, hβk, -⟩ := htype
  rw [← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hβs, Subgroup.card_top]
  rfl

theorem not_isExcA7Block_of_isAltType {K : Subgroup G} (htype : IsAltType K 7) :
    ¬ IsExcA7Block K := by
  rintro ⟨-, -, h4⟩
  rw [index_blockZ_of_isAltType htype, card_evenWeight_seven] at h4
  norm_num at h4

end Excl

section Main

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem three_of_isAltType (hC129 : ASC129Statement G) (hI : B5.B51IrrInputs)
    (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (h : Hyp27 H R M K)
    (hchi : IsChiBlock2 H K) {m : ℕ} (hm : Odd m) (htype : IsAltType K m) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hK : IsShort2 K := hchi.1.1
  obtain ⟨T, hT, hRT⟩ := h.starHyp.exists_sylow
  obtain ⟨α, hα, hker, -⟩ := id htype
  rcases five_or_seven_of_isAltType h hm htype with rfl | rfl
  · have hZ := center_quot_eq_bot_of_surj (Or.inl rfl) α hα hker
    have E := entryPlus_of_hyp27 hI hA21 hA36 h (Or.inl rfl)
      (isAltQuotient_of_surj (Or.inl rfl) α hα hker) hT hRT
    rcases spec4a_holds G _ _ _ _ _ _ _ E.toEntry with hc | hc | hc | hc | hc | hc
    · exact absurd (spec4cL2_holds G _ _ _ _ _ _ _ E.toEntry hc
        (blockData_of_short h h.starHyp hK hZ)) (AppC.not_lin2_of_alt5 hK htype (by norm_num))
    · obtain ⟨-, π, hπ, hinj⟩ := hc
      have hfix := fix_eq_one_of_realizes _ (Or.inl rfl) hπ E.case1i.1
      obtain ⟨k, ⟨C⟩⟩ := exists_altCtx h (Or.inl rfl) hT hRT E hinj hπ
      have hk1 := C.k_pos
      have hk2 : k ≤ 2 := by have := C.k_le; omega
      interval_cases k
      · exact C.three_of_k1 hK htype hfix
      · exact C.three_of_k2_five hchi htype
    · exact absurd hc.1 (by norm_num)
    · exact absurd hc.1 (by norm_num)
    · exact absurd hc.1 (by norm_num)
    · exact absurd hc.1 (by norm_num)
  · have hZ := center_quot_eq_bot_of_surj (Or.inr rfl) α hα hker
    have E := entryPlus_of_hyp27 hI hA21 hA36 h (Or.inr rfl)
      (isAltQuotient_of_surj (Or.inr rfl) α hα hker) hT hRT
    rcases spec4a_holds G _ _ _ _ _ _ _ E.toEntry with hc | hc | hc | hc | hc | hc
    · exact absurd hc.1 (by norm_num)
    · exact absurd hc.1 (by norm_num)
    · exact absurd hc.1 (by norm_num)
    · obtain ⟨-, π, hπ, hinj⟩ := hc
      have hfix := fix_eq_one_of_realizes _ (Or.inr rfl) hπ E.case1i.1
      obtain ⟨k, ⟨C⟩⟩ := exists_altCtx h (Or.inr rfl) hT hRT E hinj hπ
      have hk1 := C.k_pos
      have hk2 : k ≤ 3 := by have := C.k_le; omega
      interval_cases k
      · exact C.three_of_k1 hK htype hfix
      · exact AltCtx.three_of_k2_seven hC129 C hchi htype
      · exact AltCtx.three_of_k3 hC129 C hchi htype
    · exact absurd hc.1 (by norm_num)
    · exact absurd (spec4cA7Four_holds G _ _ _ _ _ _ _ E.toEntry hc
        (blockData_of_short h h.starHyp hK hZ)) (not_isExcA7Block_of_isAltType htype)

theorem three_of_isExcA7Block (hI : B5.B51IrrInputs)
    (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (h : Hyp27 H R M K)
    (hexc : IsExcA7Block K) : C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  obtain ⟨T, hT, hRT⟩ := h.starHyp.exists_sylow
  obtain ⟨α, hα, hker⟩ := hexc.2.1
  have hZ := center_quot_eq_bot_of_surj (Or.inr rfl) α hα hker
  have E := entryPlus_of_hyp27 hI hA21 hA36 h (Or.inr rfl)
    (isAltQuotient_of_surj (Or.inr rfl) α hα hker) hT hRT
  rcases spec4a_holds G _ _ _ _ _ _ _ E.toEntry with hc | hc | hc | hc | hc | hc
  · exact absurd hc.1 (by norm_num)
  · exact absurd hc.1 (by norm_num)
  · exact absurd hc.1 (by norm_num)
  · exact absurd hexc (not_isExcA7Block_of_isAltType (spec4cAlt7_holds G _ _ _ _ _ _ _ E.toEntry
      hc (blockData_of_short h h.starHyp hexc.1 hZ)))
  · exact absurd hc.1 (by norm_num)
  · exact three_of_caseA7Four h E hc hexc

end Main

end CFSG.Quasithin.SmithC27
