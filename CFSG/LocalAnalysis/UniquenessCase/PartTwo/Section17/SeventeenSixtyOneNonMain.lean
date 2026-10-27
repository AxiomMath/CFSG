module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem seven_dvd_card_bar_of_isL2_or_isSz
    {K : Subgroup G}
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) : 7 ∣ Nat.card (Bar2 K) := by
  rcases hshape with h | h
  · rw [card_of_isL2 h]
    norm_num
  · rw [CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]
    norm_num

theorem seven_notMem_sig
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h55 : R17_55At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) : 7 ∉ D.sig := by
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hKn : (K.subgroupOf D.M).Normal := (ctx.hyp54.2 K hKcalM).1
  have h7dvdK : 7 ∣ Nat.card (Bar2 K) := seven_dvd_card_bar_of_isL2_or_isSz hshape
  obtain ⟨X, hXK, hXcard⟩ :=
    s13_exists_subgroup_of_dvd_card_bar (r := 7) Nat.prime_seven h7dvdK
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  intro h7
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h7
  exact (h55 K hKM hKn 3 hshape 3 (by norm_num) dvd_rfl 7 Nat.prime_seven
      (by norm_num : (7 : ℕ) ∣ 2 ^ 3 - 1) X hXK hXcard)
    (conjSetOf_eq_of_isStronglyPEmbedded hsp (hXK.trans hKM) hXcard)

theorem nonMain_barImage_mono {D : Data G} {P Q : Subgroup G} (hPQ : P ≤ Q) :
    barImage D.M P ≤ barImage D.M Q := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr (hPQ (Subgroup.mem_subgroupOf.mp hy)))

omit [Finite G] in
theorem isSimpleGroup_bar_of_isL2_or_isSz {K : Subgroup G}
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) : IsSimpleGroup (Bar2 K) := by
  rcases hshape with h | h
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  · have hS : CFSG.Blueprint.SuzukiModel (Bar2 K) 2 3 :=
      (CFSG.Blueprint.LieModel.twistedB2_iff (n := 0) (p := 2) (f := 3)).mp h |>.2
    exact (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 K) 2 3 hS).2

theorem mem_sup_of_mem_barImage_sup_of_sevenPow {D : Data G} {L K : Subgroup G}
    (hLM : L ≤ D.M) (hKM : K ≤ D.M) (hLn : (L.subgroupOf D.M).Normal)
    (hKn : (K.subgroupOf D.M).Normal) {x : G} (hxM : x ∈ D.M)
    (hx7 : ∃ k : ℕ, x ^ 7 ^ k = 1)
    (hxbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩) ∈
      barImage D.M (L ⊔ K)) : x ∈ L ⊔ K := by
  classical
  set H : Subgroup G := L ⊔ K with hHdef
  have hHM : H ≤ D.M := sup_le hLM hKM
  have hxbar' : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩) ∈
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) (H.subgroupOf D.M) := by
    simpa [barImage, hHdef] using hxbar
  obtain ⟨h0, hh0, hπ⟩ := Subgroup.mem_map.mp hxbar'
  have hhH : (h0 : G) ∈ H := Subgroup.mem_subgroupOf.mp hh0
  have hhM : (h0 : G) ∈ D.M := h0.2
  let z : G := x * (h0 : G)⁻¹
  have hxeq : x = z * (h0 : G) := by simp [z]
  have hzM : z ∈ D.M := D.M.mul_mem hxM (D.M.inv_mem hhM)
  have hz1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨z, hzM⟩) = 1 := by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨h0, hhM⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ := hπ
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨z, hzM⟩) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨h0, hhM⟩)⁻¹ := by
      rw [show (⟨z, hzM⟩ : ↥D.M) = ⟨x, hxM⟩ * ⟨h0, hhM⟩⁻¹ from rfl, map_mul, map_inv]
    rw [h2, h1, mul_inv_cancel]
  have hzO2 : z ∈ CFSG.Open.pCoreOf 2 D.M := by
    have hmem : (⟨z, hzM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥D.M) _).mp hz1
    exact Subgroup.mem_map_of_mem D.M.subtype hmem
  have hzH : z ∈ H := by
    by_contra hzH
    have hLnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
    have hKnorm : D.M ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
    have hHnorm : (H.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mpr
        ((le_inf hLnorm hKnorm).trans (Subgroup.inf_normalizer_le_normalizer_sup L K))
    have : (H.subgroupOf D.M).Normal := hHnorm
    let π : ↥D.M →* (↥D.M ⧸ H.subgroupOf D.M) := QuotientGroup.mk' _
    obtain ⟨k, hk⟩ := hx7
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    have hxpow7 : orderOf (π ⟨x, hxM⟩) ∣ 7 ^ k := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have h1 : (⟨x, hxM⟩ : ↥D.M) ^ 7 ^ k = 1 := by ext; exact hk
      rw [h1, map_one]
    have hzpow2 : orderOf (π ⟨z, hzM⟩) ∣ 2 ^ m := by
      obtain ⟨z0, hz0, hz0eq⟩ := Subgroup.mem_map.mp hzO2
      have hz0' : z0 = ⟨z, hzM⟩ := Subtype.ext hz0eq
      refine (orderOf_map_dvd π ⟨z, hzM⟩).trans ?_
      rw [← hz0', ← hm]
      exact Subgroup.orderOf_dvd_natCard _ hz0
    have hclass : π ⟨x, hxM⟩ = π ⟨z, hzM⟩ := by
      have hh1 : π ⟨h0, hhM⟩ = 1 := by
        refine (QuotientGroup.eq_one_iff (N := H.subgroupOf D.M) _).mpr ?_
        exact Subgroup.mem_subgroupOf.mpr hhH
      have hxeq' : (⟨x, hxM⟩ : ↥D.M) = ⟨z, hzM⟩ * ⟨h0, hhM⟩ := by ext; exact hxeq
      calc π ⟨x, hxM⟩ = π (⟨z, hzM⟩ * ⟨h0, hhM⟩) := by rw [hxeq']
        _ = π ⟨z, hzM⟩ := by rw [map_mul, hh1, mul_one]
    rw [← hclass] at hzpow2
    have hcop : Nat.Coprime (7 ^ k) (2 ^ m) :=
      (by norm_num : Nat.Coprime 7 2).pow k m
    have hord1 : orderOf (π ⟨x, hxM⟩) = 1 := by
      have hdvd : orderOf (π ⟨x, hxM⟩) ∣ 1 :=
        (Nat.dvd_gcd hxpow7 hzpow2).trans (by rw [hcop.gcd_eq_one])
      exact Nat.dvd_one.mp hdvd
    have hz1' : π ⟨z, hzM⟩ = 1 := by
      have hordz : orderOf (π ⟨z, hzM⟩) = 1 := hclass.symm ▸ hord1
      exact orderOf_eq_one_iff.mp hordz
    have hmem : (⟨z, hzM⟩ : ↥D.M) ∈ H.subgroupOf D.M :=
      (QuotientGroup.eq_one_iff (N := H.subgroupOf D.M) _).mp hz1'
    exact hzH (Subgroup.mem_subgroupOf.mp hmem)
  rw [hxeq]
  exact H.mul_mem hzH hhH

theorem exists_sevenPower_not_mem_sup
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K) :
    ∃ x : G, x ∈ D.M ∧ (∃ k : ℕ, orderOf x = 7 ^ k) ∧ x ∉ L ⊔ K := by
  classical
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hL7 : Opp 7 L = L := by
    have h7dvdL : 7 ∣ Nat.card (Bar2 L) := by
      rw [card_bar_of_isL3 ctx.shapeL]; norm_num
    have hLsimple : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ctx.shapeL
    exact opp_eq_self_of_calC ctx.memC hLsimple Nat.prime_seven (by norm_num) h7dvdL
  have hK7 : Opp 7 K = K := by
    have h7dvdK : 7 ∣ Nat.card (Bar2 K) := seven_dvd_card_bar_of_isL2_or_isSz hshape
    exact opp_eq_self_of_calC hKcalM (isSimpleGroup_bar_of_isL2_or_isSz hshape)
      Nat.prime_seven (by norm_num) h7dvdK
  have hLKle : L ⊔ K ≤ Opp 7 D.M := by
    refine sup_le ?_ ?_
    · rw [← hL7]
      exact s13_Thirteen2_pElementSubgroup_mono (p := 7) hLM
    · rw [← hK7]
      exact s13_Thirteen2_pElementSubgroup_mono (p := 7) hKM
  by_contra hcon
  push Not at hcon
  have hOppLe : Opp 7 D.M ≤ L ⊔ K := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxM, k, hk⟩
    exact hcon x hxM ⟨k, hk⟩
  exact hnotmain (le_antisymm hOppLe hLKle)

theorem false_of_E49_sylow_seven
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h55 : R17_55At D V₀ V)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hp3 : p = 3)
    (E : Subgroup G) (hEM : E ≤ D.M)
    (hEel : IsElemAbelian 7 E) (hEcard : Nat.card E = 49)
    (hEc : 0 < CFSG.Open.pRank 3 (D.M ⊓ Subgroup.centralizer (E : Set G)))
    (hXN : ∀ X' : Subgroup G, X' ≤ E → Nat.card X' = 7 →
      1 < CFSG.Open.pRank 3 (D.M ⊓ Subgroup.normalizer (X' : Set G)))
    (hR : ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 7 R D.M ∧
      E ≤ R ⊓ Subgroup.centralizer (R : Set G)) : False := by
  classical
  subst hp3
  have h3mem : 3 ∈ D.sig := ctx.hyp54.1
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h3mem
  have hΓ : rankThreeGamma 1 7 E ≤ D.M :=
    h76 3 Nat.prime_three (by norm_num) hsp3 7 Nat.prime_seven E hEM hEel hEcard hEc hXN
  have h7notsig : 7 ∉ D.sig :=
    seven_notMem_sig D ctx h55 hSg hK hshape
  obtain ⟨R, hRsyl, hER⟩ := hR
  have hsp7 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M :=
    h614 (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns) 7
      Nat.prime_seven (by norm_num) h7notsig R hRsyl E hER hEel hEcard hΓ
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hKn : (K.subgroupOf D.M).Normal := (ctx.hyp54.2 K hKcalM).1
  have h7dvdK : 7 ∣ Nat.card (Bar2 K) := seven_dvd_card_bar_of_isL2_or_isSz hshape
  obtain ⟨X, hXK, hXcard⟩ :=
    s13_exists_subgroup_of_dvd_card_bar (r := 7) Nat.prime_seven h7dvdK
  exact (h55 K hKM hKn 3 hshape 3 (by norm_num) dvd_rfl 7 Nat.prime_seven
      (by norm_num : (7 : ℕ) ∣ 2 ^ 3 - 1) X hXK hXcard)
    (conjSetOf_eq_of_isStronglyPEmbedded hsp7 (hXK.trans hKM) hXcard)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
