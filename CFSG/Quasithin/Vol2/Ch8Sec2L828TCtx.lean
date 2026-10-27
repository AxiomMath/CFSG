module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SCocode
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SLem13
public import CFSG.Quasithin.Vol2.E2NineMembers

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G]

structure S828Ctx (T L I H : Subgroup G) (h : G) (k : ℕ) [IsMulCommutative ↥(fsuV T I)] : Prop where
  hC : Concl822 T L I H h k
  hC5 : Concl825 T L I h k
  hV : IsElemAbelian 2 (fsuV T I)
  hVT : fsuV T I ≤ T
  hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G)
  hL0 : fsuL0 T L = L
  hTL : T ≤ Subgroup.normalizer (L : Set G)
  hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G)
  hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G)
  hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G)
  hAe : IsElemAbelian 2 (ch82A (fsuV T I) h)
  hLUT : T ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G)
  hhI : h ∈ ch82I (fsuV T I) h
  hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G)
  hcomm : ⁅ch82LU L (ch82U (fsuV T I) h), ch82I (fsuV T I) h⁆ ≤
    pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h))
  hILU : ⁅ch82I (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ pCoreOf 2 (ch82I (fsuV T I) h)
  hVB : ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h
  hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
    ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h
  hUZ : ch82U (fsuV T I) h = ch82ZI (fsuV T I) h
  hUB : ch82U (fsuV T I) h ≤ ch82B (fsuV T I) h
  hcen : ∀ u ∈ ch82U (fsuV T I) h, ∀ i ∈ ch82I (fsuV T I) h, i * u * i⁻¹ = u
  hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h
  hP2 : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ∀ q ∈ pCoreOf 2 (ch82I (fsuV T I) h),
    ⁅p, q⁆ ∈ ch82U (fsuV T I) h
  hO2P : ∀ w ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)),
    ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ⁅w, p⁆ ∈ ch82U (fsuV T I) h
  hfaith : ∀ d ∈ ch82I (fsuV T I) h,
    (∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), d * p * d⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h) →
      d ∈ pCoreOf 2 (ch82I (fsuV T I) h)
  hB5 : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
    (∀ v ∈ fsuV T I, v * p * v⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h) → p ∈ ch82B (fsuV T I) h

theorem s828_k_le_two {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)] {h : G} {k : ℕ}
    (hrow : Case8_2 T L I) (hC5 : Concl825 T L I h k) : k ≤ 2 := by
  rcases hrow with hr | hr | hr | hr
  · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.1 hr).1
    have : k = 1 := by exact_mod_cast this
    omega
  · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.2.1 hr).1
    have : k = 1 := by exact_mod_cast this
    omega
  · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.2.2.1 hr).1
    have : k = 1 := by exact_mod_cast this
    omega
  · have : (k : ℕ∞) = 2 := hC5.1.symm.trans (hC5.2.2.2.2.2.2.1 hr).1
    have : k = 2 := by exact_mod_cast this
    omega

theorem s828_ctx (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828)
    {T L I H : Subgroup G} {h : G} {k : ℕ} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k) :
    S828Ctx T L I H h k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, hIU, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ :=
    lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hLUU : ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hS : QuasithinUnique.IsSylowTwoOf T
      (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  obtain ⟨K, hK, hLUK, hKn⟩ := exists_k_828 h37 h38 h39 hyp hU2 hU1 hTU hLUU hfam hLUT
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  have hKle := le_of_mem_cComp hK
  have hKn' := (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp hKn
  have hhI : h ∈ ch82I (fsuV T I) h := hC.2.1
  obtain ⟨hIN, hcore, hILU, hVB⟩ :=
    s828_lemma13 (H := H) hC5 hS hLUT hLN hhI hLUC hK hKle hKn' hLUK hq
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hk2 := s828_k_le_two hrow hC5
  have hPeq := s828_pCore_eq_sup (hE214 := hE214) hC hk2
  have hP := s828_pair hV hVT hTV hC
  have hUZ : ch82U (fsuV T I) h = ch82ZI (fsuV T I) h := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hUZ', -, -⟩ := hC5
    exact hUZ'
  have hZc : ch82ZI (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) :=
    hC.2.2.2.2.1
  have hcen : ∀ u ∈ ch82U (fsuV T I) h, ∀ i ∈ ch82I (fsuV T I) h, i * u * i⁻¹ = u := by
    intro u hu i hi
    have hu' : u ∈ ch82ZI (fsuV T I) h := hUZ ▸ hu
    have := (Subgroup.mem_centralizer_iff.mp (hZc hu')) i hi
    rw [this]
    group
  have hB := s828_prop21 hyp h731 h821 hrow hH hh hC hC5 hMB0 hSyl hcard hV hL0 hVT hTV hLN hAL
    hVB
  have hP2 := s828_comm_P_U hC hUZ hP hPeq
  have hO2P := s828_lu_centralizes_P (H := H) hMB3 hcard hV hL0 hC5 hLN hAN hAL hAe hB hrow hhI
    hIN hcen hPeq
  obtain ⟨-, -, hIC, -, -, -, -, hker, -, -, -, -, -, -, -, -, -, hUB, h28, hcharH, -⟩ := id hC
  have hchar : QuasithinUnique.CharTwo (ch82I (fsuV T I) h) :=
    (ASInputs.e2_9C_members h28 hIC).2 hcharH
  refine ⟨hC, hC5, hV, hVT, hTV, hL0, hTL, hLN, hAN, hAL, hAe, hLUT, hhI, hIN, hcore, hILU, hVB,
    hB, hUZ, hUB, hcen, hPeq, hP2, hO2P, ?_, ?_⟩
  · intro d hd hdP
    refine s828_centralizer_tilde_le_P hP hPeq hZc hchar hd (fun p hp => ?_)
    rw [← hUZ]
    exact hdP p hp
  · intro p hp hxv
    refine s828_mem_B_of_centralizes hP hPeq hker hp (fun v hv => ?_)
    rw [← hUZ]
    exact hxv v hv

end Ctx

end CFSG.Quasithin.H13
