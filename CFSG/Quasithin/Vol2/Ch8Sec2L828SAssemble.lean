module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SCocode
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5In
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SLem13

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

@[expose] def Stmt8_2_8CocodeFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Row711M24Cocode T L I →
        ∀ P U LU : Subgroup G, P = pCoreOf 2 (ch82I (fsuV T I) h) → U = ch82U (fsuV T I) h →
          LU = ch82LU L U →
          ∀ x : G, x ∈ Subgroup.normalizer (P : Set G) → x ∈ Subgroup.normalizer (U : Set G) →
            (∃ a : ℕ, x ^ 5 ^ a = 1) → (∀ w ∈ LU, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U) →
            (∀ w ∈ ch82I (fsuV T I) h, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U) → ∀ p ∈ P, ⁅x, p⁆ ∈ U

section Assemble

variable {G : Type} [Group G] [Finite G]

theorem stmt8_2_8Cocode_of (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828)
    (hFive : Stmt8_2_8CocodeFive) : Stmt8_2_8Cocode := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc P U LU hP hU hLU'
  subst hP hU hLU'
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
  have hhI := hC.2.1
  obtain ⟨hIN, -, -, hVB⟩ := s828_lemma13 (H := H) hC5 hS hLUT hLN hhI hLUC hK hKle hKn' hLUK hq
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  obtain ⟨hc1, hc2⟩ := s828_cocode_clauses12 hE214 hMB0 hMB3 hSyl hcard hyp h731 h821 hrow hH
    hh hC hC5 hL0 hV hVT hTV hLN hAL hIN hVB
  exact ⟨hc1, hc2, hFive G T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc _ _ _ rfl rfl rfl⟩

theorem step828Three_Bt_of (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB1 : MB1_828) (hSyl : Sylow822VB_828) :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
      Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
        ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
          Concl822 T L I H h k →
          (∀ n : ℕ, Row711L3Nine T L I n →
            ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
              ch82B (fsuV T I) h) ∧
          (Row711M24Cocode T L I →
            ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
              ch82B (fsuV T I) h) ∧
          (Row711M22Code T L I →
            (⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h).relIndex
              (ch82B (fsuV T I) h) = 2) := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe0, hTU, hIU, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ :=
    lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe0 hLUT
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
  have hhI := hC.2.1
  obtain ⟨hIN, -, -, hVB⟩ := s828_lemma13 (H := H) hC5 hS hLUT hLN hhI hLUC hK hKle hKn' hLUK hq
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hAe : IsElemAbelian 2 (ch82A (fsuV T I) h) :=
    isElemAbelian_of_le_conjSub_82 hV inf_le_left
  have hB := s828_prop21 hyp h731 h821 hrow hH hh hC hC5 hMB0 hSyl hcard hV hL0 hVT hTV hLN hAL
    hVB
  refine ⟨fun n hn => s828_Bt_L3 (H := H) hMB1 hcard hV hL0 hC5 hLN hAN hAL hAe hB ⟨n, hn⟩,
    fun hr => s828_Bt_cocode (H := H) hMB1 hcard hV hL0 hC5 hLN hAN hAL hAe hB hr,
    fun hr => s828_Bt_M22 (H := H) hMB1 hcard hV hL0 hC5 hLN hAN hAL hAe hB hr⟩

end Assemble

end CFSG.Quasithin.H13
