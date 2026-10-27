module

public import CFSG.Quasithin.Recognition.St84.J2Borel
public import CFSG.Quasithin.Recognition.St84.J2Chart
public import CFSG.Quasithin.Recognition.St84.AutJ2Model
public import CFSG.Quasithin.Recognition.St84.AutJ2VertexS

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.A312J2 CFSG.Quasithin.F112R CFSG.Quasithin.F112R.AJ2L
open CFSG.Quasithin.F112R.St84.Heis
open CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover

variable {G : Type} [Group G]

theorem AutJ2LocalData.card_bigB [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    Nat.card ↥(bigB L2 L1 S) = 768 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hB : bigB L2 L1 S = borelOf L2 S ⊔ S := by
    rw [bigB, CFSG.Quasithin.F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1]
    exact le_antisymm
      (sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hBJ : Nat.card ↥(borelOf L2 S) = 384 := by
    obtain ⟨eL⟩ := (hD.autJ2Vertex hF h1 h2).model
    obtain ⟨eY⟩ := J2Model.nonempty_mulEquiv_Y3
    exact card_inf_normalizer_of_mulEquiv (L := L2) (T := S ⊓ L2) (eL.trans eY.symm)
      hF.1.h2.sylow
  have hS2 : Nat.card ↥(S ⊓ L2) = 2 ^ 7 := by
    rw [hF.1.h2.sylow.card_eq]
    exact CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 15) (by norm_num)
      (by rw [AutJ2LocalData.card_right h2 hD]; norm_num)
  have hinf : (borelOf L2 S) ⊓ S = S ⊓ L2 := by
    have h1 : S ⊓ L2 ≤ borelOf L2 S := le_inf inf_le_right Subgroup.le_normalizer
    refine le_antisymm ?_ (le_inf h1 inf_le_left)
    calc (borelOf L2 S) ⊓ S ≤ L2 ⊓ S :=
          le_inf (inf_le_left.trans (CFSG.Quasithin.F1.borelOf_le L2 S)) inf_le_right
      _ = S ⊓ L2 := inf_comm _ _
  have hSN : S ≤ Subgroup.normalizer (borelOf L2 S : Set G) := by
    have h := (CFSG.Quasithin.F1.bigB_le_normalizer_borelOf hR).2
    rw [← bigB_comm L1 L2 S] at h
    exact (le_sup_right : S ≤ bigB L2 L1 S).trans h
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := S) (K := borelOf L2 S) hSN
  rw [sup_comm S (borelOf L2 S), inf_comm S (borelOf L2 S), hinf, hBJ, hD.card_S, hS2,
    ← hB] at hprod
  refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 128) ?_
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num] at hprod
  rw [hprod]
  norm_num

private theorem autJ2_isSylowTwoOf_parabolic_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    IsSylowTwoOf S (L2 ⊔ bigB L2 L1 S) := by
  have hSP : S ≤ L2 ⊔ bigB L2 L1 S :=
    (le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right
  have hcardP : Nat.card ↥(L2 ⊔ bigB L2 L1 S) = 3840 :=
    AutJ2LocalData.card_parabolic_right hF h1 h2 hD
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex hSP
    (IsPGroup.of_card (n := 8) (by rw [hD.card_S])) ?_
  have hrel := Subgroup.relIndex_mul_card (H := S) (K := L2 ⊔ bigB L2 L1 S)
  rw [inf_eq_left.mpr hSP, hD.card_S, hcardP] at hrel
  have h15 : S.relIndex (L2 ⊔ bigB L2 L1 S) = 15 := by omega
  rw [h15]
  norm_num

private theorem autJ2_exists_mulEquiv_parabolic_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : AutJ2LocalData L1 L2 S) :
    ∃ Φ : ↥(L2 ⊔ bigB L2 L1 S) ≃* ↥(AJ2L.rCtx.Y 2),
      (S.subgroupOf (L2 ⊔ bigB L2 L1 S)).map
          (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2)) =
        AJ2L.rCtx.S.subgroupOf (AJ2L.rCtx.Y 2) := by
  have hSylP := autJ2_isSylowTwoOf_parabolic_right hF h1 h2 hD
  have hSylY : IsSylowTwoOf AJ2L.rCtx.S (AJ2L.rCtx.Y 2) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right AJ2L.rCtx_sylow (AJ2L.rCtx.S_le_Y 2) le_top
  obtain ⟨Φ₀⟩ := AutJ2Vertex.nonempty_mulEquiv (hD.autJ2Vertex hF h1 h2)
    (AutJ2Model.autJ2Vertex_Y2)
  exact CFSG.exists_mulEquiv_map_subgroupOf_eq_of_isSylowTwoOf Φ₀ hSylP hSylY

private theorem autJ2_image_bigB_eq_inf [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : AutJ2LocalData L1 L2 S)
    {Φ : ↥(L2 ⊔ bigB L2 L1 S) ≃* ↥(AJ2L.rCtx.Y 2)}
    (hΦ : (S.subgroupOf (L2 ⊔ bigB L2 L1 S)).map
        (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2)) =
      AJ2L.rCtx.S.subgroupOf (AJ2L.rCtx.Y 2)) :
    Nonempty (↥(bigB L2 L1 S) ≃* ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBP : bigB L2 L1 S ≤ L2 ⊔ bigB L2 L1 S := le_sup_right
  have hSB : S ≤ bigB L2 L1 S := le_sup_right
  have hcardB : Nat.card ↥(bigB L2 L1 S) = 768 :=
    AutJ2LocalData.card_bigB hF h1 h2 hD
  let W : Subgroup ↥(AJ2L.rCtx.Y 2) :=
    ((bigB L2 L1 S).subgroupOf (L2 ⊔ bigB L2 L1 S)).map
      (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2))
  let Z : Subgroup ↥R := W.map (AJ2L.rCtx.Y 2).subtype
  have hBsub : Nat.card ↥((bigB L2 L1 S).subgroupOf (L2 ⊔ bigB L2 L1 S)) =
      Nat.card ↥(bigB L2 L1 S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  have hWcard : Nat.card ↥W = 768 := by
    show Nat.card ↥(((bigB L2 L1 S).subgroupOf (L2 ⊔ bigB L2 L1 S)).map
      (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2))) = 768
    rw [Subgroup.card_map_of_injective Φ.injective, hBsub, hcardB]
  have hZcard : Nat.card ↥Z = 768 := by
    show Nat.card ↥(W.map (AJ2L.rCtx.Y 2).subtype) = 768
    rw [Subgroup.card_map_of_injective (AJ2L.rCtx.Y 2).subtype_injective, hWcard]
  have hZle2 : Z ≤ AJ2L.rCtx.Y 2 := Subgroup.map_subtype_le W
  have hSZ : AJ2L.rCtx.S ≤ Z := by
    intro x hx
    have hxY : x ∈ AJ2L.rCtx.Y 2 := AJ2L.rCtx.S_le_Y 2 hx
    have hx' : (⟨x, hxY⟩ : ↥(AJ2L.rCtx.Y 2)) ∈ W := by
      have h2 : (⟨x, hxY⟩ : ↥(AJ2L.rCtx.Y 2)) ∈
          AJ2L.rCtx.S.subgroupOf (AJ2L.rCtx.Y 2) := hx
      rw [← hΦ] at h2
      have h3 : (S.subgroupOf (L2 ⊔ bigB L2 L1 S)).map
            (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2)) ≤
          ((bigB L2 L1 S).subgroupOf (L2 ⊔ bigB L2 L1 S)).map
            (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2)) :=
        Subgroup.map_mono (fun y hy => hSB hy)
      exact h3 h2
    exact Subgroup.mem_map_of_mem (AJ2L.rCtx.Y 2).subtype hx'
  rcases AJ2L.overgroup hSZ with htop | ⟨j, hj, hZj, hcardj⟩
  · rw [htop, Subgroup.card_top, card_R] at hZcard
    norm_num at hZcard
  · have hord : (#[1, 9, 15, 3, 3] : Array ℕ)[j]! * 2 ^ 8 = 768 := by
      rw [← hcardj, hZcard]
    have hj34 : j = 3 ∨ j = 4 := by
      interval_cases j <;> simp_all
    have hZle1 : Z ≤ AJ2L.rCtx.Y 1 := by
      rw [hZj]
      rcases hj34 with rfl | rfl
      · exact AJ2L.Y3_le_Y1
      · exact AJ2L.Y4_le_Y1
    have hZle : Z ≤ AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1 := le_inf hZle2 hZle1
    have hcard4 : Nat.card ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1) = 768 := by
      rw [AJ2Y.inf_eq, AJ2L.rCtx_card (by norm_num)]
      norm_num
    have hZeq : Z = AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1 :=
      Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard4, hZcard])
    exact ⟨(Subgroup.subgroupOfEquivOfLe hBP).symm.trans
      ((Subgroup.equivMapOfInjective ((bigB L2 L1 S).subgroupOf (L2 ⊔ bigB L2 L1 S))
          (Φ : ↥(L2 ⊔ bigB L2 L1 S) →* ↥(AJ2L.rCtx.Y 2)) Φ.injective).trans
        ((Subgroup.equivMapOfInjective W (AJ2L.rCtx.Y 2).subtype
            (AJ2L.rCtx.Y 2).subtype_injective).trans
          (MulEquiv.subgroupCongr hZeq)))⟩

theorem AutJ2LocalData.nonempty_mulEquiv_borel [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : AutJ2LocalData L1 L2 S) :
    Nonempty (↥(bigB L2 L1 S) ≃* ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1)) := by
  obtain ⟨Φ, hΦ⟩ := autJ2_exists_mulEquiv_parabolic_right hF h1 h2 hD
  exact autJ2_image_bigB_eq_inf hF h1 h2 hD hΦ

private theorem autJ2_card_L1 {L1 L2 S : Subgroup G} (h1 : VS3 L1)
    (hD : AutJ2LocalData L1 L2 S) : Nat.card L1 = 384 := by
  rw [card_eq_six_mul_of_vs3 h1, hD.card_left]
  norm_num

private theorem autJ2_card_S_inf_L1 [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hD : AutJ2LocalData L1 L2 S) :
    Nat.card ↥(S ⊓ L1) = 2 ^ 7 := by
  rw [hF.1.h1.sylow.card_eq]
  exact CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 3) (by norm_num)
    (by rw [autJ2_card_L1 h1 hD]; norm_num)

private theorem autJ2_normalizer_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    L1 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (L1 : Set G) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  rw [← bigB_comm L2 L1 S]
  exact CFSG.Quasithin.F1.parabolic_le_normalizer hR

private theorem autJ2_card_parabolic_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    Nat.card ↥(L1 ⊔ bigB L2 L1 S) = 2304 := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hP1norm := autJ2_normalizer_left hF h1 h2
  have hcardB : Nat.card ↥(bigB L2 L1 S) = 768 :=
    AutJ2LocalData.card_bigB hF h1 h2 hD
  have hL1B : L1 ⊓ bigB L2 L1 S = borelOf L1 S := by
    have h := CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR
    rwa [← bigB_comm L1 L2 S] at h
  have hBK : bigB L2 L1 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (le_sup_right : bigB L2 L1 S ≤ L1 ⊔ bigB L2 L1 S).trans hP1norm
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := bigB L2 L1 S) (K := L1) hBK
  rw [sup_comm (bigB L2 L1 S) L1, inf_comm (bigB L2 L1 S) L1, hL1B,
    CFSG.Quasithin.F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1,
    autJ2_card_S_inf_L1 hF h1 hD, hcardB, autJ2_card_L1 h1 hD] at hprod
  refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 128) ?_
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num] at hprod
  rw [hprod]

private theorem autJ2_isSylowTwoOf_parabolic_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    IsSylowTwoOf S (L1 ⊔ bigB L2 L1 S) := by
  have hSP1le : S ≤ L1 ⊔ bigB L2 L1 S :=
    (le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex hSP1le
    (IsPGroup.of_card (n := 8) (by rw [hD.card_S])) ?_
  have hrel := Subgroup.relIndex_mul_card (H := S) (K := L1 ⊔ bigB L2 L1 S)
  rw [inf_eq_left.mpr hSP1le, hD.card_S, autJ2_card_parabolic_left hF h1 h2 hD] at hrel
  have h9 : S.relIndex (L1 ⊔ bigB L2 L1 S) = 9 := by omega
  rw [h9]
  norm_num

private theorem autJ2_exists_heisChart_aut [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    ∃ (χ : ↥(pCoreOf 2 L1) ≃* Q1M) (β t : G),
      β ∈ borelOf L2 S ∧ β ^ 3 = 1 ∧ ActsAs χ β βM ∧ t ∈ S ⊓ L2 ∧ ActsAs χ t τM ∧
        S ⊓ L2 ⊓ Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ pCoreOf 2 L1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS1 : Nat.card ↥(S ⊓ L1) = 2 ^ 7 := autJ2_card_S_inf_L1 hF h1 hD
  obtain ⟨eL⟩ := (hD.autJ2Vertex hF h1 h2).model
  obtain ⟨eY⟩ := J2Model.nonempty_mulEquiv_Y3
  obtain ⟨eC⟩ := J2Model.nonempty_C2_equiv_Y3
  obtain ⟨Φ, hΦS⟩ := exists_chartMap_of_mulEquiv (eL.trans (eY.symm.trans eC.symm))
    hF.1.h2.sylow
  have hrelS : (S ⊓ L1).relIndex S = 2 := by
    have h := Subgroup.relIndex_mul_card (H := S ⊓ L1) (K := S)
    rw [inf_eq_left.mpr (inf_le_left : S ⊓ L1 ≤ S), hS1, hD.card_S] at h
    omega
  have hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2 := by
    rw [show S ⊓ L2 ⊓ L1 = (S ⊓ L1) ⊓ (S ⊓ L2) from by
      ext x
      simp only [Subgroup.mem_inf]
      tauto]
    rw [Subgroup.inf_relIndex_right]
    calc (S ⊓ L1).relIndex (S ⊓ L2)
        ≤ (S ⊓ L1).relIndex S :=
          Subgroup.relIndex_le_of_le_right (inf_le_left : S ⊓ L2 ≤ S)
            (by rw [hrelS]; norm_num)
      _ = 2 := hrelS
  obtain ⟨χ, _hQ1leS2, ⟨β, hβB, hβ3, hβacts⟩, ⟨t, htS2, htacts⟩, hchartZ⟩ :=
    J2Model.exists_heisChart Φ hΦS hD.card_left
      (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hF.1.h1.sylow) hS1 hidx hF.1.h1.borel_le
  exact ⟨χ, β, t, hβB, hβ3, hβacts, htS2, htacts, hchartZ⟩

private theorem autJ2_relIndex_pCoreOf_le_two [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    (pCoreOf 2 L1).relIndex (pCoreOf 2 (L1 ⊔ bigB L2 L1 S)) ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS1 : Nat.card ↥(S ⊓ L1) = 2 ^ 7 := autJ2_card_S_inf_L1 hF h1 hD
  have hP1norm := autJ2_normalizer_left hF h1 h2
  have hSP1 := autJ2_isSylowTwoOf_parabolic_left hF h1 h2 hD
  have hQ1leO : pCoreOf 2 L1 ≤ pCoreOf 2 (L1 ⊔ bigB L2 L1 S) :=
    CFSG.GH74.QTGen4.DSGen4.FaithfulA5.pCoreOf_le_of_normalizes le_sup_left hP1norm
  have hOinf : pCoreOf 2 (L1 ⊔ bigB L2 L1 S) ⊓ L1 = pCoreOf 2 L1 := by
    refine le_antisymm ?_ (le_inf hQ1leO (CFSG.LieType.BorelTits.pCoreOf_le 2 L1))
    exact CFSG.Quasithin.F7.pCoreOf_inf_le (le_sup_left : L1 ≤ L1 ⊔ bigB L2 L1 S)
  have hOS : pCoreOf 2 (L1 ⊔ bigB L2 L1 S) ≤ S :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSP1
  have hQ1S : pCoreOf 2 L1 ≤ S := hQ1leO.trans hOS
  have hS4 : (pCoreOf 2 L1).relIndex S = 4 := by
    have hc := Subgroup.relIndex_mul_card (H := pCoreOf 2 L1) (K := S)
    rw [inf_eq_left.mpr hQ1S, hD.card_left, hD.card_S] at hc
    omega
  have hdiv : (pCoreOf 2 L1).relIndex (pCoreOf 2 (L1 ⊔ bigB L2 L1 S)) ∣ 4 := by
    have h := Subgroup.relIndex_mul_relIndex (pCoreOf 2 L1)
      (pCoreOf 2 (L1 ⊔ bigB L2 L1 S)) S hQ1leO hOS
    rw [hS4] at h
    exact ⟨_, h.symm⟩
  obtain ⟨k, hk2, hk⟩ :=
    (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 2)).mp (by simpa using hdiv)
  rw [hk]
  interval_cases k
  · norm_num
  · norm_num
  · exfalso
    have heq : (pCoreOf 2 L1).relIndex (pCoreOf 2 (L1 ⊔ bigB L2 L1 S)) = 4 := by
      rw [hk]
      norm_num
    have hOcard : Nat.card ↥(pCoreOf 2 (L1 ⊔ bigB L2 L1 S)) = 256 := by
      have hc := Subgroup.relIndex_mul_card (H := pCoreOf 2 L1)
        (K := pCoreOf 2 (L1 ⊔ bigB L2 L1 S))
      rw [inf_eq_left.mpr hQ1leO, hD.card_left, heq] at hc
      omega
    have hOS' : pCoreOf 2 (L1 ⊔ bigB L2 L1 S) = S :=
      Subgroup.eq_of_le_of_card_ge hOS (by rw [hOcard, hD.card_S]; norm_num)
    have hthis : (2 : ℕ) ^ 7 = 2 ^ 6 := by
      rw [← hS1, ← hD.card_left, ← hOS', hOinf]
    norm_num at hthis

private theorem autJ2_central_involution_mem [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S)
    (hchartZ : S ⊓ L2 ⊓ Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ pCoreOf 2 L1)
    {c : G} (hcP : c ∈ L1 ⊔ bigB L2 L1 S)
    (hcent : ∀ g ∈ L1 ⊔ bigB L2 L1 S, g * c = c * g) (hc2 : c ^ 2 = 1) :
    c ∈ pCoreOf 2 L1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hSP1 := autJ2_isSylowTwoOf_parabolic_left hF h1 h2 hD
  have hSP1le : S ≤ L1 ⊔ bigB L2 L1 S := hSP1.1
  have hQleS : pCoreOf 2 L2 ≤ S :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hF.1.h2.sylow).trans inf_le_left
  have hcentz : L1 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.le_centralizer_iff.mpr
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hcent))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hpg : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hc2)
  have hcO : c ∈ pCoreOf 2 (L1 ⊔ bigB L2 L1 S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      (Subgroup.zpowers_le.mpr hcP) hcentz hpg (Subgroup.mem_zpowers c)
  have hcS : c ∈ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSP1 hcO
  have hcQcent : c ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcent q (hSP1le (hQleS hq))
  have hcP2 : c ∈ L2 ⊔ bigB L2 L1 S :=
    (le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right hcS
  have hcQ : c ∈ pCoreOf 2 L2 := by
    have hchar2 : CharTwo (L2 ⊔ bigB L2 L1 S) :=
      CFSG.Quasithin.F1.parabolic_charTwo hR.symm
    have hchar2' : (L2 ⊔ bigB L2 L1 S) ⊓ Subgroup.centralizer
        (pCoreOf 2 (L2 ⊔ bigB L2 L1 S) : Set G) ≤
        pCoreOf 2 (L2 ⊔ bigB L2 L1 S) := hchar2
    rw [AutJ2LocalData.pCoreOf_parabolic_right hF h1 h2 hD] at hchar2'
    exact hchar2' ⟨hcP2, hcQcent⟩
  have hcentQ1 : c ∈ Subgroup.centralizer (pCoreOf 2 L1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcent q ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans le_sup_left hq)
  exact hchartZ ⟨⟨hcS, (CFSG.LieType.BorelTits.pCoreOf_le 2 L2) hcQ⟩, hcentQ1⟩

theorem AutJ2LocalData.nonempty_mulEquiv_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    Nonempty (↥(L1 ⊔ bigB L2 L1 S) ≃* Q1M ⋊[AJ'.subtype] ↥AJ') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hP1norm := autJ2_normalizer_left hF h1 h2
  have hSP1le : S ≤ L1 ⊔ bigB L2 L1 S :=
    (autJ2_isSylowTwoOf_parabolic_left hF h1 h2 hD).1
  obtain ⟨χ, β, t, hβB, hβ3, hβacts, htS2, htacts, hchartZ⟩ :=
    autJ2_exists_heisChart_aut hF h1 h2 hD
  have hβP : β ∈ L1 ⊔ bigB L2 L1 S :=
    (le_sup_right : bigB L2 L1 S ≤ L1 ⊔ bigB L2 L1 S)
      ((le_sup_left.trans le_sup_left : borelOf L2 S ≤ bigB L2 L1 S) hβB)
  have htP : t ∈ L1 ⊔ bigB L2 L1 S := hSP1le ((inf_le_left : S ⊓ L2 ≤ S) htS2)
  have hZ : ∀ c ∈ L1 ⊔ bigB L2 L1 S, (∀ g ∈ L1 ⊔ bigB L2 L1 S, g * c = c * g) →
      c ^ 2 = 1 → c ∈ pCoreOf 2 L1 :=
    fun c hcP hcent hc2 => autJ2_central_involution_mem hF h1 h2 hD hchartZ hcP hcent hc2
  refine nonempty_mulEquiv_heisModelAut (P := L1 ⊔ bigB L2 L1 S) (Q := pCoreOf 2 L1)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans le_sup_left)
    (hP1norm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L1))
    (autJ2_card_parabolic_left hF h1 h2 hD) ?_ (autJ2_relIndex_pCoreOf_le_two hF h1 h2 hD)
    χ hβP hβ3 ?_ htP ?_ hZ
  · rw [← bigB_comm L2 L1 S]
    exact CFSG.Quasithin.F1.parabolic_charTwo hR
  · exact parAct_eq_of_actsAs hβP hβacts
  · exact parAct_eq_of_actsAs htP htacts

theorem isParabolicAmalgamOfGroup_autJ2_of_autJ2LocalData [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    IsParabolicAmalgamOfGroup (f112Amalgam L2 L1 S)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) := by
  refine ⟨↥J2Cover.R, inferInstance,
    ⟨((CFSG.Quasithin.H13.mulAutCongrOfMulEquiv
      (quasithinJ2MulEquivNative.trans J2Cover.nativeEquivP)).trans
        J2Cover.rAutEquiv.symm).symm⟩,
    AJ2L.rCtx.S, AJ2L.rCtx.Y 2, AJ2L.rCtx.Y 1, AJ2Y.isYAmalgamPair, ?_, ?_, ?_⟩
  · exact AutJ2Vertex.nonempty_mulEquiv (hD.autJ2Vertex hF h1 h2)
      (AutJ2Model.autJ2Vertex_Y2)
  · obtain ⟨e⟩ := hD.nonempty_mulEquiv_borel hF h1 h2
    exact ⟨(MulEquiv.subgroupCongr (parabolic_inf_eq_bigB_of_vs3_va5 hF h1 h2)).trans e⟩
  · obtain ⟨e⟩ := hD.nonempty_mulEquiv_left hF h1 h2
    obtain ⟨f⟩ := AutJ2Model.nonempty_Y1_equiv
    exact ⟨e.trans f.symm⟩

end CFSG.Quasithin.F112R.St84

