module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs
public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.Background.SmithC27RTypeRank2
public import CFSG.Quasithin.Vol2.Ch12Sec6L32e
public import CFSG.Quasithin.H13.A5S136r
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique S126
open CFSG.Quasithin.H13.F126 CFSG.Quasithin.F7

theorem leafKer_holds : LeafKer := by
  intro G _ _ T V L V₁ Vp H K h
  refine le_antisymm ?_ (pCore_le_ker_toAutI h (le_conjClosure Vp H))
  intro x hx
  rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hxQ : (x : G) ∈ pCoreOf 2 H := mem_pCoreOf_of_actH_eq_one h hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) g)
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hk)) g)
  have hEn : ((K ⊓ pCoreOf 2 H).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKn
  have hEq : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K :=
    le_pCoreOf 2 inf_le_left hEn ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  exact (coe_mem_pCoreOf_iff_mem_pCore x).mp (hEq ⟨x.2, hxQ⟩)

theorem isPSL_statedProj_of_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    IsPSL 3 2 2 (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
  letI := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  have h1 := SmithC27.isPSL_statedSL_three (F := F) (n := 2) (by norm_num) hF'
  exact IsPSL.of_mulEquiv
    ((SmithC27.quotCenterCongr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)) h1

theorem leafCenter_of_ker (hKer : LeafKer) : LeafCenter := by
  intro G _ _ T L V _ F H K c
  have h918 : HypF918 T V L F.V1 F.V5 H K := c.f918
  have h := h918.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hker' : (toAutI h918 F.V5).ker = CFSG.pCore 2 ↥K := hKer G T V L F.V1 F.V5 H K h918
  have hX : autOn (tildeOf F.V1 K) (UT F.V1 F.V5 H) = (S126.star H K).map (psiH h) := by
    rw [← range_thetaH h hKH, S126.star, Subgroup.map_map]
    rfl
  have e₂ : ↥(autIH F.V1 F.V5 H K) ≃* ↥(S126.star H K) :=
    (MulEquiv.subgroupCongr hX).trans
      (Subgroup.equivMapOfInjective (S126.star H K) (psiH h) (psiH_injective h)).symm
  have e₁ : KQ K ≃* ↥(autIH F.V1 F.V5 H K) :=
    (QuotientGroup.quotientMulEquivOfEq hker').symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective (toAutI h918 F.V5) (toAutI_surjective h918 F.V5))
  have eQ : KQ K ≃* ↥(S126.star H K) := e₁.trans e₂
  rcases c.case1.2.1 with ⟨F', hFld, hFin, hF', ⟨eA⟩, -⟩ |
      ⟨F', hFld, hFin, hF', ⟨eA⟩, hidx, hsq⟩
  ·
    have hPSLX : IsPSL 3 2 2 (KQ K) :=
      IsPSL.of_mulEquiv (eQ.trans eA).symm (isPSL_statedProj_of_card_four hF')
    have hbot : Subgroup.center (KQ K) = ⊥ := A5.center_eq_bot_of_isPSL34 hPSLX
    refine ⟨IsPSL.of_mulEquiv (SmithC27.quotCenterEquivSelf hbot).symm hPSLX, ?_, fun h3 => ?_⟩
    · rw [hbot, Subgroup.card_bot]
      exact one_dvd 3
    · rw [hbot, Subgroup.card_bot] at h3
      norm_num at h3
  ·
    letI := Fintype.ofFinite F'
    have eS : KQ K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F') := eQ.trans eA
    have hcen : Nat.card (Subgroup.center (KQ K)) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (K := F')
        (by rw [hF'] <;> norm_num)
    have hPSLX : IsPSL 3 2 2 (KQ K ⧸ Subgroup.center (KQ K)) := by
      refine IsPSL.of_mulEquiv (SmithC27.quotCenterCongr eS).symm ?_
      exact SmithC27.isPSL_statedSL_three (F := F') (n := 2) (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hF']; norm_num)
    refine ⟨hPSLX, ?_, fun _ => ?_⟩
    · rw [hcen]
    have hperf : ⁅S126.star H K, S126.star H K⁆ = S126.star H K :=
      perfect_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp)
    have hO2 : oTwoRes (⊤ : Subgroup (S126.HStar H)) = S126.star H K :=
      L1232.oTwoRes_top_eq hperf hsq
    have hstar : ∀ l (hl : l ∈ H), l ∈ Li L F.V1 →
        (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈ S126.star H K := by
      intro l hl hlL
      rw [← hO2]
      exact L1232.mk_mem_oTwoRes (le_sup_left.trans h.L₁T_le_H) hlL
    have hL1 : Li L F.V1 ≤ K ⊔ T := by
      intro l hlL
      have hlH : l ∈ H := (le_sup_left.trans h.L₁T_le_H) hlL
      obtain ⟨x, hxK, hxe⟩ := hstar l hlH hlL
      have hxK' : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hxK
      rw [QuotientGroup.mk'_apply] at hxe
      have hm : x⁻¹ * (⟨l, hlH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp hxe
      have hmP : ((x⁻¹ * (⟨l, hlH⟩ : ↥H) : ↥H) : G) ∈ pCoreOf 2 H :=
        (coe_mem_pCoreOf_iff_mem_pCore _).mpr hm
      have hT : (x : G)⁻¹ * l ∈ T := isSylowTwoOf_pCoreOf_le h.sylow_H hmP
      have := (K ⊔ T).mul_mem (Subgroup.mem_sup_left hxK') (Subgroup.mem_sup_right hT)
      simpa using this
    have hK₀ : conjClosure K T = K := c.case1.1
    have hHeq : H = conjClosure K T ⊔ (Li L F.V1 ⊔ T) := c.isHK.2.2
    have hHKT : H = K ⊔ T := by
      refine le_antisymm ?_ (sup_le hKH hTH)
      rw [hHeq, hK₀]
      exact sup_le le_sup_left (sup_le hL1 le_sup_right)
    exact ⟨hHKT, fun l hlL hl => hstar l hl hlL⟩

end CFSG.Quasithin.H13.L1232S2
