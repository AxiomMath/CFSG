module

public import CFSG.Quasithin.H13.L32A510
public import CFSG.Quasithin.H13.L32A512P
public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_of_map_eq_bot {I K : Subgroup G} (hKI : K ≤ I) (hQK : pCoreOf 2 I ≤ K)
    (hS : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I))
    (h : pCoreOf 2 ((K.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) = ⊥) :
    pCoreOf 2 K = pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 hQK
    (fun k hk => le_normalizer_pCoreOf 2 I (hKI hk)) (pCoreOf_isPGroup 2 I))
  have hPK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hP2 : IsPGroup 2 ((pCoreOf 2 K).subgroupOf I) :=
    (pCoreOf_isPGroup 2 K).of_equiv (Subgroup.subgroupOfEquivOfLe (hPK.trans hKI)).symm
  have himg : ((pCoreOf 2 K).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ≤
      pCoreOf 2 ((K.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
    refine le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPK (Subgroup.mem_subgroupOf.mp hx))) ?_ (hP2.map _)
    refine le_trans ?_ (Subgroup.le_normalizer_map _)
    refine Subgroup.map_mono fun k hk => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 K (Subgroup.mem_subgroupOf.mp hk)) x
    simpa using this
  rw [h] at himg
  have hle : (pCoreOf 2 K).subgroupOf I ≤ CFSG.pPrimeCore 3 ↥I := by
    intro x hx
    have h1 := himg ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at h1
    have h2 : x ∈ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)).ker := h1
    rwa [QuotientGroup.ker_mk'] at h2
  have : (Open.pCore 2 ↥I).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hsup := hS.eq_of_le le_sup_right (sup_le hle hS.1) (hP2.to_sup_of_normal_right hS.2.1)
  have hle2 : (pCoreOf 2 K).subgroupOf I ≤ Open.pCore 2 ↥I := by
    rw [← hsup]
    exact le_sup_left
  intro p hp
  exact ⟨⟨p, hKI (hPK hp)⟩, hle2 (Subgroup.mem_subgroupOf.mpr hp), rfl⟩

namespace T53

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem lemma14_5_12 (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (hsolv : Group.IsSolvable ↥(hY T L V₂ Y))
    (hO3 : (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)).map (hY T L V₂ Y).subtype ≤
      Subgroup.centralizer (vH T L V V₂ Y : Set G))
    (h1 : Lemma14_5_12CaseOne) :
    pCoreOf 2 (xL L V₂ ⊔ T) ≠ pCoreOf 2 (Y ⊔ T) ∧
      F6.IsF618CaseTwo (↥(hY T L V₂ Y) ⧸ CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)) := by
  have hGI : F6.IsGoldschmidtTripleIn (hY T L V₂ Y) (xL L V₂ ⊔ T) (Y ⊔ T) := C.goldschmidt h4
  have hcase := h1 G T L V V₂ Y C (C.quot_xT h4).1 (C.inf_eq h4) hQ hsolv
    (C.thompsonJ_le_centralizer h4 hQ hsolv) (C.xL_eq_commutator h4 hQ hsolv) hO3
  rcases hGI.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, hsup, -⟩
  swap
  ·
    exfalso
    apply C.not_le_normalizer
    have hCn : hY T L V₂ Y ≤ Subgroup.normalizer (cH T L V V₂ Y : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        le_normalizer_centralizer_vH le_rfl hg⟩
    have hH : hY T L V₂ Y ≤ (xL L V₂ ⊔ T) ⊔ cH T L V V₂ Y := by
      intro h hh
      have h2 : (⟨h, hh⟩ : ↥(hY T L V₂ Y)) ∈ (xL L V₂ ⊔ T).subgroupOf (hY T L V₂ Y) ⊔
          CFSG.pPrimeCore 3 ↥(hY T L V₂ Y) := by
        rw [hsup]
        exact Subgroup.mem_top _
      have h3 := Subgroup.mem_map_of_mem (hY T L V₂ Y).subtype h2
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at h3
      exact sup_le_sup inf_le_left (le_inf (Subgroup.map_subtype_le _) hO3) h3
    refine le_trans (le_sup_right.trans le_sup_left) (hH.trans ?_)
    refine sup_le (sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => ?_)
      (le_sup_right.trans Subgroup.le_normalizer)
    exact F6.mem_normalizer_sup (C.T_le_normalizer_xL ht)
      (hCn ((le_sup_right : T ≤ hY T L V₂ Y) ht))
  have hne : pCoreOf 2 (xL L V₂ ⊔ T) ≠ pCoreOf 2 (Y ⊔ T) := hcase hA
  refine ⟨hne, ?_⟩
  have hX3 : Open.pRank 3 (⊤ : Subgroup ↥(hY T L V₂ Y)) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
  obtain ⟨hO3', hm3⟩ := F6.pPrimeCore_eq_bot_and_pRank_le hX3 (MulEquiv.refl _)
  have : Group.IsSolvable ↥(hY T L V₂ Y) := hsolv
  rcases F6.f618_trichotomy hA.toIsGoldschmidtTriple hO3' hm3 with
    (hc1 | hc2) | ⟨-, K, hK, -, -⟩ | ⟨-, hqs⟩
  ·
    exfalso
    apply hne
    have hS := hGI.isSylowTwoOf_pCore_pPrimeCore
    have hQT : pCoreOf 2 (hY T L V₂ Y) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
    rw [pCoreOf_eq_of_map_eq_bot (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (hQT.trans le_sup_right) hS hc1.2.1,
      pCoreOf_eq_of_map_eq_bot (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        (hQT.trans le_sup_right) hS hc1.2.2.1]
  · exact hc2
  · exact (CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK.1
      inferInstance).elim
  · exact (CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hqs
      inferInstance).elim

end Ctx

end T53

end CFSG.Quasithin.H13.L32A
