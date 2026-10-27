module

public import CFSG.Quasithin.H13.A5S132
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.H13.U3L14Set

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_reducedAggregate (X : Subgroup G) :
    IsTwoReducedIn X (reducedAggregate X) := by
  refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨map_subtype_le _, ?_⟩
  have hsub : (reducedAggregate X).subgroupOf X = primeReducedAggregate (↥X) 2 :=
    comap_map_eq_self_of_injective X.subtype_injective _
  rw [hsub]
  exact isPrimeReduced_primeReducedAggregate 2

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem inH_L2T : InH T (L₁Of L V₂ ⊔ T) := by
  have hV2T : V₂ ≤ T := S.le2V.trans S.V_T
  have hN : L₁Of L V₂ ⊔ T ≤ normalizer (V₂ : Set G) :=
    sup_le ((oTwoRes_le _).trans inf_le_right) S.v2.2.2.1
  refine ⟨le_sup_right, fun hb => ?_⟩
  have h1 := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (hV2T.trans le_sup_right) hN
    (S.isP_T.to_le hV2T)
  rw [hb, le_bot_iff] at h1
  apply S.V1_ne
  rw [eq_bot_iff, ← h1]
  exact S.le12

theorem exists_hStar_K {K : Subgroup G} (hHK : A6.g1 T V ≤ normalizer (K : Set G))
    (hL2K : ¬ L₁Of L V₂ ≤ normalizer (K : Set G)) :
    ∃ H : Subgroup G, IsHStar T (normalizer (K : Set G)) H ∧ H ≤ L₁Of L V₂ ⊔ T ∧
      ¬ H ≤ centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨H, hH, hHle⟩ := A5.exists_isHStar_le' S.inH_L2T fun h => hL2K (le_sup_left.trans h)
  refine ⟨H, hH, hHle, fun hHZ => hH.2.1 ?_⟩
  refine hHZ.trans (le_trans ?_ hHK)
  exact (centralizer_le (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)).trans
    (centralizer_le_normalizer _)

theorem reduced_K (h1332 : Stmt13_3_2) {K : Subgroup G} (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :
    ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) ∧
      T ⊓ centralizer (reducedAggregate (K ⊔ T) : Set G) = pCoreOf 2 (K ⊔ T) := by
  obtain ⟨-, -, ⟨⟨VK, hVK⟩, -⟩, -⟩ := h1332 G T L S.h13 K hfK
  have hloc := hfK.1
  have hKc : K ∈ cComp (K ⊔ T) := hloc.2.1
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hred := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hKV : ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) := by
    intro hle
    have hVKc : K ≤ centralizer (VK : Set G) := hle.trans (centralizer_le hVK.1)
    have h1 : ⁅VK, K⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVKc)
    exact hVK.2.1 (hVK.2.2.2.1.symm.trans h1)
  exact ⟨hKV, (Ch3Sec3.centralizer_reduced_of_cComp hKc hq hTsyl hred hKV).2.1⟩

theorem hyp318_K (h1332 : Stmt13_3_2) {K : Subgroup G} (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hne : ∃ H : Subgroup G, IsHStar T (normalizer (K : Set G)) H) :
    Hyp318 T (normalizer (K : Set G)) K (reducedAggregate (K ⊔ T)) := by
  obtain ⟨-, ⟨hTK, -, hMK, huniq⟩, -, -⟩ := h1332 G T L S.h13 K hfK
  have hKc : K ∈ cComp (K ⊔ T) := hfK.1.2.1
  have hred := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hcen := (S.reduced_K h1332 hfK hq).2
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  exact
    { inM := ⟨hMK, hTK⟩
      nonempty := hne
      perfect := le_antisymm (perfect_le_oTwoUpper le_rfl (Subgroup.isPerfect_iff.2 hperf))
        (oTwoUpper_le K)
      le_M := le_normalizer
      normal := le_rfl
      unique := ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := hred
      centralizer := hcen.symm }

theorem ff_K (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow) {K : Subgroup G}
    (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hHK : A6.g1 T V ≤ normalizer (K : Set G))
    (hL2K : ¬ L₁Of L V₂ ≤ normalizer (K : Set G)) :
    ¬ thompsonJ T ≤ T ⊓ centralizer (reducedAggregate (K ⊔ T) : Set G) ∧
      IsFFInt (K ⊔ T) (reducedAggregate (K ⊔ T))
        (isTwoReducedIn_reducedAggregate (K ⊔ T)).2.2.1 := by
  obtain ⟨H, hH, -, hHZ⟩ := S.exists_hStar_K hHK hL2K
  have h318 := S.hyp318_K h1332 hfK hq ⟨H, hH⟩
  rcases theorem318_three hC58 h317 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow h318
    with h | ⟨-, hZ, -⟩
  · exact h
  · exfalso
    apply hHZ
    intro x hx
    rw [mem_centralizer_iff]
    intro z hz
    exact ((mem_centralizer_iff.1 ((hZ H hH hz).2)) x hx).symm

end Set14

end CFSG.Quasithin.H13.U3
