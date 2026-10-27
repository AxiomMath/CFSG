module

public import CFSG.LocalAnalysis.StandardType.GGFusionExceptionFullHardComps
public import CFSG.LocalAnalysis.StandardType.GGSixNotExcVacuous
public import CFSG.LocalAnalysis.StandardType.GGRootFactorOrdersIdent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLiftKV
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLiftY

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Count

variable {A B : Type} [Group A] [Group B] [Finite B]

theorem ncard_compOrdSet_le_of_injOn (F : Subgroup A → Subgroup B)
    (hinj : Set.InjOn F {C | CFSG.Open.IsComponentOf C ⊤})
    (hF : ∀ C, CFSG.Open.IsComponentOf C ⊤ → CFSG.Open.IsComponentOf (F C) ⊤ ∧
      Nonempty (↥(F C) ⧸ Subgroup.center ↥(F C) ≃* ↥C ⧸ Subgroup.center ↥C)) (N : ℕ) :
    (CFSG.LieType.ChevTwo.compOrdSet A N).ncard ≤
      (CFSG.LieType.ChevTwo.compOrdSet B N).ncard := by
  refine Set.ncard_le_ncard_of_injOn F ?_ ?_ (CFSG.LieType.ChevTwo.compOrdSet_finite N)
  · intro C hC
    rw [CFSG.LieType.ChevTwo.mem_compOrdSet] at hC ⊢
    obtain ⟨hcomp, hcard⟩ := hC
    refine ⟨(hF C hcomp).1, ?_⟩
    obtain ⟨e⟩ := (hF C hcomp).2
    rw [Nat.card_congr e.toEquiv, hcard]
  · exact hinj.mono fun C hC => (CFSG.LieType.ChevTwo.mem_compOrdSet.mp hC).1

theorem two_le_ncard_compOrdSet {N : ℕ} {C₁ C₂ : Subgroup A} [Finite A] (hne : C₁ ≠ C₂)
    (h₁ : CFSG.Open.IsComponentOf C₁ ⊤) (h₂ : CFSG.Open.IsComponentOf C₂ ⊤)
    (hcard₁ : Nat.card (↥C₁ ⧸ Subgroup.center ↥C₁) = N)
    (hcard₂ : Nat.card (↥C₂ ⧸ Subgroup.center ↥C₂) = N) :
    2 ≤ (CFSG.LieType.ChevTwo.compOrdSet A N).ncard := by
  have hsub : ({C₁, C₂} : Set (Subgroup A)) ⊆ CFSG.LieType.ChevTwo.compOrdSet A N := by
    intro C hC
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact CFSG.LieType.ChevTwo.mem_compOrdSet.mpr ⟨h₁, hcard₁⟩
    · exact CFSG.LieType.ChevTwo.mem_compOrdSet.mpr ⟨h₂, hcard₂⟩
  calc 2 = ({C₁, C₂} : Set (Subgroup A)).ncard := (Set.ncard_pair hne).symm
    _ ≤ (CFSG.LieType.ChevTwo.compOrdSet A N).ncard :=
        Set.ncard_le_ncard hsub (CFSG.LieType.ChevTwo.compOrdSet_finite N)

theorem one_le_ncard_compOrdSet {N : ℕ} {C : Subgroup A} [Finite A]
    (hC : CFSG.Open.IsComponentOf C ⊤)
    (hcard : Nat.card (↥C ⧸ Subgroup.center ↥C) = N) :
    1 ≤ (CFSG.LieType.ChevTwo.compOrdSet A N).ncard := by
  have hsub : ({C} : Set (Subgroup A)) ⊆ CFSG.LieType.ChevTwo.compOrdSet A N := by
    intro C' hC'
    rw [Set.mem_singleton_iff] at hC'
    subst hC'
    exact CFSG.LieType.ChevTwo.mem_compOrdSet.mpr ⟨hC, hcard⟩
  calc 1 = ({C} : Set (Subgroup A)).ncard := (Set.ncard_singleton C).symm
    _ ≤ (CFSG.LieType.ChevTwo.compOrdSet A N).ncard :=
        Set.ncard_le_ncard hsub (CFSG.LieType.ChevTwo.compOrdSet_finite N)

end Count

section Inputs

theorem ggSix_false_of_count_sixty {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {o : List ℕ}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 5)
    (ho : o ∈ ggRootFactorOrders t n f) (h : 2 ≤ o.count 60) : False := by
  rcases ggRootFactorOrders_two_le_count_sixty ho h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ggSix_false_of_spSixFour hctx s1 hp
  · exact ggSix_false_of_plusFourFour hctx s1 hp

theorem ggSix_false_of_mem_360 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {o : List ℕ}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 3)
    (ho : o ∈ ggRootFactorOrders t n f) (h : 360 ∈ o) : False := by
  obtain ⟨rfl, hn, rfl⟩ := ggRootFactorOrders_mem_360 ho h
  exact ggSix_false_of_spTwoThree hn hctx s1 hp

theorem ggSix_false_of_mem_174182400 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {o : List ℕ}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 5)
    (ho : o ∈ ggRootFactorOrders t n f) (h : 174182400 ∈ o) : False := by
  obtain ⟨rfl, rfl, rfl⟩ := ggRootFactorOrders_mem_174182400 ho h
  exact ggSix_false_of_plusSixTwo hctx s1 hp

theorem ggSixRootCent_exists_count_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {E : Subgroup G} {r : G}
    (hcount : GGRootInvolCountTag t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J)
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    ∃ o ∈ ggRootFactorOrders t n f, GGInvolCentTypedBy (ggG0 p B x L D J) r o := by
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -⟩ := hctx.2.2.2.1, hctx.2.2.2.2.1, hctx.2.2.2.2.2.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  obtain ⟨o, ho, htyped⟩ := hcount G n f ψ hadm hrk hker hC r hch.rootInvolution
  exact ⟨o, ho, hrange ▸ htyped⟩

theorem ggSixSchreier_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hSP : GGSchreierPerfectInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) :
    ∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → ⁅P, P⁆ = P →
      P ≤ ggG0 p B x L D J := by
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, -, -, -⟩ := hctx.2
  have hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) := by
    rw [s1.1, Subgroup.card_bot]
    exact odd_one
  exact fun P hP hPP =>
    hSP G t n f ψ _ ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf0, hmodel⟩ hodd P hP hPP

noncomputable abbrev ggRCSEt {X : Type} [Group X] (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) :=
  (E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))

private theorem ggRCSImg_commute {G : Type} [Group G] {r : G} {E : Subgroup G}
    (hE : IsMulCommutative ↥E) {a b : GGRCSNbar r}
    (ha : a ∈ ggRCSImg r E) (hb : b ∈ ggRCSImg r E) : Commute a b := by
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
  have hvalG : (a₀ : G) * (b₀ : G) = (b₀ : G) * (a₀ : G) :=
    congrArg Subtype.val (hE.is_comm.comm ⟨(a₀ : G), ha₀⟩ ⟨(b₀ : G), hb₀⟩)
  have hval : a₀ * b₀ = b₀ * a₀ := Subtype.ext hvalG
  have hmap : QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))
        a₀ * QuotientGroup.mk' _ b₀ =
      QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))
        b₀ * QuotientGroup.mk' _ a₀ := by
    simpa only [map_mul] using congrArg
      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))) hval
  exact hmap

noncomputable abbrev ggRCSWt {X : Type} [Group X] (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] : Type :=
  ↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)

theorem ggRCS_exists_componentInj_six {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {E : Subgroup G} {r : G} {K S : Subgroup (GGRCSNbar r)}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hSch : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → ⁅P, P⁆ = P →
      P ≤ ggG0 p B x L D J)
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r)
    (hset : GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S)
    [((ggRCSU (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K).subgroupOf
        (ggRCSImg r E ⊔ K)).Normal] :
    ∃ F : Subgroup ↥(ggRCSHK (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K) →
        Subgroup (GGInvolCentBar (ggG0 p B x L D J) r),
      Set.InjOn F {C | CFSG.Open.IsComponentOf C ⊤} ∧
      ∀ C, CFSG.Open.IsComponentOf C ⊤ → CFSG.Open.IsComponentOf (F C) ⊤ ∧
        Nonempty (↥(F C) ⧸ Subgroup.center ↥(F C) ≃* ↥C ⧸ Subgroup.center ↥C) := by
  have hEs : Group.IsSolvable ↥(ggRCSImg r E) :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext (ggRCSImg_commute hch.2.1.1 a.2 b.2).eq
  have hEM : E ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    hch.1.trans hctx.2.2.2.2.2.2.1.1
  have hEV : ggRCSImg r E ≤
      ggRCSImg r (Subgroup.normalizer (ggG0 p B x L D J : Set G)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hEM)
  have hEK : ggRCSImg r E ≤ Subgroup.normalizer (K : Set (GGRCSNbar r)) := hset.2.2.1
  obtain ⟨FA, hinjA, hFA⟩ :=
    ggRCS_hk_componentInj_kv
      (V := ggRCSImg r (Subgroup.normalizer (ggG0 p B x L D J : Set G)))
      (E := ggRCSImg r E) (K := K) hEs hEV hEK
  obtain ⟨FB, hinjB, hFB⟩ :=
    ggRCS_kv_componentInj_bar (G₀ := ggG0 p B x L D J) (r := r) (K := K) hSch hset.1.2
  refine ⟨fun C => FB (FA C), ?_, ?_⟩
  · intro C₁ hC₁ C₂ hC₂ hEq
    exact hinjA hC₁ hC₂ (hinjB (hFA C₁ hC₁).1 (hFA C₂ hC₂).1 hEq)
  · intro C hC
    have hFBc := hFB (FA C) (hFA C hC).1
    exact ⟨hFBc.1, hFBc.2.elim fun e₁ => (hFA C hC).2.elim fun e₂ => ⟨e₁.trans e₂⟩⟩

end Inputs

end CFSG.StandardType
