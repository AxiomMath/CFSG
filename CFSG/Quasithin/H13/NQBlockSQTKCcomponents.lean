module

public import CFSG.Quasithin.Vol2.Ch1Quotient

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def SQTKCLayerPerfectResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsSQTKCat G → CFSG.pCore 2 G = ⊥ →
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G)

section Embedding

variable {G : Type} [Group G] [Finite G]

theorem exists_le_cComp_of_cCompSpan_eq {T B : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hB : B ∈ lFamily T) (h37 : A37Statement G)
    (hEC : cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G)) :
    ∃ L ∈ cComp (⊤ : Subgroup G), B ≤ L := by
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB'
  have hBT : ⁅B, T ⊓ B⁆ = B := A312.commutator_inf_eq_self hT le_sup_right hB'
  have hBspan : B ≤ cCompSpan (⊤ : Subgroup G) := by
    rw [hEC]
    exact le_perfectCore_of_perfect le_top hperf
  have hnorm : ∀ L ∈ cComp (⊤ : Subgroup G), B ≤ Subgroup.normalizer (L : Set G) := fun L hL =>
    hBspan.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (cComp_normal_span hL).1).mp
      (cComp_normal_span hL).2)
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsolv : ∀ L ∈ cComp (⊤ : Subgroup G), Group.IsSolvable ↥⁅B, T ⊓ L⁆ := by
    intro L hL
    rcases cComp_commutator_dichotomy_of_le hB'
      (inf_le_left.trans le_sup_right : T ⊓ L ≤ B ⊔ T) with ⟨-, hs⟩ | heq
    · exact hs
    · exfalso
      apply hcon L hL
      calc B ≤ conjClosure B (T ⊓ L) := le_conjClosure _ _
        _ = ⁅B, T ⊓ L⁆ := heq.symm
        _ ≤ L := A312.commutator_le_of_le_normalizer (hnorm L hL) inf_le_right
  exact ne_bot_of_mem_cComp hB' (A312.eq_bot_of_le_sSup hT h37 hBT hperf hnorm hsolv (cComp ⊤)
    subset_rfl hBspan)

theorem exists_cComp_ge_of_lFamily_of_cCompSpan_eq {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N) (h37 : A37Statement (X ⧸ N))
    (hEC : cCompSpan (⊤ : Subgroup (X ⧸ N)) = perfectCore (⊤ : Subgroup (X ⧸ N)))
    {S B : Subgroup X} (hS : IsSylowTwoOf S ⊤) (hNS : N ≤ S) (hB : B ∈ lFamily S) :
    ∃ K ∈ cComp (⊤ : Subgroup X), B ≤ K := by
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hker : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hkerle : (QuotientGroup.mk' N).ker ≤ B ⊔ S := by
    rw [QuotientGroup.ker_mk']
    exact hNS.trans le_sup_right
  have hBbar := map_mem_cComp_of_le (QuotientGroup.mk' N) hker hkerle hB'
  rw [Subgroup.map_sup] at hBbar
  have hSbar := isSylowTwoOf_top_map_of_surjective hS (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  obtain ⟨Lbar, hLbar, hBL⟩ := exists_le_cComp_of_cCompSpan_eq hSbar hBbar h37 hEC
  obtain ⟨L, hL, rfl⟩ := (cComp_quotient_bijOn N hN).surjOn hLbar
  refine ⟨L, hL, ?_⟩
  have hBle : B ≤ L ⊔ N := by
    have := Subgroup.comap_mono (f := QuotientGroup.mk' N) hBL
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    exact le_sup_left.trans this
  have h3 := cComp_commutator_perfectCore hL le_top hN Subgroup.le_normalizer_of_normal
  rw [← h3.2]
  exact le_perfectCore_of_perfect hBle (perfect_of_mem_cComp hB')

theorem exists_cComp_ge_of_subgroup_of_cCompSpan_eq {H S B : Subgroup G}
    (hS : IsSylowTwoOf S H) (hBH : B ≤ H) (hB : B ∈ lFamily S)
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H))
    (hEC : cCompSpan (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) =
      perfectCore (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) : ∃ K ∈ cComp H, B ≤ K := by
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hBS : B ⊔ S ≤ H := sup_le hBH hS.1
  have hB'' : B.subgroupOf H ∈ lFamily (S.subgroupOf H) := by
    show B.subgroupOf H ∈ cComp (B.subgroupOf H ⊔ S.subgroupOf H)
    rw [← Subgroup.subgroupOf_sup hBH hS.1]
    exact subgroupOf_mem_cComp_of_le hBS hB'
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨K', hK', hBK'⟩ := exists_cComp_ge_of_lFamily_of_cCompSpan_eq (CFSG.pCore 2 ↥H)
    (isSolvable_pCore_two_group _) h37 hEC (isSylowTwoOf_top_subgroupOf hS)
    (pCore_two_le_subgroupOf hS) hB''
  refine ⟨K'.map H.subtype, map_subtype_mem_cComp hK', ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hBH]
  exact Subgroup.map_mono hBK'

end Embedding

end CFSG.Quasithin.H13.NQBlock
