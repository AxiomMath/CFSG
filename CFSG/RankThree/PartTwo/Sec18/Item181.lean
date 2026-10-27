module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem rank3II_18_1_1_of (h444 : Sec4.Item4_44_1) : Item181_1 := by
  intro G _ _ A M h X hAX hX hO
  have hXM : X ⊓ M ≠ X := fun heq => hO (by rw [heq])
  have hctx := ctx444_subgroupOf h hAX hX hXM
  set M' := (X ⊓ M).subgroupOf X with hM'
  have hmap : inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M) =
      (inSubgroup (CFSG.pPrimeCore 3) M').map X.subtype := by
    rw [← inSubgroup_pPrimeCore_map X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hO' : CFSG.pPrimeCore 3 X ≠ inSubgroup (CFSG.pPrimeCore 3) M' := by
    intro heq
    apply hO
    rw [hmap, ← heq]
    rfl
  obtain ⟨L', hL', S, hS⟩ := h444 X (A.subgroupOf X) M' hctx hO'
  set S' : Subgroup X := (S : Subgroup _).map (inSubgroup (CFSG.pPrimeCore 3) M').subtype
  refine ⟨L'.map X.subtype, ⟨L', hL', rfl⟩, S'.map X.subtype, ?_, ?_⟩
  · rw [hmap]
    exact IsSylowOf.map_of_injective X.subtype_injective ⟨S, rfl⟩
  · have hmem := mem_scriptH_of_subgroupOf hAX hX hS
    rwa [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAX,
      sup_comm A] at hmem

omit [Finite G] in
theorem le_of_mem_scriptH₀ {A M H : Subgroup G} (hH : H ∈ scriptH₀ A M) : A ≤ H := by
  rw [hH.1]
  exact le_sup_left.trans' le_sup_right

omit [Finite G] in
theorem inf_ne_of_mem_scriptH₀ {A M H : Subgroup G} (hH : H ∈ scriptH₀ A M) : H ⊓ M ≠ H :=
  fun heq => hH.2.2 (by rw [heq])

omit [Finite G] in
theorem ne_top_of_mem_scriptH {A M H : Subgroup G} (hH : H ∈ scriptH A M) : H ≠ ⊤ :=
  hH.1

omit [Finite G] in
theorem map_subtype_top (H : Subgroup G) : (⊤ : Subgroup H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite G] in
theorem top_mem_scriptH₀_subgroupOf {A M H : Subgroup G} (hH : H ∈ scriptH₀ A M) :
    (⊤ : Subgroup H) ∈ scriptH₀ (A.subgroupOf H) ((H ⊓ M).subgroupOf H) := by
  rw [← map_mem_scriptH₀_iff H.subtype H.subtype_injective, map_subtype_top,
    Subgroup.map_subgroupOf_eq_of_le (le_of_mem_scriptH₀ hH),
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hinf : H ⊓ (H ⊓ M) = H ⊓ M := by rw [← inf_assoc, inf_idem]
  rw [mem_scriptH₀_iff, hinf]
  exact hH

theorem isHeisSLThreeFour_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Sec4.IsHeisSLThreeFour X) : Sec4.IsHeisSLThreeFour Y := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := h
  refine ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hUV, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hcomm u hu v hv]
  · exact Sec13.isHeisThree_of_mulEquiv (U.equivMapOfInjective _ e.injective) hU
  · exact ⟨(V.equivMapOfInjective _ e.injective).symm.trans eV⟩
  · rw [← Subgroup.map_inf_eq U V e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective, hcard]

theorem isZ3L34OrHeisSL34_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Sec4.IsZ3L34OrHeisSL34 X) : Sec4.IsZ3L34OrHeisSL34 Y := by
  rcases h with h | h
  · obtain ⟨φ⟩ := h
    exact Or.inl ⟨e.symm.trans φ⟩
  · exact Or.inr (isHeisSLThreeFour_of_mulEquiv e h)

theorem concl4442_of_subgroupOf {A M H : Subgroup G} (hAH : A ≤ H) {s : H}
    (hs : Sec4.Concl4442 (A.subgroupOf H) ((H ⊓ M).subgroupOf H) ⊤ s) :
    Sec4.Concl4442 A M H (s : G) := by
  obtain ⟨hsO, hsC, hkind, hs', X, hXn, hX, hXs, hsX⟩ := hs
  refine ⟨?_, ?_, ?_, s.2, ?_⟩
  ·
    have h1 := Subgroup.mem_map_of_mem H.subtype hsO
    rwa [← pCoreOf_map H.subtype H.subtype_injective, top_inf_eq,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp hsC ⟨a, hAH ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  ·
    have h1 := Sec13.inducesStdKind_sub H (inSubgroup perfectResidual (⊤ : Subgroup H)) hkind
    rwa [← inSubgroup_perfectResidual_map H.subtype H.subtype_injective, map_subtype_top] at h1
  ·
    set e : (⊤ : Subgroup H) ≃* H := Subgroup.topEquiv
    set φ : (⊤ : Subgroup H) ⧸ CFSG.pCore 2 (⊤ : Subgroup H) ≃* H ⧸ CFSG.pCore 2 H :=
      QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
    have hφs : φ (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup H)) ⟨s, trivial⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 H) ⟨(s : G), s.2⟩ := rfl
    refine ⟨X.map φ.toMonoidHom, hXn.map _ φ.surjective,
      isZ3L34OrHeisSL34_of_mulEquiv (X.equivMapOfInjective _ φ.injective) hX, ?_, ?_⟩
    · have hz : Subgroup.zpowers (φ (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup H))
          ⟨s, trivial⟩)) = (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup H))
          ⟨s, hs'⟩)).map φ.toMonoidHom :=
        (MonoidHom.map_zpowers φ.toMonoidHom
          (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup H)) ⟨s, hs'⟩)).symm
      rw [← hφs, hz, ← Subgroup.map_sup, hXs]
      exact Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective
    · rw [← hφs]
      rintro ⟨y, hy, hyφ⟩
      exact hsX (φ.injective hyφ ▸ hy)

theorem exists_concl4442_of (h444 : Sec4.Item4_44_2) {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) : ∃ s : G, Sec4.Concl4442 A M H s := by
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hctx := ctx444_subgroupOf h hAH hH.1 (inf_ne_of_mem_scriptH₀ hH₀)
  obtain ⟨s, hs⟩ := h444 H (A.subgroupOf H) ((H ⊓ M).subgroupOf H) hctx
    (top_mem_scriptH₀_subgroupOf hH₀)
  exact ⟨s, concl4442_of_subgroupOf hAH hs⟩

end CFSG.RankThree.PartTwo.Sec18
