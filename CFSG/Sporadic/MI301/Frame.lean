module

public import CFSG.Monster.GMS.Extraspecial
public import CFSG.Monster.GMS.TwoCentral
public import CFSG.Monster.GMS.Orbits
public import CFSG.Monster.NormalChain
public import CFSG.Monster.Existence.Monolith
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.Sporadic.MI301

open CFSG.Monster.GMS CFSG.LocalAnalysis.GLTheoremA.S8 Subgroup

variable {G : Type} [Group G] {z : G}

theorem isExtraSpec2_leechQ (h : GMSLeechCentralizer z) : IsExtraSpec2 (leechQ z) := by
  have h1 : CFSG.Open.timmesfeldIsExtraspecial ↥(CFSG.pCore 2 (centralizer ({z} : Set G))) :=
    (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2 h.2.1
  unfold IsExtraSpec2 leechQ
  exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (centralizer ({z} : Set G)).subtype_injective) h1

theorem leech_hR (h : GMSLeechCentralizer z) :
    IsExtraSpec2 (leechQ z) ∧ Nat.card (leechQ z) = 2 ^ 25 :=
  ⟨isExtraSpec2_leechQ h, h.card_leechQ⟩

private theorem map_center_map_subtype {C : Subgroup G} (P : Subgroup C) :
    (center ↥(P.map C.subtype)).map (P.map C.subtype).subtype =
      ((center ↥P).map P.subtype).map C.subtype := by
  ext x
  rw [CFSG.Monster.mem_map_center_iff]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hx⟩
    refine ⟨c, CFSG.Monster.mem_map_center_iff.2 ⟨hc, fun y hy => Subtype.ext ?_⟩, rfl⟩
    exact hx _ ⟨y, hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hcP, hcc⟩ := CFSG.Monster.mem_map_center_iff.1 hc
    refine ⟨⟨c, hcP, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcc y hy)

theorem centerOf_leechQ (h : GMSLeechCentralizer z) : centerOf (leechQ z) = zpowers z := by
  obtain ⟨hz, hQ, -, -, hcon⟩ := h
  unfold centerOf leechQ
  rw [map_center_map_subtype]
  exact center_pCore_map_eq_zpowers hz hQ hcon

theorem normalizer_leechQ (h : GMSLeechCentralizer z) :
    normalizer (leechQ z : Set G) = centralizer ({z} : Set G) := by
  apply le_antisymm
  · have hc := centerOf_leechQ h
    unfold centerOf at hc
    exact CFSG.Monster.Existence.normalizer_le_centralizer_of_center h.1 hc
  · intro g hg
    rw [mem_normalizer_iff]
    intro q
    refine ⟨conj_mem_leechQ hg, fun hq => ?_⟩
    have h1 := conj_mem_leechQ ((centralizer ({z} : Set G)).inv_mem hg) hq
    simpa [mul_assoc] using h1

end CFSG.Sporadic.MI301
