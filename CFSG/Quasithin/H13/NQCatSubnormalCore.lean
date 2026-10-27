module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup

theorem map_pCore_le_pCore_of_isSubnormal' {H : Type*} [Group H] {p : ℕ} {X : Subgroup H}
    (hX : X.IsSubnormal) : (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [mem_subgroupOf] at hl ⊢
        have hN := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (CFSG.pCore p X) (hYN y.2)
        simpa using (mem_normalizer_iff.mp hN _).mp hl
      · exact (CFSG.pCore_isPGroup.map X.subtype).of_equiv (subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => ?_⟩, CFSG.pCore_isPGroup.map _⟩
    have hg : g ∈ normalizer ((⊤ : Subgroup H) : Set H) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top g
    have hN := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore p (⊤ : Subgroup H)) hg
    exact (mem_normalizer_iff.mp hN l).mp hl
  | step X Y hXY _ hN ih =>
    exact (key hXY ((normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

end CFSG.Quasithin.H13.NQCat
