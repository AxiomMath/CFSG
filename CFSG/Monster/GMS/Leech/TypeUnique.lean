module

public import CFSG.Monster.GMS.Leech.TypeUniqueCover
public import CFSG.Monster.GMS.F1Basic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem leechTypeUniqueness_of
    (h13 : Co1ModuleUniqueness)
    (hDC : Co1DoubleCoverTwoB) :
    LeechTypeUniqueness := by
  intro G G' _ _ _ _ z z' hz hz' φ φ' hφs hφk hφs' hφk' h2B h2B'
  obtain ⟨L, hL⟩ := exists_leechSystem_of_hom h13 hz φ hφs hφk
  obtain ⟨L', hL'⟩ := exists_leechSystem_of_hom h13 hz' φ' hφs' hφk'
  subst hL hL'
  obtain ⟨glue⟩ := TypeUnique.exists_glue L.toTypeSystem L'.toTypeSystem
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({z'} : Set G')) := by
    rw [hz.card_centralizer, hz'.card_centralizer]
  refine TypeUnique.exists_mulEquiv hDC glue ?_ ?_ hcard
  · intro t ht
    exact h2B t ht
  · intro t ht
    exact h2B' t ht

end CFSG.Monster.GMS
