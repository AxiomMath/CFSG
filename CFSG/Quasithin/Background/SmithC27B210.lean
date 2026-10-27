module

public import CFSG.Quasithin.Background.SmithC27Star
public import CFSG.Quasithin.Background.SmithC27Two

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem not_thompsonJ_le_centralizer (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) := by
  intro hJ
  apply h.not_le
  apply h.le_of_thompsonJ_le
  rw [hs.pCore_eq_inf]
  exact le_inf (thompsonJ_le_self R) hJ

theorem stable_branch (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V) :
    IsStableFF (autI hV (K ⊔ R)) (C124.offenderImagesConjIn hV (K ⊔ R) R) ∧
      ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R)) ≤ ffJ (autI hV (K ⊔ R)) ∧
      quasithinGenFitting (ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R))) =
        autI hV K := by
  have hJ := not_thompsonJ_le_centralizer h hs
  have hVR : V ≤ R := (C124.le_pCoreOf_of_reduced hs.red).trans hs.core
  obtain ⟨T, hT, hRT⟩ := hs.exists_sylow
  obtain ⟨hstab, hle⟩ := C124.B2_10_1_stable_in hV hs.le_normalizer_V le_sup_right hVR hJ
  exact ⟨hstab, hle, C124.genFitting_ffJP_eq hV hs.red hT hs.core hRT hJ le_sup_left
    hs.le_normalizer (hs.prod_of_le hRT) hs.commutator_ne_bot (Or.inl hs.quasi)⟩

end CFSG.Quasithin.SmithC27
