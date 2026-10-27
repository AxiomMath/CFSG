module

public import CFSG.Quasithin.EmptyFaithful.S151NotFF
public import CFSG.Quasithin.EmptyFaithful.S152ObsF7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def StageLemma15111One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      V154 T Mc M ≤ pCoreOf 2 H

theorem not_isFFModule_of_lemma1518_151b {T Mc M : Subgroup G} (hV : IsElemAbelian 2 (V154 T Mc M))
    (h : Lemma1518Concl T Mc M) :
    ¬ @IsFFModule (V154 T Mc M) (commGroupOfElemAbelian hV) (autOn M (V154 T Mc M)) :=
  CFSG.Quasithin.S151.not_isFFModule_of_lemma1518 hV h

theorem isElemAbelian_conjClosure_of_le_pCore151b {T Mc M : Subgroup G} (hs : Setting152 T Mc M)
    (h1518 : Lemma1518Concl T Mc M) (h1519 : Lemma1519Concl T Mc M) {H : Subgroup G}
    (hH : IsHStar T M H) (hVH : V154 T Mc M ≤ pCoreOf 2 H) :
    IsElemAbelian 2 (conjClosure (V154 T Mc M) H) := by
  have hyp := amalgamHypV_normalizer hs hH h1519
  have hFF : ¬ @IsFFModule (V154 T Mc M) (commGroupOfElemAbelian hyp.elemAbelian)
      (autOn (M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G))
        (V154 T Mc M)) := by
    rw [h1519.six_autOn]
    exact not_isFFModule_of_lemma1518_151b hyp.elemAbelian h1518
  exact CosetGeom.isElemAbelian_conjClosure_of_not_isFFModule hyp (V154_ne_bot hs.qtfe) hVH hFF

theorem stageLemma15111_of_one (h1518 : StageLemma1518) (h1519 : StageLemma1519)
    (h1 : StageLemma15111One) : StageLemma15111 := by
  intro G _ _ T Mc M h hM hCE H hH
  have hVH := h1 G T Mc M h hM hCE H hH
  exact ⟨hVH, isElemAbelian_conjClosure_of_le_pCore151b ⟨h, hM, hCE⟩
    (h1518 G T Mc M h hM hCE) (h1519 G T Mc M h hM hCE) hH hVH⟩

end CFSG.Quasithin
