module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8Four

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem lemma_14_2_4 (h : Hyp1421 G T M) (f : Facts1422 T M) :
    Hyp1281Two G T M (yOfL22 T M) :=
  h.hyp1281Two f.unique f.centralizer_yT f.sThree

theorem normalizer_omegaOneCenter_eq_mcOf (h : Hyp1421 G T M) :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = mcOf T :=
  le_antisymm (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
    (Subgroup.centralizer_le_normalizer _)

theorem lemma_14_2_5 (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G} :
    IsHz T M (yOfL22 T M) H ↔ InH T H ∧ ¬ H ≤ M := by
  rw [(lemma_14_2_4 h f).isHz_iff, normalizer_omegaOneCenter_eq_mcOf h]
  exact ⟨fun hH => ⟨hH.1, hH.2.2⟩, fun hH =>
    ⟨hH.1, (h.isUniqueM_centralizer hH.1 hH.2).1.2, hH.2⟩⟩

theorem lemma_14_2_6_one (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ M) :
    AlmostSpecialHyp (VZ T M) (quasithinOmegaOneCenter T) (yOfL22 T M) T H :=
  (lemma_14_2_4 h f).almostSpecialHyp ((lemma_14_2_5 h f).mpr ⟨hH, hHM⟩)

theorem lemma_14_2_6_two (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ M) :
    tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) ≤
        omegaOneCenterOf (tildeOf (quasithinOmegaOneCenter T) (pCoreOf 2 H)) ∧
      IsTwoReducedIn (tildeOf (quasithinOmegaOneCenter T) H)
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H)) :=
  (lemma_14_2_4 h f).lemma_12_8_4_two ((lemma_14_2_5 h f).mpr ⟨hH, hHM⟩)

theorem lemma_14_2_6_three (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G}
    (hH : InH T H) (hHM : ¬ H ≤ M) :
    frattiniOf (conjClosure (VZ T M) H) ≤ quasithinOmegaOneCenter T :=
  (lemma_14_2_4 h f).lemma_12_8_4_three ((lemma_14_2_5 h f).mpr ⟨hH, hHM⟩)

theorem lemma_14_2_6_four (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ M) :
    centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
  (lemma_14_2_4 h f).lemma_12_8_4_four ((lemma_14_2_5 h f).mpr ⟨hH, hHM⟩)

end CFSG.Quasithin
