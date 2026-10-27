module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step148PointOmegaGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, Subgroup.zpowers b ∈ omegaA A → ∀ Lb ∈ lA A b,
        Q ≤ Lb ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers b : Set G)) →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        ∃ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)), K ≤ Lb ∧
          K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
            V = ⁅V, A⁆}

namespace Item148Point

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_le_normalizer148 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h142 : Concl142 A LB) {b : G} (hbΩ : Subgroup.zpowers b ∈ omegaA A) {V : Subgroup G}
    (hVH : V ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (hV : V ∈ invariantPiSubgroups ⊤ A (piCompl 3)) : V ∈ scriptQ A LB := by
  obtain ⟨Qs, hQs, hVQs⟩ := exists_le_mem_maxInvariantPiSubgroups
    (⟨hVH, hV.2.1, hV.2.2⟩ : V ∈ invariantPiSubgroups
      (Subgroup.normalizer (Subgroup.zpowers b : Set G)) A (piCompl 3))
  exact mem_scriptQ_of_le (h142 b hbΩ Qs hQs).1 hVQs hV.2.2

theorem eq_deltaZero_of_le_sSup148 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h142 : Concl142 A LB) {b : G} (hbΩ : Subgroup.zpowers b ∈ omegaA A) {K Lb : Subgroup G}
    (hLb : Lb ∈ thetaComponentsAt 3 b) (hKLb : K ≤ Lb)
    (hK : K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
      V = ⁅V, A⁆}) :
    K = deltaZero A LB K := by
  refine le_antisymm (hK.trans (sSup_le fun V hV => ?_)) (deltaZero_le K)
  obtain ⟨hVK, hVinv, hVA⟩ := hV
  have hVH : V ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hVK.trans (hKLb.trans ((le_centralizer_of_mem_thetaComponentsAt hLb).trans
      (centralizer_singleton_le_normalizer_zpowers b)))
  exact le_deltaZero ⟨mem_scriptQ_of_le_normalizer148 h142 hbΩ hVH hVinv, hVA⟩ hVK

end Item148Point

theorem step148PointOmega_of_gen (h142 : Concl142S14) (hgen : Step148PointOmegaGen) :
    Step148PointOmega := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hbΩ Lb hLb hQLb hQb
  obtain ⟨K, hK, hKLb, hKgen⟩ :=
    hgen G A c L h Y hY hs hYB B hB Q hQ hQY b hb hbΩ Lb hLb hQLb hQb
  exact ⟨K, hK, Item148Point.eq_deltaZero_of_le_sSup148 (h142 G A c L h) hbΩ hLb.1 hKLb hKgen,
    hKLb⟩

end CFSG.RankThree.PartTwo.Sec14
