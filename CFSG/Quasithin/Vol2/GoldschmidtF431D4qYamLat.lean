module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6

theorem isCoatom_of_overgroups_four {G : Type*} [Group G] {N P Q : Subgroup G} (hNP : N ≤ P)
    (hQP : ¬ Q ≤ P) (hlat : ∀ A : Subgroup G, N ≤ A → A = N ∨ A = P ∨ A = Q ∨ A = ⊤)
    (hPQ : ¬ P ≤ Q) : IsCoatom P := by
  refine ⟨fun htop => hQP (htop ▸ le_top), fun A hA => ?_⟩
  rcases hlat A (hNP.trans hA.le) with h | h | h | h
  · exact absurd (h ▸ hNP) (not_le_of_gt hA)
  · exact absurd h hA.ne'
  · exact absurd (h ▸ hA.le) hPQ
  · exact h


variable {K : Type} [Field K] (σ : K ≃+* K)

theorem d4_normalizer_eq :
    Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  rw [normalizer_subgroupOf_eq' (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _),
    (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1]

theorem d4_borel_overgroups (A : Subgroup (ModGL TwistTag.D4.tag K))
    (hB : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ A)
    (hA : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    A = graphFixedRootBorel TwistTag.D4 K σ.toRingHom ∨
      A = graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨0, by decide⟩} ∨
      A = graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} ∨
      A = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hAJ := eq_graphFixedParabolic_of_le σ.surjective hB hA
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection a) ∈ A} with hJ
  by_cases h0 : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J <;>
    by_cases h1 : (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J
  · right; right; right
    refine le_antisymm hA ?_
    rw [graphFixedRootGroup_eq_sup_closure σ.surjective]
    refine sup_le hB ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨a, rfl⟩
    rcases foldedRank_D4_cases a with rfl | rfl
    · exact h0
    · exact h1
  · right; left
    rw [hAJ]
    congr 1
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl <;> simp [h0, h1]
  · right; right; left
    rw [hAJ]
    congr 1
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl <;> simp [h0, h1]
  · left
    rw [hAJ, ← graphFixedParabolic_empty (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)]
    congr 1
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl <;> simp [h0, h1]

theorem d4_overgroups_normalizer (A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hA : Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ A) :
    A = Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∨
      A = (graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨0, by decide⟩}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∨
      A = (graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∨ A = ⊤ := by
  have hN := d4_normalizer_eq σ
  have hAeq : A = (A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective A).symm
  have hB : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (graphFixedRootBorel_le _ _ _), ← hN]
    exact Subgroup.map_mono hA
  rcases d4_borel_overgroups σ _ hB (Subgroup.map_subtype_le A) with h | h | h | h
  · exact Or.inl (hAeq.trans (by rw [h, hN]))
  · exact Or.inr (Or.inl (hAeq.trans (by rw [h])))
  · exact Or.inr (Or.inr (Or.inl (hAeq.trans (by rw [h]))))
  · exact Or.inr (Or.inr (Or.inr (hAeq.trans (by rw [h]; exact Subgroup.subgroupOf_self _))))

end CFSG.Quasithin.H13.F431.D4q.Hex
