module

public import CFSG.Quasithin.EmptyFaithful.S153G93SplitA
public import CFSG.Quasithin.Background.F918L2
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin

namespace S153G93

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem isQuotientOfSQTKTC_of_cat {X : Type} [Group X] (h : G64.IsQuotientOfSQTKCat X) :
    IsQuotientOfSQTKTC X := by
  obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := h
  exact ⟨Y, inferInstance, inferInstance,
    fun p hp hp2 => CFSG.SectionRank.isStronglyQuasithin_iff.mp hY.1 p hp hp2, hY.2,
    e.symm.toMonoidHom.comp (QuotientGroup.mk' N),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)⟩

private theorem map_map_conj {A B : Type*} [Group A] [Group B] (φ : A →* B) (t : A)
    (L : Subgroup A) :
    (L.map (MulAut.conj t).toMonoidHom).map φ =
      (L.map φ).map (MulAut.conj (φ t)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem exists_split_of_a38 (h38 : A38ForSQTKCat) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuotientOfSQTKTC Q) (hO2 : CFSG.pCore 2 Q = ⊥) {K : Subgroup Q} (hKn : K.Normal)
    (hK1 : K ≠ ⊥) (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ K → M = ⊥ ∨ M = K)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) :
    ∃ N : Subgroup Q, CFSG.IsComponent N ∧ N ≤ K ∧
      (K = N ∨ ∃ g : Q, N.map (MulAut.conj g).toMonoidHom ≠ N ∧
        CFSG.IsComponent (N.map (MulAut.conj g).toMonoidHom) ∧
        K = N ⊔ N.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨N, hNc, hNK, hNcl⟩ := exists_component_conjClosure_eq hKn hK1 hmin hnc
  refine ⟨N, hNc, hNK, ?_⟩
  have hNcomp : N ∈ cComp (⊤ : Subgroup Q) := mem_cComp_top_of_isComponent hNc
  obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hQ hO2 hNcomp
  rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨-, t, -, -, -, hcl⟩
  ·
    left
    have hNn : N.Normal := hmap ▸ hN.map φ hφ
    rcases hmin N hNn hNK with h | h
    · exact absurd h (ne_bot_of_mem_cComp hNcomp)
    · exact h.symm
  ·
    have hKeq : K = N ⊔ N.map (MulAut.conj (φ t)).toMonoidHom := by
      have h1 := congrArg (Subgroup.map φ) hcl
      rw [A3.map_conjClosure, hmap, Subgroup.map_top_of_surjective φ hφ, hNcl, Subgroup.map_sup,
        hmap, map_map_conj, hmap] at h1
      exact h1
    by_cases hgN : N.map (MulAut.conj (φ t)).toMonoidHom = N
    · left
      rw [hKeq, hgN, sup_idem]
    · right
      exact ⟨φ t, hgN, CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (φ t)) hNc, hKeq⟩

end S153G93

end CFSG.Quasithin
