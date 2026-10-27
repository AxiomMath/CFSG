module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructBase
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

theorem openIsQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

theorem isHatAlt_of_mulEquiv {n : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y' ≃* Y)
    (h : F6.IsHatAlt n Y) : F6.IsHatAlt n Y' := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hZ : (Subgroup.center Y').map e.toMonoidHom = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨openIsQuasisimple_of_mulEquiv e.symm hq, ?_, ⟨(QuotientGroup.congr _ _ e hZ).trans f⟩⟩
  rw [← hc, ← hZ]
  exact Nat.card_congr ((Subgroup.center Y').equivMapOfInjective e.toMonoidHom
    e.injective).toEquiv

theorem F618Core_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y' ≃* Y) (h : F618Core Y) :
    F618Core Y' := by
  rcases h with ⟨p, hp, hp24, hL⟩ | ⟨p, k, hp, hk, hk2, hk16, hL⟩ | hA | hN | hA7 |
    ⟨p, hp, hp8, hL⟩ | ⟨p, hp8, hS⟩ | hM
  · exact Or.inl ⟨p, hp, hp24, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hL⟩
  · exact Or.inr (Or.inl ⟨p, k, hp, hk, hk2, hk16,
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hL⟩)
  · exact Or.inr (Or.inr (Or.inl (isHatAlt_of_mulEquiv e hA)))
  · obtain ⟨f⟩ := hN
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isHatAlt_of_mulEquiv e hA7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hp, hp8, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hL⟩)))))
  · obtain ⟨hpp, K, _, _, hK⟩ := hS
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp8, hpp, K,
      inferInstance, inferInstance, ?_⟩))))))
    rcases hK with ⟨h1, h2, hf | hf⟩ | ⟨h1, h2, hf | hf⟩
    · obtain ⟨f⟩ := hf
      exact Or.inl ⟨h1, h2, Or.inl ⟨e.trans f⟩⟩
    · obtain ⟨f⟩ := hf
      exact Or.inl ⟨h1, h2, Or.inr ⟨e.trans f⟩⟩
    · obtain ⟨f⟩ := hf
      exact Or.inr ⟨h1, h2, Or.inl ⟨e.trans f⟩⟩
    · obtain ⟨f⟩ := hf
      exact Or.inr ⟨h1, h2, Or.inr ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := hM
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f⟩))))))

variable {D : Type} [Group D]

theorem idx2Data_of_simple (hs : IsSimpleGroup D) (hc : F618Core D) : Idx2Data D := by
  have hs' : IsSimpleGroup ↥(⊤ : Subgroup D) := by
    have := hs
    exact Subgroup.topEquiv.isSimpleGroup
  exact ⟨⊤, inferInstance, F618Core_of_mulEquiv Subgroup.topEquiv hc, fun x => trivial, Or.inl hs'⟩

theorem idx2Data_of_quasisimple (hq : CFSG.IsQuasisimple D) (hc : F618Core D) : Idx2Data D := by
  refine ⟨⊤, inferInstance, F618Core_of_mulEquiv Subgroup.topEquiv hc, fun x => trivial,
    Or.inr ?_⟩
  have := (CFSG.Foundations.SteinbergCA.quasisimple_iff D).2.2.1.mp hq
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr
    (openIsQuasisimple_of_mulEquiv Subgroup.topEquiv.symm this)

theorem Idx2Data.of_mulEquiv {D' : Type} [Group D'] (e : D ≃* D') (h : Idx2Data D') :
    Idx2Data D := by
  obtain ⟨Kb, hKn, hcore, hsq, hq⟩ := h
  let f : ↥(Kb.map e.symm.toMonoidHom) ≃* ↥Kb :=
    (Kb.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  refine ⟨Kb.map e.symm.toMonoidHom, hKn.map _ e.symm.surjective, F618Core_of_mulEquiv f hcore,
    fun x => ?_, ?_⟩
  · exact Subgroup.mem_map.2 ⟨e x ^ 2, hsq (e x), by simp⟩
  · rcases hq with hs | hq
    · exact Or.inl f.isSimpleGroup
    · refine Or.inr ?_
      have := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hq
      exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr
        (openIsQuasisimple_of_mulEquiv f.symm this)

theorem idx2Data_of_index_two {N : Subgroup D} (hN : N.index = 2) (hcore : F618Core ↥N)
    (hq : IsSimpleGroup ↥N ∨ CFSG.IsQuasisimple ↥N) : Idx2Data D := by
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have : N.FiniteIndex := ⟨by omega⟩
  refine ⟨N, inferInstance, hcore, fun x => ?_, hq⟩
  have := Subgroup.pow_index_mem N x
  rwa [hN] at this

end Struct

end Gold14610

end CFSG.Quasithin
