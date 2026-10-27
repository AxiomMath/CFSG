module

public import CFSG.Timmesfeld.Outcome
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace Final

theorem chevalleyExceptionalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel G t n p f) :
    ChevalleyExceptionalModel G t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem card_mem_of_lieModel_exceptional {G : Type} [Group G] {t : StatedLieTag} {f : ℕ} (hf : 1 ≤ f)
    (ht : t ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : ChevalleyExceptionalModel G t 2 f) : Nat.card G ∈ evenOrdersExceptUnitarySp4 := by
  refine Set.mem_union_left _ ⟨f, hf, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr (.inr (.inr (.inl (card_chevalleyExceptionalModel_two h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl
      (ExceptionalOrders.card_of_untwistedChevalleyModel_F4 h.2))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ExceptionalOrders.card_of_untwistedChevalleyModel_E6 h.2)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (card_chevalleyExceptionalModel_two h))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ExceptionalOrders.card_of_untwistedChevalleyModel_E7 h.2)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (ExceptionalOrders.card_of_untwistedChevalleyModel_E8 h.2))))))))))

end Final

open Final in
theorem evenLieType_and_card_mem_of_outcome {G : Type} [Group G] (h : Outcome G) :
    (EvenLieType G ∧ Nat.card G ∈ evenOrdersExceptUnitarySp4) ∨ LieModel G .PSU 3 3 1 ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ NativeSporadic.IsSporadic G .J2 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  · have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    refine .inl ⟨⟨_, _, _, hc.1, h⟩, Set.mem_union_left _
      ⟨f, hf, .inl ⟨n - 1, by omega, fun h1 => ?_, (card_statedClassicalModel_two hc).1 rfl⟩⟩⟩
    simp only [Prod.mk.injEq] at h1
    omega
  · have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    exact .inl ⟨⟨_, _, _, hc.1, h⟩, Set.mem_union_left _
      ⟨f, hf, .inr (.inl ⟨n, hn, (card_statedClassicalModel_two hc).2.2.1 rfl⟩)⟩⟩
  · have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    exact .inl ⟨⟨_, _, _, hc.1, h⟩, Set.mem_union_left _
      ⟨f, hf, .inr (.inr (.inl ⟨n, hn, .inl ((card_statedClassicalModel_two hc).2.2.2.1 rfl)⟩))⟩⟩
  · have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    exact .inl ⟨⟨_, _, _, hc.1, h⟩, Set.mem_union_left _
      ⟨f, hf, .inr (.inr (.inl ⟨n, hn, .inr ((card_statedClassicalModel_two hc).2.2.2.2 rfl)⟩))⟩⟩
  · have hc := chevalleyExceptionalModel_of_lieModel (by decide) h
    exact .inl ⟨⟨_, _, _, hc.1, h⟩, Set.mem_union_left _ ⟨f, by omega,
      .inr (.inr (.inr (.inl ⟨hf, ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc.2⟩)))⟩⟩
  · have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := chevalleyExceptionalModel_of_lieModel hct h
    exact .inl ⟨⟨_, _, _, hc.1, h⟩, card_mem_of_lieModel_exceptional hf ht hc⟩
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

theorem card_mem_of_outcome {G : Type} [Group G] (h : Outcome G) :
    Nat.card G ∈ evenOrdersExceptUnitarySp4 ∨ LieModel G .PSU 3 3 1 ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ NativeSporadic.IsSporadic G .J2 :=
  (evenLieType_and_card_mem_of_outcome h).imp_left And.right

theorem not_lieModel_PSU_of_card_mem {G : Type} [Group G]
    (hm : Nat.card G ∈ evenOrdersExceptUnitarySp4) {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    ¬ LieModel G .PSU n 2 f := fun h =>
  (evenOrdersExceptUnitarySp4_ne hm).1 (n - 1) f (by omega) hf
    ((card_statedClassicalModel_two
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2.1 rfl)

theorem not_lieModel_PSp_two_of_card_mem {G : Type} [Group G]
    (hm : Nat.card G ∈ evenOrdersExceptUnitarySp4) {f : ℕ} (hf : 1 ≤ f) :
    ¬ LieModel G .PSp 2 2 f := fun h =>
  (evenOrdersExceptUnitarySp4_ne hm).2 f hf
    ((card_statedClassicalModel_two
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)).2.2.1 rfl)

end CFSG.Timmesfeld
