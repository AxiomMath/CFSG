module

public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item131b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    (Sec4.IsSLThreePiTwo (lBarA c L A) ∨
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
          (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
              CFSG.Blueprint.NativeSporadic.M22))) →
      (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
          CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
          ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
          ¬ IsCyclic (E ⊓ L : Subgroup G) →
            E ∈ partTwoF G ∧ (E ∉ partTwoT G →
              Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
              (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
                Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
              ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
                omegaA E = orbitIn A (Subgroup.zpowers e) ∧
                ∃ I : Subgroup G, lA E e = {I} ∧
                  Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2))

theorem rank3II_13_1_of_parts (h131a : Item131a) (h131b : Item131b) : Item131 := by
  intro G _ _ A c L hD
  rcases h131a G A c L hD with h | h | h | h | h | h | h7
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h7, h131b G A c L hD h7⟩)))))

end CFSG.RankThree.PartTwo.Sec13
