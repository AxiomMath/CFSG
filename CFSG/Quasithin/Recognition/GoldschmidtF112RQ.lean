module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Vol2.Ch5Sec1DS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv

public section

namespace CFSG.Quasithin

namespace F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

@[expose] def F112R1Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → VBig L2 → ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)

@[expose] def DSBStatementL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → (∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L1)) →
    Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
          centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112ListB L1' L2' S ∧ F112Second L1' L2' S

theorem dsBL2_of_sliceS3L2 (hs : F112SliceS3L2 F112ConclPredC) : DSBStatementL2 := by
  have hF := listedGroupFacts
  intro G _ _ L1 L2 S hyp hq hS hns1 hL1 hS3
  have hS3' : VS3 L2 := hS3
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ :=
    hs G L1 L2 S ⟨hyp, hq, hS⟩ (Or.inr ⟨vBig_of_not_isSolvable hns1, hS3'⟩) (by
      rintro L (rfl | rfl) hL
      · exact hL1
      · exact absurd (Or.inl hS3') hL)
  refine ⟨L1', L2', hsw, hZ, ?_, h2⟩
  rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact f112ListB_unswapped hF hns1 hS3 hl
  · exact f112ListB_swapped hF hns1 hS3 hl

end F112R

end CFSG.Quasithin
