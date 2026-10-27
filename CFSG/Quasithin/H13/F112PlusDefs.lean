module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit
public import CFSG.Quasithin.Vol2.Ch5Sec1DS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Quasithin.F112R

@[expose] def DSCStatementPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 →
    centerOf (L1 ⊔ S ⊔ borelOf L2 S) ≠ ⊥ → S ≤ L2 →
    ¬ (Nonempty (oTwoQuot ↥L2 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L2 ≃* ↥(Sz 0)))

@[expose] def F112SliceFDBigPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VBig L1 → VFD L2 →
    centerOf (L1 ⊔ S ⊔ borelOf L2 S) ≠ ⊥ → S ≤ L2 → False

theorem dscPlus_iff_slicePlus : DSCStatementPlus ↔ F112SliceFDBigPlus := by
  constructor
  · intro h G _ _ L1 L2 S hH hBig hFD hc hS
    exact h G L1 L2 S hH.1 hH.2.1 hH.2.2 (hH.vBig_iff_left.1 hBig) hc hS hFD
  · intro h G _ _ L1 L2 S hH hQ hN hs1 hc hS hFD
    exact h G L1 L2 S ⟨hH, hQ, hN⟩ (vBig_of_not_isSolvable hs1) hFD hc hS

@[expose] def DSBStatementPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) → S ≤ L2 →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
          centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112ListB L1' L2' S ∧ F112Second L1' L2' S

@[expose] def F112R1QPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → S ≤ L1 → VBig L2 → ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)

theorem dsBPlus_of_sliceS3L2_R1QPlus (hs : F112SliceS3L2 F112ConclPredC) (hR1 : F112R1QPlus) :
    DSBStatementPlus := by
  have hF := listedGroupFacts
  intro G _ _ L1 L2 S hyp hq hS hns1 hS3 hSle
  have hS3' : VS3 L2 := hS3
  have hFh : F112Hyp L1 L2 S := ⟨hyp, hq, hS⟩
  have hb1 : VBig L1 := vBig_of_not_isSolvable hns1
  have hL1 : ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L1) := hR1 G L2 L1 S hFh.symm hS3' hSle hb1
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ :=
    hs G L1 L2 S hFh (Or.inr ⟨hb1, hS3'⟩) (by
      rintro L (rfl | rfl) hL
      · exact hL1
      · exact absurd (Or.inl hS3') hL)
  refine ⟨L1', L2', hsw, hZ, ?_, h2⟩
  rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact f112ListB_unswapped hF hns1 hS3 hl
  · exact f112ListB_swapped hF hns1 hS3 hl

end CFSG.Quasithin.H13
