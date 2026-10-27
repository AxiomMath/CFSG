module

public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one diagUnitOne)
open scoped Pointwise MatrixGroups

@[expose] def fourRootSet {τ : Tag} (r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {r₁, -r₁, r₂, -r₂, r₃, -r₃, r₄, -r₄}

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ}

@[expose] def fourProd (τ : Tag) (L : Type) [Field L] (r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ)
    (A B C D : SL2 L) : ModGL τ L :=
  rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D

@[expose] def fourMul (τ : Tag) (L : Type) [Field L] (r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ)
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D)) :
    SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L :=
  (rootSL2 τ L r₁).noncommCoprod
    ((rootSL2 τ L r₂).noncommCoprod
      ((rootSL2 τ L r₃).noncommCoprod (rootSL2 τ L r₄) hc34)
      fun B CD => (hc23 B CD.1).mul_right (hc24 B CD.2))
    fun A BCD => (hc12 A BCD.1).mul_right ((hc13 A BCD.2.1).mul_right (hc14 A BCD.2.2))

theorem fourMul_apply
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D)) (A B C D : SL2 L) :
    fourMul τ L r₁ r₂ r₃ r₄ hc12 hc13 hc14 hc23 hc24 hc34 (A, B, C, D) =
      fourProd τ L r₁ r₂ r₃ r₄ A B C D := by
  show rootSL2 τ L r₁ A * (rootSL2 τ L r₂ B * (rootSL2 τ L r₃ C * rootSL2 τ L r₄ D)) = _
  unfold fourProd
  simp only [mul_assoc]

theorem rootSpan_fourRootSet (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (h₄ : IsRoot τ r₄) :
    rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ ⊔
        rootRankOneGroup τ L r₄ := by
  have key : ∀ r, IsRoot τ r → rootSubgroup τ L r ≤ rootRankOneGroup τ L r ∧
      rootSubgroup τ L (-r) ≤ rootRankOneGroup τ L r := fun r hr => by
    rw [rootRankOneGroup, range_rootSL2_of_isRoot hr]
    exact ⟨le_sup_left, le_sup_right⟩
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (key _ h₁).1.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact (key _ h₁).2.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact (key _ h₂).1.trans (le_sup_right.trans (le_sup_left.trans le_sup_left))
    · exact (key _ h₂).2.trans (le_sup_right.trans (le_sup_left.trans le_sup_left))
    · exact (key _ h₃).1.trans (le_sup_right.trans le_sup_left)
    · exact (key _ h₃).2.trans (le_sup_right.trans le_sup_left)
    · exact (key _ h₄).1.trans le_sup_right
    · exact (key _ h₄).2.trans le_sup_right
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact rootRankOneGroup_le_rootSpan h₁ (by simp [fourRootSet]) (by simp [fourRootSet])
    · exact rootRankOneGroup_le_rootSpan h₂ (by simp [fourRootSet]) (by simp [fourRootSet])
    · exact rootRankOneGroup_le_rootSpan h₃ (by simp [fourRootSet]) (by simp [fourRootSet])
    · exact rootRankOneGroup_le_rootSpan h₄ (by simp [fourRootSet]) (by simp [fourRootSet])

theorem fourRootSet_isRoot (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (h₄ : IsRoot τ r₄) : ∀ α ∈ fourRootSet r₁ r₂ r₃ r₄, IsRoot τ α := by
  intro α hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃, h₄, IsRoot.neg h₄]

theorem fourRootSet_neg : ∀ α ∈ fourRootSet r₁ r₂ r₃ r₄, -α ∈ fourRootSet r₁ r₂ r₃ r₄ := by
  intro α hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fourRootSet]

theorem rootRankOne_le_centralizer_of_commute {r r' : Fin τ.rank → ℤ}
    (h : ∀ A B : SL2 L, Commute (rootSL2 τ L r A) (rootSL2 τ L r' B)) :
    rootRankOneGroup τ L r ≤ Subgroup.centralizer (rootRankOneGroup τ L r' : Set (ModGL τ L)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨B, rfl⟩
  exact (h A B).symm.eq

theorem mem_sup_four
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D)) {q : ModGL τ L}
    (hq : q ∈ rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ ⊔
      rootRankOneGroup τ L r₄) :
    ∃ A B C D : SL2 L, q = fourProd τ L r₁ r₂ r₃ r₄ A B C D := by
  have c12 := rootRankOne_le_centralizer_of_commute hc12
  have c13 := rootRankOne_le_centralizer_of_commute hc13
  have c14 := rootRankOne_le_centralizer_of_commute hc14
  have c23 := rootRankOne_le_centralizer_of_commute hc23
  have c24 := rootRankOne_le_centralizer_of_commute hc24
  have c34 := rootRankOne_le_centralizer_of_commute hc34
  have hle1 : rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ ≤
      Subgroup.normalizer (rootRankOneGroup τ L r₄ : Set (ModGL τ L)) :=
    sup_le (sup_le (c14.trans (Subgroup.centralizer_le_normalizer _))
      (c24.trans (Subgroup.centralizer_le_normalizer _)))
      (c34.trans (Subgroup.centralizer_le_normalizer _))
  have hle2 : rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ≤
      Subgroup.normalizer (rootRankOneGroup τ L r₃ : Set (ModGL τ L)) :=
    sup_le (c13.trans (Subgroup.centralizer_le_normalizer _))
      (c23.trans (Subgroup.centralizer_le_normalizer _))
  have hle3 : rootRankOneGroup τ L r₁ ≤
      Subgroup.normalizer (rootRankOneGroup τ L r₂ : Set (ModGL τ L)) :=
    c12.trans (Subgroup.centralizer_le_normalizer _)
  have e1 := Subgroup.coe_mul_of_left_le_normalizer_right
    (rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃)
    (rootRankOneGroup τ L r₄) hle1
  have e2 := Subgroup.coe_mul_of_left_le_normalizer_right
    (rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂) (rootRankOneGroup τ L r₃) hle2
  have e3 := Subgroup.coe_mul_of_left_le_normalizer_right (rootRankOneGroup τ L r₁)
    (rootRankOneGroup τ L r₂) hle3
  have hq' : q ∈ ((rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔
    rootRankOneGroup τ L r₃ ⊔ rootRankOneGroup τ L r₄ : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hq
  rw [e1, e2, e3] at hq'
  obtain ⟨x3, ⟨x2, ⟨x1, ⟨A, rfl⟩, y1, ⟨B, rfl⟩, rfl⟩, y2, ⟨C, rfl⟩, rfl⟩, y3, ⟨D, rfl⟩, rfl⟩ := hq'
  exact ⟨A, B, C, D, rfl⟩

theorem exists_decomp_four
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄)) :
    ∃ (b : Fin τ.rank → Lˣ) (A B C D : SL2 L),
      y = rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
    (rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄))
    (torusGroup_le_normalizer_rootSpan (fourRootSet_isRoot h₁ h₂ h₃ h₄))
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) :
    Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq, rfl⟩ := hy'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [SetLike.mem_coe, rootSpan_fourRootSet h₁ h₂ h₃ h₄] at hq
  obtain ⟨A, B, C, D, rfl⟩ := mem_sup_four hc12 hc13 hc14 hc23 hc24 hc34 hq
  exact ⟨b, A, B, C, D, rfl⟩

theorem conj_four_rootSL2
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (b : Fin τ.rank → Lˣ) (A B C D : SL2 L) :
    (∀ U, rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D * rootSL2 τ L r₁ U *
        (rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D)⁻¹ =
      rootSL2 τ L r₁ (conjSL (diagUnitOne (rootChar b r₁) *
        Matrix.SpecialLinearGroup.toGL A) U)) ∧
    (∀ U, rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D * rootSL2 τ L r₂ U *
        (rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D)⁻¹ =
      rootSL2 τ L r₂ (conjSL (diagUnitOne (rootChar b r₂) *
        Matrix.SpecialLinearGroup.toGL B) U)) ∧
    (∀ U, rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D * rootSL2 τ L r₃ U *
        (rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D)⁻¹ =
      rootSL2 τ L r₃ (conjSL (diagUnitOne (rootChar b r₃) *
        Matrix.SpecialLinearGroup.toGL C) U)) ∧
    (∀ U, rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D * rootSL2 τ L r₄ U *
        (rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D)⁻¹ =
      rootSL2 τ L r₄ (conjSL (diagUnitOne (rootChar b r₄) *
        Matrix.SpecialLinearGroup.toGL D) U)) := by
  refine ⟨fun U => ?_, fun U => ?_, fun U => ?_, fun U => ?_⟩
  · have h : rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D =
        (rootDiagUnit τ b * rootSL2 τ L r₁ A) *
          (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D) := by
      unfold fourProd
      group
    rw [h, conj_mul_of_commute _ _ _
      ((((hc12 U B).symm.mul_left (hc13 U C).symm).mul_left (hc14 U D).symm).eq),
      conj_rootSL2_torus_mul h₁ b A U]
  · have h : rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D =
        (rootDiagUnit τ b * rootSL2 τ L r₂ B) *
          (rootSL2 τ L r₁ A * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D) := by
      unfold fourProd
      rw [(hc12 A B).eq]
      group
    rw [h, conj_mul_of_commute _ _ _
      ((((hc12 A U).mul_left (hc23 U C).symm).mul_left (hc24 U D).symm).eq),
      conj_rootSL2_torus_mul h₂ b B U]
  · have h : rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D =
        (rootDiagUnit τ b * rootSL2 τ L r₃ C) *
          (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₄ D) := by
      unfold fourProd
      rw [((hc13 A C).mul_left (hc23 B C)).eq]
      group
    rw [h, conj_mul_of_commute _ _ _
      ((((hc13 A U).mul_left (hc23 B U)).mul_left (hc34 U D).symm).eq),
      conj_rootSL2_torus_mul h₃ b C U]
  · have h : rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D =
        (rootDiagUnit τ b * rootSL2 τ L r₄ D) *
          (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) := by
      unfold fourProd
      rw [(((hc14 A D).mul_left (hc24 B D)).mul_left (hc34 C D)).eq]
      group
    rw [h, conj_mul_of_commute _ _ _
      ((((hc14 A U).mul_left (hc24 B U)).mul_left (hc34 C U)).eq),
      conj_rootSL2_torus_mul h₄ b D U]

end Generic

end CFSG.RankThree.PartOne.KE
