module

public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaMain

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one diagUnitOne)
open scoped Pointwise MatrixGroups

@[expose] def threeRootSet {τ : Tag} (r₁ r₂ r₃ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {r₁, -r₁, r₂, -r₂, r₃, -r₃}

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}

theorem rootSpan_threeRootSet (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) :
    rootSpan τ L (threeRootSet r₁ r₂ r₃) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ := by
  have key : ∀ r, IsRoot τ r → rootSubgroup τ L r ≤ rootRankOneGroup τ L r ∧
      rootSubgroup τ L (-r) ≤ rootRankOneGroup τ L r := fun r hr => by
    rw [rootRankOneGroup, range_rootSL2_of_isRoot hr]
    exact ⟨le_sup_left, le_sup_right⟩
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (key _ h₁).1.trans (le_sup_left.trans le_sup_left)
    · exact (key _ h₁).2.trans (le_sup_left.trans le_sup_left)
    · exact (key _ h₂).1.trans (le_sup_right.trans le_sup_left)
    · exact (key _ h₂).2.trans (le_sup_right.trans le_sup_left)
    · exact (key _ h₃).1.trans le_sup_right
    · exact (key _ h₃).2.trans le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact rootRankOneGroup_le_rootSpan h₁ (by simp [threeRootSet]) (by simp [threeRootSet])
    · exact rootRankOneGroup_le_rootSpan h₂ (by simp [threeRootSet]) (by simp [threeRootSet])
    · exact rootRankOneGroup_le_rootSpan h₃ (by simp [threeRootSet]) (by simp [threeRootSet])

theorem conj_mul_of_commute {G : Type*} [Group G] (x c u : G) (h : c * u = u * c) :
    x * c * u * (x * c)⁻¹ = x * u * x⁻¹ := by
  have : c * u * c⁻¹ = u := by rw [h, mul_inv_cancel_right]
  calc x * c * u * (x * c)⁻¹ = x * (c * u * c⁻¹) * x⁻¹ := by group
    _ = x * u * x⁻¹ := by rw [this]

variable (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
  (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
  (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))

include hc12 hc13 hc23

theorem conj_three_rootSL2 (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (b : Fin τ.rank → Lˣ) (A B C : SL2 L) :
    (∀ U, rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) *
        rootSL2 τ L r₁ U * (rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B *
          rootSL2 τ L r₃ C))⁻¹ =
      rootSL2 τ L r₁ (conjSL (diagUnitOne (rootChar b r₁) *
        Matrix.SpecialLinearGroup.toGL A) U)) ∧
    (∀ U, rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) *
        rootSL2 τ L r₂ U * (rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B *
          rootSL2 τ L r₃ C))⁻¹ =
      rootSL2 τ L r₂ (conjSL (diagUnitOne (rootChar b r₂) *
        Matrix.SpecialLinearGroup.toGL B) U)) ∧
    (∀ U, rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) *
        rootSL2 τ L r₃ U * (rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B *
          rootSL2 τ L r₃ C))⁻¹ =
      rootSL2 τ L r₃ (conjSL (diagUnitOne (rootChar b r₃) *
        Matrix.SpecialLinearGroup.toGL C) U)) := by
  refine ⟨fun U => ?_, fun U => ?_, fun U => ?_⟩
  · have h : rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) =
        (rootDiagUnit τ b * rootSL2 τ L r₁ A) * (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) := by
      group
    rw [h, conj_mul_of_commute _ _ _ (((hc12 U B).symm.mul_left (hc13 U C).symm).eq),
      conj_rootSL2_torus_mul h₁ b A U]
  · have h : rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) =
        (rootDiagUnit τ b * rootSL2 τ L r₂ B) * (rootSL2 τ L r₁ A * rootSL2 τ L r₃ C) := by
      calc rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
          = rootDiagUnit τ b * (rootSL2 τ L r₂ B * rootSL2 τ L r₁ A * rootSL2 τ L r₃ C) := by
            rw [(hc12 A B).eq]
        _ = (rootDiagUnit τ b * rootSL2 τ L r₂ B) * (rootSL2 τ L r₁ A * rootSL2 τ L r₃ C) := by
            group
    rw [h, conj_mul_of_commute _ _ _ (((hc12 A U).mul_left (hc23 U C).symm).eq),
      conj_rootSL2_torus_mul h₂ b B U]
  · have h : rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) =
        (rootDiagUnit τ b * rootSL2 τ L r₃ C) * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B) := by
      calc rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
          = rootDiagUnit τ b * ((rootSL2 τ L r₁ A * rootSL2 τ L r₂ B) * rootSL2 τ L r₃ C) := rfl
        _ = rootDiagUnit τ b * (rootSL2 τ L r₃ C * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B)) := by
            rw [((hc13 A C).mul_left (hc23 B C)).eq]
        _ = (rootDiagUnit τ b * rootSL2 τ L r₃ C) * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B) := by
            group
    rw [h, conj_mul_of_commute _ _ _ (((hc13 A U).mul_left (hc23 B U)).eq),
      conj_rootSL2_torus_mul h₃ b C U]


theorem rootRankOne_le_centralizer :
    rootRankOneGroup τ L r₁ ≤ Subgroup.centralizer (rootRankOneGroup τ L r₂ : Set (ModGL τ L)) ∧
    rootRankOneGroup τ L r₁ ≤ Subgroup.centralizer (rootRankOneGroup τ L r₃ : Set (ModGL τ L)) ∧
    rootRankOneGroup τ L r₂ ≤ Subgroup.centralizer (rootRankOneGroup τ L r₃ : Set (ModGL τ L)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, rfl⟩
    exact (hc12 A B).symm.eq
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨C, rfl⟩
    exact (hc13 A C).symm.eq
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨C, rfl⟩
    exact (hc23 B C).symm.eq

theorem mem_sup_three {q : ModGL τ L}
    (hq : q ∈ rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃) :
    ∃ A B C : SL2 L,
      q = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C := by
  obtain ⟨h12, h13, h23⟩ := rootRankOne_le_centralizer hc12 hc13 hc23
  have hle1 : rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ≤
      Subgroup.normalizer (rootRankOneGroup τ L r₃ : Set (ModGL τ L)) :=
    sup_le (h13.trans (Subgroup.centralizer_le_normalizer _))
      (h23.trans (Subgroup.centralizer_le_normalizer _))
  have e1 := Subgroup.coe_mul_of_left_le_normalizer_right
    (rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂) (rootRankOneGroup τ L r₃) hle1
  have e2 := Subgroup.coe_mul_of_left_le_normalizer_right (rootRankOneGroup τ L r₁)
    (rootRankOneGroup τ L r₂) (h12.trans (Subgroup.centralizer_le_normalizer _))
  have hq' : q ∈ ((rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔
    rootRankOneGroup τ L r₃ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hq
  rw [e1, e2] at hq'
  obtain ⟨a, ⟨a₁, ⟨A, rfl⟩, a₂, ⟨B, rfl⟩, rfl⟩, c, ⟨C, rfl⟩, rfl⟩ := hq'
  exact ⟨A, B, C, rfl⟩

theorem exists_decomp (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃)) :
    ∃ (b : Fin τ.rank → Lˣ) (A B C : SL2 L), y = rootDiagUnit τ b *
      (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) := by
  have hS : ∀ α ∈ threeRootSet r₁ r₂ r₃, IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃]
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
    (rootSpan τ L (threeRootSet r₁ r₂ r₃)) (torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃) :
    Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq, rfl⟩ := hy'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [SetLike.mem_coe, rootSpan_threeRootSet h₁ h₂ h₃] at hq
  obtain ⟨A, B, C, rfl⟩ := mem_sup_three hc12 hc13 hc23 hq
  exact ⟨b, A, B, C, rfl⟩


omit hc12 hc13 in
theorem rootSL2_pair_fixed_iff {n : ModGL τ L}
    (hn₂ : ∀ B : SL2 L, n * rootSL2 τ L r₂ B * n⁻¹ = rootSL2 τ L r₃ B)
    (hn₃ : ∀ C : SL2 L, n * rootSL2 τ L r₃ C * n⁻¹ = rootSL2 τ L r₂ C)
    (hinj23 : ∀ B C B' C' : SL2 L,
      rootSL2 τ L r₂ B * rootSL2 τ L r₃ C = rootSL2 τ L r₂ B' * rootSL2 τ L r₃ C' →
        B = B' ∧ C = C')
    (Fr : L →+* L) (B C : SL2 L) :
    n * Units.map (entrywiseHom Fr) (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) * n⁻¹ =
        rootSL2 τ L r₂ B * rootSL2 τ L r₃ C ↔
      Matrix.SpecialLinearGroup.map Fr C = B ∧ Matrix.SpecialLinearGroup.map Fr B = C := by
  rw [map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
  have h : n * (rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) *
      rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C)) * n⁻¹ =
      rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr C) *
        rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B) := by
    calc n * (rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) *
          rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C)) * n⁻¹
        = (n * rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹) *
          (n * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C) * n⁻¹) := by group
      _ = rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B) *
          rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr C) := by rw [hn₂, hn₃]
      _ = rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr C) *
          rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B) :=
        ((hc23 _ _).eq).symm
  rw [h]
  constructor
  · intro heq
    exact hinj23 _ _ _ _ heq
  · rintro ⟨h1, h2⟩
    rw [h1, h2]


@[expose] def pairHom (Fr : L →+* L) : SL2 L →* ModGL τ L :=
  (MonoidHom.noncommCoprod (rootSL2 τ L r₂) (rootSL2 τ L r₃) hc23).comp
    ((MonoidHom.id (SL2 L)).prod (Matrix.SpecialLinearGroup.map Fr))

omit hc12 hc13 in
theorem pairHom_apply (Fr : L →+* L) (B : SL2 L) :
    pairHom hc23 Fr B = rootSL2 τ L r₂ B * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B) :=
  rfl

omit hc12 hc13 in
theorem pairHom_injective
    (hinj23 : ∀ B C B' C' : SL2 L,
      rootSL2 τ L r₂ B * rootSL2 τ L r₃ C = rootSL2 τ L r₂ B' * rootSL2 τ L r₃ C' →
        B = B' ∧ C = C')
    (Fr : L →+* L) : Function.Injective (pairHom hc23 Fr) := by
  intro B B' h
  rw [pairHom_apply, pairHom_apply] at h
  exact (hinj23 _ _ _ _ h).1

theorem three_A1_family [IsAlgClosed L] (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (hinj23 : ∀ B C B' C' : SL2 L,
      rootSL2 τ L r₂ B * rootSL2 τ L r₃ C = rootSL2 τ L r₂ B' * rootSL2 τ L r₃ C' →
        B = B' ∧ C = C')
    (Fr : L →+* L) (n : ModGL τ L)
    (hn₂ : ∀ B : SL2 L, n * rootSL2 τ L r₂ B * n⁻¹ = rootSL2 τ L r₃ B)
    (hn₃ : ∀ C : SL2 L, n * rootSL2 τ L r₃ C * n⁻¹ = rootSL2 τ L r₂ C)
    (S₁ S₂ : Subgroup (SL2 L)) [Finite S₁] [Finite S₂]
    (hS₁ : ∀ B : SL2 L, n * Units.map (entrywiseHom Fr) (rootSL2 τ L r₁ B) * n⁻¹ =
      rootSL2 τ L r₁ B ↔ B ∈ S₁)
    (hS₂ : ∀ B : SL2 L, B ∈ S₂ ↔
      Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr B) = B)
    (hq₁ : CFSG.IsQuasisimple S₁) (hq₂ : CFSG.IsQuasisimple S₂)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Bool → Subgroup (ModGL τ L), (∀ i, Finite (P i)) ∧
      (∀ i, CFSG.IsQuasisimple (P i)) ∧
      (∀ i, P i ≤ rootSpan τ L (threeRootSet r₁ r₂ r₃)) ∧
      (∀ i, P i ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      (∀ i, P i ≤ adjointGroup τ L) ∧
      (∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
        ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
        (∀ i, ∀ u ∈ P i, y * u = u * y) →
        y ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (threeRootSet r₁ r₂ r₃)) ∧
      P true = S₁.map (rootSL2 τ L r₁) ∧ P false = S₂.map (pairHom hc23 Fr) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Rs := twistedFixedPoints n Φ with hRs
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  set Q₁ := rootRankOneGroup τ L r₁ with hQ₁
  set Q₂ := rootRankOneGroup τ L r₂ with hQ₂
  set Q₃ := rootRankOneGroup τ L r₃ with hQ₃
  set ν := pairHom hc23 Fr with hν
  have hνinj : Function.Injective ν := pairHom_injective hc23 hinj23 Fr
  set P₁ : Subgroup (ModGL τ L) := Q₁ ⊓ Rs with hP₁def
  have hP₁S : P₁ = S₁.map (rootSL2 τ L r₁) := by
    ext u
    constructor
    · rintro ⟨hu, hu2⟩
      obtain ⟨B, rfl⟩ := MonoidHom.mem_range.1 hu
      exact ⟨B, (hS₁ B).1 hu2, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨⟨B, rfl⟩, (hS₁ B).2 hB⟩
  have hP₁e : S₁ ≃* P₁ :=
    (Subgroup.equivMapOfInjective S₁ (rootSL2 τ L r₁) (rootSL2_injective_of_field r₁)).trans
      (MulEquiv.subgroupCongr hP₁S.symm)
  set P₂ : Subgroup (ModGL τ L) := (Q₂ ⊔ Q₃) ⊓ Rs with hP₂def
  obtain ⟨-, -, h23⟩ := rootRankOne_le_centralizer hc12 hc13 hc23
  have hP₂S : P₂ = S₂.map ν := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      have e := Subgroup.coe_mul_of_left_le_normalizer_right Q₂ Q₃
        (h23.trans (Subgroup.centralizer_le_normalizer _))
      have hy1' : y ∈ ((Q₂ ⊔ Q₃ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hy1
      rw [e] at hy1'
      obtain ⟨a, ⟨B, rfl⟩, c, ⟨C, rfl⟩, rfl⟩ := hy1'
      obtain ⟨h1, h2⟩ := (rootSL2_pair_fixed_iff hc23 hn₂ hn₃ hinj23 Fr B C).1 hy2
      refine ⟨B, (hS₂ B).2 ?_, ?_⟩
      · rw [h2]
        exact h1
      · rw [hν, pairHom_apply, h2]
    · rintro ⟨B, hB, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hν, pairHom_apply]
        exact mul_mem (le_sup_left (a := Q₂) (b := Q₃) ⟨B, rfl⟩)
          (le_sup_right (a := Q₂) (b := Q₃) ⟨_, rfl⟩)
      · rw [hν, pairHom_apply]
        exact (rootSL2_pair_fixed_iff hc23 hn₂ hn₃ hinj23 Fr B _).2 ⟨(hS₂ B).1 hB, rfl⟩
  have hP₂e : S₂ ≃* P₂ :=
    (Subgroup.equivMapOfInjective S₂ ν hνinj).trans (MulEquiv.subgroupCongr hP₂S.symm)
  have hPq₁ : CFSG.IsQuasisimple P₁ := CFSG.LocalCores.isQuasisimple_of_mulEquiv hP₁e hq₁
  have hPq₂ : CFSG.IsQuasisimple P₂ := CFSG.LocalCores.isQuasisimple_of_mulEquiv hP₂e hq₂
  have hfin₁ : Finite P₁ := Finite.of_equiv S₁ hP₁e.toEquiv
  have hfin₂ : Finite P₂ := Finite.of_equiv S₂ hP₂e.toEquiv
  have hS3 : ∀ α ∈ threeRootSet r₁ r₂ r₃, IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃]
  have hQS : rootSpan τ L (threeRootSet r₁ r₂ r₃) = Q₁ ⊔ Q₂ ⊔ Q₃ :=
    rootSpan_threeRootSet h₁ h₂ h₃
  have hH₁ := torusGroup_le_normalizer_rootRankOneGroup (L := L) h₁
  have hH₂ := torusGroup_le_normalizer_rootRankOneGroup (L := L) h₂
  have hH₃ := torusGroup_le_normalizer_rootRankOneGroup (L := L) h₃
  have hc21 : Q₂ ≤ Subgroup.centralizer (Q₁ : Set (ModGL τ L)) := by
    rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (hc12 A B).eq
  have hc31 : Q₃ ≤ Subgroup.centralizer (Q₁ : Set (ModGL τ L)) := by
    rintro _ ⟨C, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (hc13 A C).eq
  have hc32 : Q₃ ≤ Subgroup.centralizer (Q₂ : Set (ModGL τ L)) := by
    rintro _ ⟨C, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, rfl⟩
    exact (hc23 B C).eq
  have hQ23c : Q₂ ⊔ Q₃ ≤ Subgroup.centralizer (Q₁ : Set (ModGL τ L)) := sup_le hc21 hc31
  have hQ1c : Q₁ ≤ Subgroup.centralizer ((Q₂ ⊔ Q₃ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hQ23c hh) g hg).symm
  have hN₁ : torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃) ≤
      Subgroup.normalizer (Q₁ : Set (ModGL τ L)) := by
    refine sup_le hH₁ ?_
    rw [hQS]
    exact sup_le (sup_le Subgroup.le_normalizer (hc21.trans (Subgroup.centralizer_le_normalizer _)))
      (hc31.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂₃ : torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃) ≤
      Subgroup.normalizer ((Q₂ ⊔ Q₃ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
    refine sup_le (fun h hh => Subgroup.inf_normalizer_le_normalizer_sup Q₂ Q₃
      ⟨hH₂ hh, hH₃ hh⟩) ?_
    rw [hQS]
    exact sup_le (sup_le (hQ1c.trans (Subgroup.centralizer_le_normalizer _))
      (le_sup_left.trans Subgroup.le_normalizer)) (le_sup_right.trans Subgroup.le_normalizer)
  have hQadj : ∀ r, rootRankOneGroup τ L r ≤ adjointGroup τ L := fun r => by
    rintro _ ⟨A, rfl⟩
    exact hρadj r A
  refine ⟨fun i => cond i P₁ P₂, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, ?_, ?_, ?_, ?_⟩
  · cases i
    · exact hfin₂
    · exact hfin₁
  · cases i
    · exact hPq₂
    · exact hPq₁
  · rw [hQS]
    cases i
    · exact inf_le_left.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    · exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  · cases i
    · exact inf_le_right
    · exact inf_le_right
  · cases i
    · exact inf_le_left.trans (sup_le (hQadj r₂) (hQadj r₃))
    · exact inf_le_left.trans (hQadj r₁)
  · intro i y hy hyR u hu
    cases i
    · have hu' : u ∈ P₂ := hu
      have hR : y * u * y⁻¹ ∈ Rs := mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hN₂₃ hy) u).1 hu'.1, hR⟩
    · have hu' : u ∈ P₁ := hu
      have hR : y * u * y⁻¹ ∈ Rs := mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hN₁ hy) u).1 hu'.1, hR⟩
  · intro y hy hyR hcomm
    obtain ⟨b, A, B, C, rfl⟩ := exists_decomp hc12 hc13 hc23 h₁ h₂ h₃ hy
    obtain ⟨hc1', hc2', hc3'⟩ := conj_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃ b A B C
    set t := rootDiagUnit τ b with ht
    have htH : t ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup b
    set y := t * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) with hydef
    set X₁ : GL (Fin 2) L := diagUnitOne (rootChar b r₁) * Matrix.SpecialLinearGroup.toGL A
      with hX₁
    set X₂ : GL (Fin 2) L := diagUnitOne (rootChar b r₂) * Matrix.SpecialLinearGroup.toGL B
      with hX₂
    set X₃ : GL (Fin 2) L := diagUnitOne (rootChar b r₃) * Matrix.SpecialLinearGroup.toGL C
      with hX₃
    have hU₁ : ∀ U ∈ S₁, conjSL X₁ U = U := by
      intro U hU
      apply rootSL2_injective_of_field r₁
      rw [← hc1' U]
      have hmem : rootSL2 τ L r₁ U ∈ P₁ := by
        rw [hP₁S]
        exact ⟨U, hU, rfl⟩
      have h := hcomm true _ hmem
      rw [h, mul_inv_cancel_right]
    have hpair : ∀ B' ∈ S₂, conjSL X₂ B' = B' ∧
        conjSL X₃ (Matrix.SpecialLinearGroup.map Fr B') = Matrix.SpecialLinearGroup.map Fr B' := by
      intro B' hB'
      have hmem : ν B' ∈ P₂ := by
        rw [hP₂S]
        exact ⟨B', hB', rfl⟩
      have h := hcomm false _ hmem
      rw [hν, pairHom_apply] at h
      have h2 : y * (rootSL2 τ L r₂ B' * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B')) *
          y⁻¹ = rootSL2 τ L r₂ B' * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B') := by
        rw [h, mul_inv_cancel_right]
      have h3 : y * (rootSL2 τ L r₂ B' * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B')) *
          y⁻¹ = (y * rootSL2 τ L r₂ B' * y⁻¹) *
            (y * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr B') * y⁻¹) := by group
      rw [h3, hc2' B', hc3' (Matrix.SpecialLinearGroup.map Fr B')] at h2
      exact hinj23 _ _ _ _ h2
    have hstab : ∀ D ∈ S₂, Matrix.SpecialLinearGroup.map Fr D ∈ S₂ := fun D hD =>
      (hS₂ _).2 (congrArg (Matrix.SpecialLinearGroup.map Fr) ((hS₂ D).1 hD))
    have hU₂ : ∀ D ∈ S₂, conjSL X₂ D = D := fun D hD => (hpair D hD).1
    have hU₃ : ∀ D ∈ S₂, conjSL X₃ D = D := by
      intro D hD
      have h := (hpair _ (hstab D hD)).2
      rwa [(hS₂ D).1 hD] at h
    have hfac : ∀ (r : Fin τ.rank → ℤ) (hr : IsRoot τ r) (S : Subgroup (SL2 L))
        (hz : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
          Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
            (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) (M : SL2 L) (X : GL (Fin 2) L)
        (hX : X = diagUnitOne (rootChar b r) * Matrix.SpecialLinearGroup.toGL M)
        (hSX : ∀ U ∈ S, conjSL X U = U),
        t * rootSL2 τ L r M ∈ torusGroup τ L ∧
          ∀ A' : SL2 L, rootSL2 τ L r (conjSL X A') = rootSL2 τ L r A' := by
      intro r hr S hz M X hX hSX
      have hconj := conj_rootSL2_torus_mul hr b M
      rw [← hX] at hconj
      have hc : ∀ U ∈ S, (t * rootSL2 τ L r M) * rootSL2 τ L r U =
          rootSL2 τ L r U * (t * rootSL2 τ L r M) := fun U hU => by
        have h := hconj U
        rw [hSX U hU] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have hyH : t * rootSL2 τ L r M ∈
          (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L r : Set (ModGL τ L)) :=
        ⟨t, htH, rootSL2 τ L r M, ⟨M, rfl⟩, rfl⟩
      have hall := commute_rootSL2_of_commute_fixed hr hz hyH hc
      refine ⟨mem_torusGroup_of_centralizes_rootSL2 hr hyH hall, fun A' => ?_⟩
      have h := hconj A'
      rw [hall A', mul_inv_cancel_right] at h
      exact h.symm
    obtain ⟨hT₁, hF₁⟩ := hfac r₁ h₁ S₁ hz₁ A X₁ hX₁ hU₁
    obtain ⟨hT₂, hF₂⟩ := hfac r₂ h₂ S₂ hz₂ B X₂ hX₂ hU₂
    obtain ⟨hT₃, hF₃⟩ := hfac r₃ h₃ S₂ hz₂ C X₃ hX₃ hU₃
    have hA : rootSL2 τ L r₁ A ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₁
      rwa [inv_mul_cancel_left] at this
    have hB : rootSL2 τ L r₂ B ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₂
      rwa [inv_mul_cancel_left] at this
    have hC : rootSL2 τ L r₃ C ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₃
      rwa [inv_mul_cancel_left] at this
    have hyH : y ∈ torusGroup τ L := mul_mem htH (mul_mem (mul_mem hA hB) hC)
    have hcZ : y ∈ Subgroup.centralizer
        ((rootSpan τ L (threeRootSet r₁ r₂ r₃) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, hQS] at hg
      obtain ⟨A', B', C', rfl⟩ := mem_sup_three hc12 hc13 hc23 hg
      have f₁ : Commute y (rootSL2 τ L r₁ A') := by
        have h := hc1' A'
        rw [hF₁ A'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have f₂ : Commute y (rootSL2 τ L r₂ B') := by
        have h := hc2' B'
        rw [hF₂ B'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have f₃ : Commute y (rootSL2 τ L r₃ C') := by
        have h := hc3' C'
        rw [hF₃ C'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      exact ((f₁.mul_right f₂).mul_right f₃).eq.symm
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩
  · exact hP₁S
  · exact hP₂S


theorem rootDiagUnit_mem_centralizer_three_iff (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂)
    (h₃ : IsRoot τ r₃) (a : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a ∈ Subgroup.centralizer
        ((rootSpan τ L (threeRootSet r₁ r₂ r₃) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) ↔
      rootChar a r₁ = 1 ∧ rootChar a r₂ = 1 ∧ rootChar a r₃ = 1 := by
  rw [rootSpan_threeRootSet h₁ h₂ h₃]
  constructor
  · intro h
    have key : ∀ Q : Subgroup (ModGL τ L),
        Q ≤ rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ →
          rootDiagUnit τ a ∈ Subgroup.centralizer (Q : Set (ModGL τ L)) := fun Q hQ => by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_iff.1 h g (hQ hg)
    exact ⟨(rootDiagUnit_mem_centralizer_iff h₁ a).1 (key _ (le_sup_left.trans le_sup_left)),
      (rootDiagUnit_mem_centralizer_iff h₂ a).1 (key _ (le_sup_right.trans le_sup_left)),
      (rootDiagUnit_mem_centralizer_iff h₃ a).1 (key _ le_sup_right)⟩
  · rintro ⟨e₁, e₂, e₃⟩
    have c₁ := (rootDiagUnit_mem_centralizer_iff h₁ a).2 e₁
    have c₂ := (rootDiagUnit_mem_centralizer_iff h₂ a).2 e₂
    have c₃ := (rootDiagUnit_mem_centralizer_iff h₃ a).2 e₃
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe] at hg
    obtain ⟨A, B, C, rfl⟩ := mem_sup_three hc12 hc13 hc23 hg
    have f₁ : Commute (rootDiagUnit τ a) (rootSL2 τ L r₁ A) :=
      (Subgroup.mem_centralizer_iff.1 c₁ _ ⟨A, rfl⟩).symm
    have f₂ : Commute (rootDiagUnit τ a) (rootSL2 τ L r₂ B) :=
      (Subgroup.mem_centralizer_iff.1 c₂ _ ⟨B, rfl⟩).symm
    have f₃ : Commute (rootDiagUnit τ a) (rootSL2 τ L r₃ C) :=
      (Subgroup.mem_centralizer_iff.1 c₃ _ ⟨C, rfl⟩).symm
    exact ((f₁.mul_right f₂).mul_right f₃).eq.symm

theorem subtorusSigma_eq_map_fixedBlockTuples_three [IsAlgClosed L]
    {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    (hT : twistedTorusOf n Φ = (fixedCharTuples M Fr).map (rootDiagUnitHom τ L))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) :
    subtorusSigma n Φ (threeRootSet r₁ r₂ r₃) =
      (fixedBlockTuples M Fr {r₁, r₂, r₃}).map (rootDiagUnitHom τ L) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [hT] at hx1
    obtain ⟨a, ha, rfl⟩ := hx1
    have h := (rootDiagUnit_mem_centralizer_three_iff hc12 hc13 hc23 h₁ h₂ h₃ a).1 hx2
    refine ⟨a, ⟨ha, fun u hu => ?_⟩, rfl⟩
    rcases hu with rfl | rfl | rfl
    exacts [h.1, h.2.1, h.2.2]
  · rintro ⟨a, ⟨ha, hrt⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact ⟨a, ha, rfl⟩
    · exact (rootDiagUnit_mem_centralizer_three_iff hc12 hc13 hc23 h₁ h₂ h₃ a).2
        ⟨hrt r₁ (by simp), hrt r₂ (by simp), hrt r₃ (by simp)⟩

end Generic

end CFSG.RankThree.PartOne.KE
