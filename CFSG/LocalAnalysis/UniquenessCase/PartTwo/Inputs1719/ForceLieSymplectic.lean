module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.Open.StatedDefs
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LieType.Multipliers.U42

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix CFSG.Blueprint

private def sp6Idx : Fin 3 ⊕ Fin 3 → Fin 6
  | .inl i => ![0, 1, 2] i
  | .inr i => ![3, 4, 5] i

private def sp6Mat (r : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun i j => r (sp6Idx i) (sp6Idx j)

private def sp6A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  sp6Mat !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

private def sp6B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  sp6Mat !![0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0]

private def sp6G : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  sp6Mat !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

private def sp6K : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  sp6Mat !![1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0]

private theorem sp6_facts : sp6A * (sp6A * sp6A) = 1 ∧ sp6B * (sp6B * sp6B) = 1 ∧
    sp6G * sp6G = 1 ∧ sp6K * sp6K = 1 ∧
    sp6A * (sp6B * sp6A * (sp6B * sp6B)) = sp6B * sp6A * (sp6B * sp6B) * sp6A ∧
    sp6A * sp6B ≠ sp6B * sp6A ∧ sp6G * sp6A * sp6G = sp6A * sp6A ∧
    sp6K * sp6B * sp6K = sp6B * sp6B := by
  decide +kernel

private theorem sp6_symp : sp6Aᵀ * fromBlocks 0 1 (-1) 0 * sp6A = fromBlocks 0 1 (-1) 0 ∧
    sp6Bᵀ * fromBlocks 0 1 (-1) 0 * sp6B = fromBlocks 0 1 (-1) 0 ∧
    sp6Gᵀ * fromBlocks 0 1 (-1) 0 * sp6G = fromBlocks 0 1 (-1) 0 ∧
    sp6Kᵀ * fromBlocks 0 1 (-1) 0 * sp6K = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

private def sp6UA : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨sp6A, sp6A * sp6A, sp6_facts.1, by rw [mul_assoc]; exact sp6_facts.1⟩
private def sp6UB : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨sp6B, sp6B * sp6B, sp6_facts.2.1, by rw [mul_assoc]; exact sp6_facts.2.1⟩
private def sp6UG : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨sp6G, sp6G, sp6_facts.2.2.1, sp6_facts.2.2.1⟩
private def sp6UK : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨sp6K, sp6K, sp6_facts.2.2.2.1, sp6_facts.2.2.2.1⟩

theorem forceRealPair_sp6 : ForceRealPair ↥(CFSG.Open.StatedSp 3 (ZMod 2)) := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8⟩ := sp6_facts
  obtain ⟨s1, s2, s3, s4⟩ := sp6_symp
  obtain ⟨ha, hb, hw, hab, hg, hk⟩ := forceRealPair_facts_of_matrix sp6UA sp6UB sp6UG sp6UK
    (by rw [mul_assoc]; exact h1) (by rw [mul_assoc]; exact h2) h5 h6 h7 h8
  have m1 : sp6UA ∈ CFSG.Open.StatedSp 3 (ZMod 2) := Subgroup.subset_closure s1
  have m2 : sp6UB ∈ CFSG.Open.StatedSp 3 (ZMod 2) := Subgroup.subset_closure s2
  have m3 : sp6UG ∈ CFSG.Open.StatedSp 3 (ZMod 2) := Subgroup.subset_closure s3
  have m4 : sp6UK ∈ CFSG.Open.StatedSp 3 (ZMod 2) := Subgroup.subset_closure s4
  exact ForceRealPair.of_mem _ m1 m2 m3 m4 ha hb hw hab hg hk

private def sp4X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fromBlocks 1 !![0, 2; 2, 0] 0 1

private def sp4Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fromBlocks !![1, 0; 1, 1] 0 0 !![1, 2; 0, 1]

private def sp4G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fromBlocks !![1, 0; 0, 2] 0 0 !![1, 0; 0, 2]

private theorem sp4_facts : sp4X * (sp4X * sp4X) = 1 ∧ sp4Y * (sp4Y * sp4Y) = 1 ∧
    sp4G * sp4G = 1 ∧
    sp4X * (sp4Y * sp4X * (sp4Y * sp4Y)) = sp4Y * sp4X * (sp4Y * sp4Y) * sp4X ∧
    sp4X * sp4Y ≠ sp4Y * sp4X ∧ sp4X * sp4Y ≠ -(sp4Y * sp4X) ∧
    sp4G * sp4X * sp4G = sp4X * sp4X ∧ sp4G * sp4Y * sp4G = sp4Y * sp4Y := by
  decide +kernel

private theorem sp4_symp : sp4Xᵀ * fromBlocks 0 1 (-1) 0 * sp4X = fromBlocks 0 1 (-1) 0 ∧
    sp4Yᵀ * fromBlocks 0 1 (-1) 0 * sp4Y = fromBlocks 0 1 (-1) 0 ∧
    sp4Gᵀ * fromBlocks 0 1 (-1) 0 * sp4G = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

open CFSG.GH74.Exceptional in
theorem forceRealPair_psp43 : ForceRealPair PSp43 := by
  obtain ⟨h1, h2, h3, h5, h6, h6', h7, h8⟩ := sp4_facts
  obtain ⟨s1, s2, s3⟩ := sp4_symp
  let a : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ⟨sp4X, sp4X * sp4X, h1, by rw [mul_assoc]; exact h1⟩
  let b : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ⟨sp4Y, sp4Y * sp4Y, h2, by rw [mul_assoc]; exact h2⟩
  let g : GL (Fin 2 ⊕ Fin 2) (ZMod 3) := ⟨sp4G, sp4G, h3, h3⟩
  obtain ⟨ha, hb, hw, -, hg, hk⟩ := forceRealPair_facts_of_matrix a b g g
    (by rw [mul_assoc]; exact h1) (by rw [mul_assoc]; exact h2) h5 h6 h7 h8
  let a' : CFSG.Open.StatedSp 2 (ZMod 3) := ⟨a, Subgroup.subset_closure s1⟩
  let b' : CFSG.Open.StatedSp 2 (ZMod 3) := ⟨b, Subgroup.subset_closure s2⟩
  let g' : CFSG.Open.StatedSp 2 (ZMod 3) := ⟨g, Subgroup.subset_closure s3⟩
  refine ForceRealPair.of_hom (QuotientGroup.mk' _) (a := a') (b := b') (g := g') (k := g')
    (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hw) ?_ (Subtype.ext hg) (Subtype.ext hk)
  intro hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hq
  obtain ⟨c, hc⟩ := hq
  have hc' : (a * b) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = b * a := by
    have : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = (a * b)⁻¹ * (b * a) := hc
    rw [this, mul_inv_cancel_left]
  rcases units_zmod_three c with rfl | rfl
  · rw [map_one, mul_one] at hc'
    exact h6 (congrArg Units.val hc')
  · rw [scalar_neg_one, mul_neg_one] at hc'
    apply h6'
    have := congrArg Units.val hc'
    rw [Units.val_neg, Units.val_mul, Units.val_mul] at this
    rw [← this, neg_neg]

theorem forceRealPair_of_lieModel_PSp_three {Q : Type} [Group Q] (h : LieModel Q .PSp 3 2 1) :
    ForceRealPair Q := by
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel h
  exact forceRealPair_sp6.of_mulEquiv e

theorem forceRealPair_of_lieModel_PSU_four {Q : Type} [Group Q] (h : LieModel Q .PSU 4 2 1) :
    ForceRealPair Q := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 h
  exact forceRealPair_psp43.of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
