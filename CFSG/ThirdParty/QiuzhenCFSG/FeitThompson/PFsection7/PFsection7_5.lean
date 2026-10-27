module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_4

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_5_statement
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (A : I → Set G)
    (L : I → Subgroup G)
    (H : I → G → Subgroup G)
    (G0 : Set G) : Prop :=
  hypothesis_7_4_statement A L H G0 →
    ∀ χ : Section1.ClassFunction G,
      Section1.IsIrreducibleCharacterOnGroup χ →
        normalizedSupportEnergy G0 χ +
            ∑ i, weightedProjectionEnergy (A i) (L i) (H i) χ ≤
          normalizedSupportEnergy G0 (Section1.principalCharacter G) +
            ∑ i, ((A i).ncard : ℝ) / (Nat.card (L i) : ℝ)

/-- Peterfalvi Hypothesis `(7.6)`. -/


private theorem isClassFunction_of_irreducible_pf75
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρ, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem scalarProduct_self_of_irreducible_pf75
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem cfNormSq_irreducible_eq_one_pf75
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section5.cfNormSq χ = 1 := by
  unfold Section5.cfNormSq
  rw [scalarProduct_self_of_irreducible_pf75 hχ]
  simp

private theorem principal_isClassFunction_pf75
    {G : Type u} [Group G] :
    Section1.IsClassFunction (Section1.principalCharacter G) := by
  intro x g
  simp [Section1.principalCharacter]

private theorem cfNormSq_principal_eq_one_pf75
    {G : Type u} [Group G] [Finite G] :
    Section5.cfNormSq (Section1.principalCharacter G) = 1 := by
  unfold Section5.cfNormSq Section1.scalarProduct Section1.principalCharacter
  simp

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf75
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section5.cfNormSq φ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) := by
  unfold Section5.cfNormSq Section1.scalarProduct
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g)) = Complex.re (star (φ g) * φ g) := by
      rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by
          simp

private theorem supportEnergy_partition_pf75
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (S : I → Set G) (G0 : Set G)
    (hG0 : G0 = (Set.univ \ ⋃ i, S i))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (χ : Section1.ClassFunction G) :
    supportEnergy G0 χ + ∑ i, supportEnergy (S i) χ =
      ∑ g : G, Complex.normSq (χ g) := by
  classical
  unfold supportEnergy
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  by_cases hg0 : g ∈ G0
  · have hnotU : g ∉ ⋃ i, S i := by
      have hg0' : g ∈ Set.univ \ ⋃ i, S i := by
        simpa [hG0] using hg0
      exact hg0'.2
    have hnotS : ∀ i, g ∉ S i := by
      intro i hgi
      exact hnotU (Set.mem_iUnion.2 ⟨i, hgi⟩)
    have hsum : (∑ i, if g ∈ S i then Complex.normSq (χ g) else 0) = 0 := by
      simp [hnotS]
    simp [hg0, hsum]
  · have hU : g ∈ ⋃ i, S i := by
      by_contra hnotU
      exact hg0 (by
        simpa [hG0] using (show g ∈ Set.univ \ ⋃ i, S i from ⟨trivial, hnotU⟩))
    rcases Set.mem_iUnion.1 hU with ⟨i0, hi0⟩
    have huniq : ∀ j, j ≠ i0 → g ∉ S j := by
      intro j hji hgj
      have hdis : Disjoint (S j) (S i0) := hdisj hji
      exact Set.disjoint_left.mp hdis hgj hi0
    have hsum : (∑ i, if g ∈ S i then Complex.normSq (χ g) else 0) =
        Complex.normSq (χ g) := by
      simpa [hi0] using
        (Finset.sum_eq_single
          (s := (Finset.univ : Finset I))
          (f := fun i => if g ∈ S i then Complex.normSq (χ g) else 0) i0
          (by
            intro j _hj hji
            simp [huniq j hji])
          (by
            intro hi0not
            exact False.elim (hi0not (by simp))))
    simp [hg0, hsum]

private theorem normalizedSupportEnergy_partition_pf75
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (S : I → Set G) (G0 : Set G)
    (hG0 : G0 = (Set.univ \ ⋃ i, S i))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (χ : Section1.ClassFunction G) :
    normalizedSupportEnergy G0 χ + ∑ i, normalizedSupportEnergy (S i) χ =
      Section5.cfNormSq χ := by
  calc
    normalizedSupportEnergy G0 χ + ∑ i, normalizedSupportEnergy (S i) χ =
        (Nat.card G : ℝ)⁻¹ * (supportEnergy G0 χ + ∑ i, supportEnergy (S i) χ) := by
          unfold normalizedSupportEnergy
          rw [← Finset.mul_sum]
          ring
    _ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (χ g) := by
          rw [supportEnergy_partition_pf75 S G0 hG0 hdisj χ]
    _ = Section5.cfNormSq χ := by
          rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf75]

private theorem dadeProjectionOn_principal_apply_of_mem_pf75
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (a : L) (ha : (a : G) ∈ A) :
    dadeProjectionOn A L H (Section1.principalCharacter G) a = 1 := by
  unfold dadeProjectionOn dadeProjection Section2.dadeAveragingFunction
  simp only [ha, ↓reduceIte, Section1.principalCharacter]
  simp

private theorem dadeProjectionOn_principal_apply_of_not_mem_pf75
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (a : L) (ha : (a : G) ∉ A) :
    dadeProjectionOn A L H (Section1.principalCharacter G) a = 0 := by
  simp [dadeProjectionOn, ha]

private theorem subgroup_mem_subtype_card_eq_ncard_pf75
    {G : Type u} [Group G]
    (A : Set G) (L : Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) :
    Nat.card {l : L // (l : G) ∈ A} = A.ncard := by
  let e : {l : L // (l : G) ∈ A} ≃ A :=
    { toFun := fun l => ⟨(l.1 : G), l.2⟩
      invFun := fun a => ⟨⟨a.1, hAL a.1 a.2⟩, a.2⟩
      left_inv := by
        intro l
        ext
        rfl
      right_inv := by
        intro a
        ext
        rfl }
  calc
    Nat.card {l : L // (l : G) ∈ A} = Nat.card A := Nat.card_congr e
    _ = A.ncard := Nat.card_coe_set_eq A

private theorem weightedProjectionEnergy_principal_eq_card_pf75
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Section2.Hypothesis2 A L H) :
    weightedProjectionEnergy A L H (Section1.principalCharacter G) =
      ((A.ncard : ℝ) / (Nat.card L : ℝ)) := by
  classical
  rw [weightedProjectionEnergy, cfNormSq_eq_inv_card_mul_sum_normSq_pf75]
  have hsum :
      (∑ l : L,
          Complex.normSq (dadeProjectionOn A L H (Section1.principalCharacter G) l)) =
        (A.ncard : ℝ) := by
    calc
      (∑ l : L,
          Complex.normSq (dadeProjectionOn A L H (Section1.principalCharacter G) l)) =
          ∑ l : L, if (l : G) ∈ A then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro l _hl
            by_cases hlA : (l : G) ∈ A
            · rw [dadeProjectionOn_principal_apply_of_mem_pf75 A L H l hlA]
              simp [hlA]
            · rw [dadeProjectionOn_principal_apply_of_not_mem_pf75 A L H l hlA]
              simp [hlA]
      _ = (A.ncard : ℝ) :=
          by
            rw [← subgroup_mem_subtype_card_eq_ncard_pf75 A L h.subset_L]
            norm_num [Fintype.card_subtype]
  have huniv :
      (@Finset.univ L (Fintype.ofFinite L)) = (Finset.univ : Finset L) := by
    ext l
    simp
  rw [huniv]
  rw [hsum]
  rw [div_eq_mul_inv, mul_comm]

public theorem theorem_7_5
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (A : I → Set G)
    (L : I → Subgroup G)
    (H : I → G → Subgroup G)
    (G0 : Set G) :
    theorem_7_5_statement A L H G0 := by
  intro h74 χ hχirr
  rcases h74 with ⟨hfamily, hG0⟩
  rcases hfamily with ⟨h71, hdisj⟩
  let S : I → Set G := fun i => dadeProjectionSupport (A i) (H i)
  have hG0S : G0 = Set.univ \ ⋃ i, S i := by
    simpa [S] using hG0
  have hχclass : Section1.IsClassFunction χ :=
    isClassFunction_of_irreducible_pf75 hχirr
  have hsum_le :
      (∑ i, weightedProjectionEnergy (A i) (L i) (H i) χ) ≤
        ∑ i, normalizedSupportEnergy (S i) χ := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact (theorem_7_3 (A i) (L i) (H i) χ (h71 i) hχclass).1
  have hleft_le_norm :
      normalizedSupportEnergy G0 χ +
          ∑ i, weightedProjectionEnergy (A i) (L i) (H i) χ ≤
        Section5.cfNormSq χ := by
    have hleft_le :
        normalizedSupportEnergy G0 χ +
            ∑ i, weightedProjectionEnergy (A i) (L i) (H i) χ ≤
          normalizedSupportEnergy G0 χ +
            ∑ i, normalizedSupportEnergy (S i) χ :=
      add_le_add le_rfl hsum_le
    simpa [normalizedSupportEnergy_partition_pf75 S G0 hG0S hdisj χ] using hleft_le
  have hleft_le_one :
      normalizedSupportEnergy G0 χ +
          ∑ i, weightedProjectionEnergy (A i) (L i) (H i) χ ≤ 1 := by
    simpa [cfNormSq_irreducible_eq_one_pf75 hχirr] using hleft_le_norm
  have hprincipal_const :
      ∀ i, constantOnDadeFibres (A i) (H i) (Section1.principalCharacter G) := by
    intro i a h ha hh
    simp [Section1.principalCharacter]
  have hprincipal_eq :
      normalizedSupportEnergy G0 (Section1.principalCharacter G) +
          ∑ i, ((A i).ncard : ℝ) / (Nat.card (L i) : ℝ) = 1 := by
    calc
      normalizedSupportEnergy G0 (Section1.principalCharacter G) +
          ∑ i, ((A i).ncard : ℝ) / (Nat.card (L i) : ℝ)
          =
        normalizedSupportEnergy G0 (Section1.principalCharacter G) +
          ∑ i, weightedProjectionEnergy (A i) (L i) (H i)
            (Section1.principalCharacter G) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [weightedProjectionEnergy_principal_eq_card_pf75 (A i) (L i) (H i) (h71 i)]
      _ =
        normalizedSupportEnergy G0 (Section1.principalCharacter G) +
          ∑ i, normalizedSupportEnergy (S i) (Section1.principalCharacter G) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact (theorem_7_3 (A i) (L i) (H i) (Section1.principalCharacter G)
            (h71 i) principal_isClassFunction_pf75).2.2 (hprincipal_const i)
      _ = Section5.cfNormSq (Section1.principalCharacter G) := by
          exact normalizedSupportEnergy_partition_pf75 S G0 hG0S hdisj
            (Section1.principalCharacter G)
      _ = 1 := cfNormSq_principal_eq_one_pf75
  exact le_of_le_of_eq hleft_le_one hprincipal_eq.symm

end CFSG.Section7
