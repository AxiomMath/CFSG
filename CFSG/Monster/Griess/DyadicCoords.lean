module

public import CFSG.Monster.Griess.Space

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster Matrix

@[expose] def IsDyadicVec (u : SpaceB) : Prop :=
  (∀ i j, (u.1 : Matrix (Fin 24) (Fin 24) ℚ) i j ∈ dyadic) ∧ (∀ c, u.2.1 c ∈ dyadic) ∧
    ∀ j i, u.2.2 j i ∈ dyadic

@[expose] noncomputable def dyadicVecs : Submodule dyadic SpaceB where
  carrier := {u | IsDyadicVec u}
  add_mem' {_ _} hu hv :=
    ⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun c => add_mem (hu.2.1 c) (hv.2.1 c),
      fun j i => add_mem (hu.2.2 j i) (hv.2.2 j i)⟩
  zero_mem' := ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' c _ hu :=
    ⟨fun i j => mul_mem c.2 (hu.1 i j), fun d => mul_mem c.2 (hu.2.1 d),
      fun j i => mul_mem c.2 (hu.2.2 j i)⟩

theorem mem_dyadicVecs {u : SpaceB} : u ∈ dyadicVecs ↔ IsDyadicVec u := Iff.rfl

private theorem ite_mem_dyadic (p : Prop) [Decidable p] : (if p then (1 : ℚ) else 0) ∈ dyadic := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isDyadicVec_basisB (k : BIdx) : IsDyadicVec (basisB k) := by
  rcases k with z | c | ⟨j, i⟩
  · rw [basisB_inl]
    refine ⟨fun k l => ?_, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
    rw [basisA_apply]
    exact ite_mem_dyadic _
  · rw [basisB_inr_inl]
    refine ⟨fun _ _ => zero_mem _, fun d => ?_, fun _ _ => zero_mem _⟩
    change (Pi.single c 1 : SpaceX) d ∈ dyadic
    rw [Pi.single_apply]
    exact ite_mem_dyadic _
  · rw [basisB_inr_inr]
    refine ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun j' i' => ?_⟩
    simp only [tensor, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp [one_mem, zero_mem]

theorem BR_le_dyadicVecs : BR ≤ dyadicVecs :=
  Submodule.span_le.2 (Set.range_subset_iff.2 isDyadicVec_basisB)

private theorem smul_mem_BR {c : ℚ} (hc : c ∈ dyadic) {v : SpaceB} (hv : v ∈ BR) : c • v ∈ BR :=
  Submodule.smul_mem BR (⟨c, hc⟩ : dyadic) hv

private theorem basisB_mem_BR (k : BIdx) : basisB k ∈ BR := Submodule.subset_span ⟨k, rfl⟩

theorem symMat_eq_sum (A : symMat) : A = ∑ z, symEntry A z • basisA z := by
  conv_lhs => rw [← basisA.sum_repr A]
  rfl

theorem mem_BR_of_isDyadicVec {u : SpaceB} (hu : IsDyadicVec u) : u ∈ BR := by
  have hdec : u = ((u.1, 0, 0) : SpaceB) + (0, u.2.1, 0) + (0, 0, u.2.2) := by
    ext <;> simp
  rw [hdec]
  refine add_mem (add_mem ?_ ?_) ?_
  · have h : ((u.1, 0, 0) : SpaceB) = ∑ z, symEntry u.1 z • basisB (Sum.inl z) := by
      simp only [basisB_inl]
      conv_lhs => rw [symMat_eq_sum u.1]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum]
      · simp [Prod.snd_sum]
    rw [h]
    refine Submodule.sum_mem _ fun z _ => smul_mem_BR ?_ (basisB_mem_BR _)
    induction z using Sym2.ind with | h i j => rw [symEntry_mk]; exact hu.1 i j
  · have h : ((0, u.2.1, 0) : SpaceB) = ∑ c, u.2.1 c • basisB (Sum.inr (Sum.inl c)) := by
      simp only [basisB_inr_inl]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [h]
    exact Submodule.sum_mem _ fun c _ => smul_mem_BR (hu.2.1 c) (basisB_mem_BR _)
  · have h : ((0, 0, u.2.2) : SpaceB) =
        ∑ j, ∑ i, u.2.2 j i • basisB (Sum.inr (Sum.inr (j, i))) := by
      simp only [basisB_inr_inr]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd, Matrix.sum_apply,
          Matrix.smul_apply, tensor, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
        simp
    rw [h]
    exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
      smul_mem_BR (hu.2.2 j i) (basisB_mem_BR _)

theorem mem_BR_iff {u : SpaceB} : u ∈ BR ↔ IsDyadicVec u :=
  ⟨fun h => BR_le_dyadicVecs h, mem_BR_of_isDyadicVec⟩

end CFSG.Monster.Griess
