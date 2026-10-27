module

public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLTypeA
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLLabel
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Families

variable {X : Type*} {m : ℕ}

@[expose] def ggTypeAFam (m : ℕ) (fJ : ℕ → X) (fb fa : X) (i : Fin (m + 2)) : X :=
  if (i : ℕ) < m then fJ i else if (i : ℕ) = m then fb else fa

@[expose] def ggTypeANearFam (m : ℕ) (fθ : X) (fJ : ℕ → X) (fb : X) (i : Fin (m + 2)) : X :=
  if (i : ℕ) = 0 then fθ else if (i : ℕ) ≤ m then fJ ((i : ℕ) - 1) else fb

theorem ggTypeA_trichotomy (i : Fin (m + 2)) : (i : ℕ) < m ∨ (i : ℕ) = m ∨ (i : ℕ) = m + 1 := by
  have := i.isLt
  omega

theorem ggTypeAFam_of_lt {fJ : ℕ → X} {fb fa : X} {i : Fin (m + 2)} (h : (i : ℕ) < m) :
    ggTypeAFam m fJ fb fa i = fJ i := ite_eq_left h

theorem ggTypeAFam_of_eq {fJ : ℕ → X} {fb fa : X} {i : Fin (m + 2)} (h : (i : ℕ) = m) :
    ggTypeAFam m fJ fb fa i = fb := by
  rw [ggTypeAFam, ite_eq_right (by omega), ite_eq_left h]

theorem ggTypeAFam_of_eq_succ {fJ : ℕ → X} {fb fa : X} {i : Fin (m + 2)} (h : (i : ℕ) = m + 1) :
    ggTypeAFam m fJ fb fa i = fa := by
  rw [ggTypeAFam, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem ggTypeANear_trichotomy (i : Fin (m + 2)) :
    (i : ℕ) = 0 ∨ (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m) ∨ (i : ℕ) = m + 1 := by
  have := i.isLt
  omega

theorem ggTypeANearFam_of_eq_zero {fθ : X} {fJ : ℕ → X} {fb : X} {i : Fin (m + 2)}
    (h : (i : ℕ) = 0) : ggTypeANearFam m fθ fJ fb i = fθ := ite_eq_left h

theorem ggTypeANearFam_of_mid {fθ : X} {fJ : ℕ → X} {fb : X} {i : Fin (m + 2)}
    (h : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m) : ggTypeANearFam m fθ fJ fb i = fJ ((i : ℕ) - 1) := by
  rw [ggTypeANearFam, ite_eq_right (by omega), ite_eq_left h.2]

theorem ggTypeANearFam_of_eq_succ {fθ : X} {fJ : ℕ → X} {fb : X} {i : Fin (m + 2)}
    (h : (i : ℕ) = m + 1) : ggTypeANearFam m fθ fJ fb i = fb := by
  rw [ggTypeANearFam, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem range_ggTypeAFam (fJ : ℕ → X) (fb fa : X) :
    Set.range (ggTypeAFam m fJ fb fa) = (fJ '' Set.Iio m ∪ {fb}) ∪ (fJ '' Set.Iio m ∪ {fa}) := by
  ext z
  simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases ggTypeA_trichotomy i with hi | hi | hi
    · exact Or.inl (Or.inl ⟨i, hi, (ggTypeAFam_of_lt hi).symm⟩)
    · exact Or.inl (Or.inr (ggTypeAFam_of_eq hi))
    · exact Or.inr (Or.inr (ggTypeAFam_of_eq_succ hi))
  · rintro ((⟨j, hj, rfl⟩ | rfl) | (⟨j, hj, rfl⟩ | rfl))
    · exact ⟨⟨j, by omega⟩, ggTypeAFam_of_lt hj⟩
    · exact ⟨⟨m, by omega⟩, ggTypeAFam_of_eq rfl⟩
    · exact ⟨⟨j, by omega⟩, ggTypeAFam_of_lt hj⟩
    · exact ⟨⟨m + 1, by omega⟩, ggTypeAFam_of_eq_succ rfl⟩

theorem range_ggTypeANearFam (fθ : X) (fJ : ℕ → X) (fb : X) :
    Set.range (ggTypeANearFam m fθ fJ fb) = (fJ '' Set.Iio m ∪ {fb}) ∪ (fJ '' Set.Iio m ∪ {fθ}) := by
  ext z
  simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases ggTypeANear_trichotomy i with hi | hi | hi
    · exact Or.inr (Or.inr (ggTypeANearFam_of_eq_zero hi))
    · exact Or.inl (Or.inl ⟨(i : ℕ) - 1, by omega, (ggTypeANearFam_of_mid hi).symm⟩)
    · exact Or.inl (Or.inr (ggTypeANearFam_of_eq_succ hi))
  · rintro ((⟨j, hj, rfl⟩ | rfl) | (⟨j, hj, rfl⟩ | rfl))
    · exact ⟨⟨j + 1, by omega⟩, by rw [ggTypeANearFam_of_mid (by simp; omega)]; simp⟩
    · exact ⟨⟨m + 1, by omega⟩, ggTypeANearFam_of_eq_succ rfl⟩
    · exact ⟨⟨j + 1, by omega⟩, by rw [ggTypeANearFam_of_mid (by simp; omega)]; simp⟩
    · exact ⟨⟨0, by omega⟩, ggTypeANearFam_of_eq_zero rfl⟩

end Families

theorem ggCoxeterMatrix_reindex_refl {B : Type*} (M : CoxeterMatrix B) :
    M.reindex (Equiv.refl B) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

section Pairing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ} {hJ : ℕ → M}
  {αJ : ℕ → Module.Dual R M} {ha hb : M} {αa αb : Module.Dual R M}

theorem ggChainRoot_zero_eq {k : ℕ} (hk : k ≤ m) :
    ggChainRoot m αJ αa 0 = (∑ j ∈ Finset.range k, αJ j) + ggChainRoot m αJ αa k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), ggChainRoot_of_lt (by omega : k < m), Finset.sum_range_succ]
    abel

theorem ggChainCoroot_zero_eq {k : ℕ} (hk : k ≤ m) :
    ggChainCoroot m hJ ha 0 = (∑ j ∈ Finset.range k, hJ j) + ggChainCoroot m hJ ha k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), ggChainCoroot_of_lt (by omega : k < m), Finset.sum_range_succ]
    abel

theorem GGChainPairing.chainRoot_zero_apply (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ}
    (hk : k < m) : ggChainRoot m αJ αa 0 (hJ k) = if k = 0 then 1 else 0 := by
  have hkk : ggChainRoot m αJ αa k (hJ k) = 1 := by
    rw [ggChainRoot_of_lt hk, LinearMap.add_apply, hP.chainRoot_succ_apply hk, hP.jj k k hk hk]
    norm_num
  have hsum : ∑ j ∈ Finset.range k, αJ j (hJ k) = if k = 0 then 0 else -1 := by
    split_ifs with hk0
    · subst hk0
      simp
    · rw [Finset.sum_eq_single (k - 1)]
      · rw [hP.jj (k - 1) k (by omega) hk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro j hj hjk
        rw [Finset.mem_range] at hj
        rw [hP.jj j k (by omega) hk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [ggChainRoot_zero_eq hk.le, LinearMap.add_apply, LinearMap.sum_apply, hsum, hkk]
  split_ifs <;> ring

theorem GGChainPairing.apply_chainCoroot_zero (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ}
    (hk : k < m) : αJ k (ggChainCoroot m hJ ha 0) = if k = 0 then 1 else 0 := by
  have hkk : αJ k (ggChainCoroot m hJ ha k) = 1 := by
    rw [ggChainCoroot_of_lt hk, map_add, hP.root_coroot_succ hk, hP.jj k k hk hk]
    norm_num
  have hsum : ∑ j ∈ Finset.range k, αJ k (hJ j) = if k = 0 then 0 else -1 := by
    split_ifs with hk0
    · subst hk0
      simp
    · rw [Finset.sum_eq_single (k - 1)]
      · rw [hP.jj k (k - 1) hk (by omega)]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro j hj hjk
        rw [Finset.mem_range] at hj
        rw [hP.jj k j hk (by omega)]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [ggChainCoroot_zero_eq hk.le, map_add, map_sum, hsum, hkk]
  split_ifs <;> ring

theorem GGChainPairing.typeA_pairing_D (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb) (hu : αa hb = 0) (hv : αb ha = 0) (i j : Fin (m + 2)) :
    ggTypeAFam m αJ αb αa i (ggTypeAFam m hJ hb ha j) = ((CartanMatrix.D (m + 2) i j : ℤ) : R) := by
  have hi' := i.isLt
  have hj' := j.isLt
  rcases ggTypeA_trichotomy i with hi | hi | hi <;> rcases ggTypeA_trichotomy j with hj | hj | hj
  · rw [ggTypeAFam_of_lt hi, ggTypeAFam_of_lt hj, hPa.jj _ _ hi hj]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_lt hi, ggTypeAFam_of_eq hj, hPb.ja _ hi]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_lt hi, ggTypeAFam_of_eq_succ hj, hPa.ja _ hi]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq hi, ggTypeAFam_of_lt hj, hPb.aj _ hj]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq hi, ggTypeAFam_of_eq hj, hPb.aa]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq hi, ggTypeAFam_of_eq_succ hj, hv]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq_succ hi, ggTypeAFam_of_lt hj, hPa.aj _ hj]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq_succ hi, ggTypeAFam_of_eq hj, hu]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeAFam_of_eq_succ hi, ggTypeAFam_of_eq_succ hj, hPa.aa]
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp

theorem GGChainPairing.typeA_pairing_A (hm : 2 ≤ m) (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb) (hθb : ggChainRoot m αJ αa 0 hb = 0)
    (hbθ : αb (ggChainCoroot m hJ ha 0) = 0) (i j : Fin (m + 2)) :
    ggTypeANearFam m (-ggChainRoot m αJ αa 0) αJ αb i
        (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb j) =
      ((CartanMatrix.A (m + 2) i j : ℤ) : R) := by
  have hi' := i.isLt
  have hj' := j.isLt
  rcases ggTypeANear_trichotomy i with hi | hi | hi <;>
    rcases ggTypeANear_trichotomy j with hj | hj | hj
  · rw [ggTypeANearFam_of_eq_zero hi, ggTypeANearFam_of_eq_zero hj, LinearMap.neg_apply, map_neg,
      neg_neg, hPa.chainRoot_chainCoroot 0 (Nat.zero_le _)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_eq_zero hi, ggTypeANearFam_of_mid hj, LinearMap.neg_apply,
      hPa.chainRoot_zero_apply (by omega)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_eq_zero hi, ggTypeANearFam_of_eq_succ hj, LinearMap.neg_apply, hθb]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_mid hi, ggTypeANearFam_of_eq_zero hj, map_neg,
      hPa.apply_chainCoroot_zero (by omega)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_mid hi, ggTypeANearFam_of_mid hj, hPa.jj _ _ (by omega) (by omega)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_mid hi, ggTypeANearFam_of_eq_succ hj, hPb.ja _ (by omega)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_eq_succ hi, ggTypeANearFam_of_eq_zero hj, map_neg, hbθ]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_eq_succ hi, ggTypeANearFam_of_mid hj, hPb.aj _ (by omega)]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [ggTypeANearFam_of_eq_succ hi, ggTypeANearFam_of_eq_succ hj, hPb.aa]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp

end Pairing

section Generation

variable {H : Type*} [Group H]

theorem ggChainProd_mem_closure {m : ℕ} (S : ℕ → H) {k : ℕ} (hk : k ≤ m) :
    ggChainProd m S k ∈ Subgroup.closure (S '' Set.Iio m) := by
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    rw [show k = m by omega, ggChainProd_self]
    exact Subgroup.one_mem _
  | succ d ih =>
    rw [ggChainProd_of_lt S (by omega)]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, by simp; omega, rfl⟩)
      (ih (by omega) (by omega))

theorem closure_union_conj (S : Set H) (a g : H) (hg : g ∈ Subgroup.closure S) :
    Subgroup.closure (S ∪ {g * a * g⁻¹}) = Subgroup.closure (S ∪ {a}) := by
  have hS : ∀ T : Set H, Subgroup.closure S ≤ Subgroup.closure (S ∪ T) := fun T =>
    Subgroup.closure_mono Set.subset_union_left
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact Subgroup.subset_closure (Or.inl hz)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hS _ hg) (Subgroup.subset_closure (Or.inr rfl)))
        (Subgroup.inv_mem _ (hS _ hg))
  · rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact Subgroup.subset_closure (Or.inl hz)
    · have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS {g * z * g⁻¹} hg))
        (Subgroup.subset_closure (Or.inr rfl : g * z * g⁻¹ ∈ S ∪ {g * z * g⁻¹}))) (hS _ hg)
      rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h

end Generation

theorem GGChainPairing.chainCoroot_self_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} (hm : 1 ≤ m) {hJ : ℕ → V}
    {αJ : ℕ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
    (hP : GGChainPairing m hJ αJ ha αa) (S : ℕ → (V ≃ₗ[ZMod p] V))
    (hS : ∀ j < m, ∀ w, S j w = w - αJ j w • hJ j) (T : V ≃ₗ[ZMod p] V)
    (hT : ∀ w, T w = w - αa w • ha) : ggChainCoroot m hJ ha m = ha := by
  have hconj := ggChainConj_apply hP S hS T hT m le_rfl
  have key : ∀ z, ggChainRoot m αJ αa m z • ggChainCoroot m hJ ha m = αa z • ha := by
    intro z
    have h1 := hconj z
    rw [ggChainProd_self, one_mul, inv_one, mul_one, hT] at h1
    exact (sub_right_injective h1).symm
  have h2 : (2 : ZMod p) • ggChainCoroot m hJ ha m = αa (ggChainCoroot m hJ ha m) • ha := by
    rw [← key, hP.chainRoot_chainCoroot m le_rfl]
  have h3 : αJ (m - 1) (ggChainCoroot m hJ ha m) = -1 := by
    have := hP.root_coroot_succ (k := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have h4 : αJ (m - 1) ha = -1 := by
    rw [hP.ja (m - 1) (by omega)]
    simp [show m - 1 + 1 = m by omega]
  have h5 : αa (ggChainCoroot m hJ ha m) = 2 := by
    have := congrArg (αJ (m - 1)) h2
    rw [map_smul, map_smul, h3, h4, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  rw [h5] at h2
  exact smul_right_injective V (zmod_two_ne_zero hp2) h2

theorem linearIndependent_ggTypeANearFam {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} {hJ : ℕ → V} {ha hb : V} (hcm : ggChainCoroot m hJ ha m = ha)
    (hind : LinearIndependent K (ggTypeAFam m hJ hb ha)) :
    LinearIndependent K (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb) := by
  have hc : ggChainCoroot m hJ ha 0 = (∑ j ∈ Finset.range m, hJ j) + ha := by
    rw [ggChainCoroot_zero_eq le_rfl, hcm]
  have hspan : Submodule.span K (Set.range (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb)) =
      Submodule.span K (Set.range (ggTypeAFam m hJ hb ha)) := by
    apply Submodule.span_eq_span
    · rintro _ ⟨i, rfl⟩
      rcases ggTypeANear_trichotomy i with hi | hi | hi
      · rw [ggTypeANearFam_of_eq_zero hi, hc]
        refine Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun j hj => ?_) ?_)
        · rw [Finset.mem_range] at hj
          exact Submodule.subset_span ⟨⟨j, by omega⟩, ggTypeAFam_of_lt hj⟩
        · exact Submodule.subset_span ⟨⟨m + 1, by omega⟩, ggTypeAFam_of_eq_succ rfl⟩
      · rw [ggTypeANearFam_of_mid hi]
        exact Submodule.subset_span ⟨⟨(i : ℕ) - 1, by omega⟩, ggTypeAFam_of_lt (by simp; omega)⟩
      · rw [ggTypeANearFam_of_eq_succ hi]
        exact Submodule.subset_span ⟨⟨m, by omega⟩, ggTypeAFam_of_eq rfl⟩
    · rintro _ ⟨i, rfl⟩
      rcases ggTypeA_trichotomy i with hi | hi | hi
      · rw [ggTypeAFam_of_lt hi]
        exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, by omega⟩, by
          rw [ggTypeANearFam_of_mid (by simp; omega)]
          simp⟩
      · rw [ggTypeAFam_of_eq hi]
        exact Submodule.subset_span ⟨⟨m + 1, by omega⟩, ggTypeANearFam_of_eq_succ rfl⟩
      · rw [ggTypeAFam_of_eq_succ hi]
        have h0 : -ggChainCoroot m hJ ha 0 ∈
            Submodule.span K (Set.range (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb)) :=
          Submodule.subset_span ⟨⟨0, by omega⟩, ggTypeANearFam_of_eq_zero rfl⟩
        have hs : ∑ j ∈ Finset.range m, hJ j ∈
            Submodule.span K (Set.range (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb)) := by
          refine Submodule.sum_mem _ fun j hj => ?_
          rw [Finset.mem_range] at hj
          exact Submodule.subset_span ⟨⟨j + 1, by omega⟩, by
            rw [ggTypeANearFam_of_mid (by simp; omega)]
            simp⟩
        have hha : ha = -(-ggChainCoroot m hJ ha 0) - ∑ j ∈ Finset.range m, hJ j := by
          rw [hc]
          abel
        have hmem := Submodule.sub_mem _ (Submodule.neg_mem _ h0) hs
        rwa [← hha] at hmem
  rw [linearIndependent_iff_card_eq_finrank_span] at hind ⊢
  rw [hind]
  show Module.finrank K (Submodule.span K _) = Module.finrank K (Submodule.span K _)
  rw [hspan]

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

theorem mem_ggInduced_top_of_mem_ggAutomizer {H : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer H Bs) : φ ∈ ggInduced ⊤ Bs := by
  refine Subgroup.closure_induction (p := fun ψ _ => ψ ∈ ggInduced ⊤ Bs) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, -, hgN, hg⟩
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  · exact one_mem_ggInduced ⊤ Bs
  · intro ψ χ _ _ h1 h2
    exact mul_mem_ggInduced h1 h2
  · intro ψ _ h
    exact inv_mem_ggInduced h

theorem ggLin_ggTypeAFam (ι : Additive ↥Bs ≃+ V) {m : ℕ} {φJ : ℕ → MulAut ↥Bs}
    {φa φb : MulAut ↥Bs} {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V}
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) (i : Fin (m + 2)) (w : V) :
    ggLin (p := p) ι (ggTypeAFam m φJ φb φa i) w =
      w - ggTypeAFam m αJ αb αa i w • ggTypeAFam m hJ hb ha i := by
  rcases ggTypeA_trichotomy i with hi | hi | hi
  · rw [ggTypeAFam_of_lt hi, ggTypeAFam_of_lt hi, ggTypeAFam_of_lt hi, hlinJ _ hi]
  · rw [ggTypeAFam_of_eq hi, ggTypeAFam_of_eq hi, ggTypeAFam_of_eq hi, hlinb]
  · rw [ggTypeAFam_of_eq_succ hi, ggTypeAFam_of_eq_succ hi, ggTypeAFam_of_eq_succ hi, hlina]

theorem ggWeylReflectionGroup_typeA_of_eq_zero (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 2 ≤ m) {φJ : ℕ → MulAut ↥Bs} {φa φb : MulAut ↥Bs}
    (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hφb : φb ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) (hu : αa hb = 0)
    (hind : LinearIndependent (ZMod p) (ggTypeAFam m hJ hb ha)) :
    GGWeylReflectionGroup p (Subgroup.closure (φJ '' Set.Iio m ∪ {φb}) ⊔
      Subgroup.closure (φJ '' Set.Iio m ∪ {φa})) := by
  have hv : αb ha = 0 :=
    (ggTypeA_cross_iff hp2 hNT ι (by omega) hφJ hφa hφb hPa hPb hlinJ hlina hlinb).1.mp hu
  have hpair := hPa.typeA_pairing_D hPb hu hv
  have hα : ∀ i, ggTypeAFam m αJ αb αa i (ggTypeAFam m hJ hb ha i) = 2 := fun i => by
    rw [hpair, CartanMatrix.D_diag]
    norm_num
  have hlin : ∀ i, ggLin (p := p) ι (ggTypeAFam m φJ φb φa i) = reflection (hα i) := fun i =>
    ggLin_eq_reflection ι (hα i) (ggLin_ggTypeAFam ι hlinJ hlina hlinb i)
  have hφ : ∀ i, ggTypeAFam m φJ φb φa i ∈ ggInduced ⊤ Bs := fun i => by
    rcases ggTypeA_trichotomy i with hi | hi | hi
    · rw [ggTypeAFam_of_lt hi]
      exact hφJ _ hi
    · rw [ggTypeAFam_of_eq hi]
      exact hφb
    · rw [ggTypeAFam_of_eq_succ hi]
      exact hφa
  have hM : GGIsWeylMatrix (ggCoxeterMatrixD (m + 2)) :=
    Or.inl ⟨m + 2, Equiv.refl _, by omega,
      Or.inr (Or.inr ⟨by omega, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩
  have hCba : CartanMatrix.D (m + 2) ⟨m, by omega⟩ ⟨m + 1, by omega⟩ = 0 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have key := ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM (ggIntCartan_D (m + 2))
    (TauCeti.isFiniteType_cartanMatrix_D (m + 2)) _ hφ ι _ _ hα hlin hind ⟨m + 1, by omega⟩
    ⟨m, by omega⟩ (fun i j _ => hpair i j) hCba
  rwa [range_ggTypeAFam, Subgroup.closure_union] at key

theorem ggWeylReflectionGroup_typeA_of_eq_one (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 2 ≤ m) {φJ : ℕ → MulAut ↥Bs} {φa φb : MulAut ↥Bs}
    (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hφb : φb ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) (hu : αa hb = 1)
    (hind : LinearIndependent (ZMod p) (ggTypeAFam m hJ hb ha)) :
    GGWeylReflectionGroup p (Subgroup.closure (φJ '' Set.Iio m ∪ {φb}) ⊔
      Subgroup.closure (φJ '' Set.Iio m ∪ {φa})) := by
  obtain ⟨hθb, hbθ⟩ := (ggTypeA_label_cases hp2 hNT ι (by omega) hφJ hφa hφb hPa hPb hlinJ hlina
    hlinb (Or.inr hu)).resolve_left fun h => one_ne_zero (hu.symm.trans h.1)
  obtain ⟨hψ, hlinψ⟩ := ggNearEnd_reflection ι hφJ hφa hPa hlinJ hlina
  have hcm : ggChainCoroot m hJ ha m = ha :=
    hPa.chainCoroot_self_eq hp2 (by omega) (fun j => ggLin (p := p) ι (φJ j)) hlinJ
      (ggLin (p := p) ι φa) hlina
  have hpair := hPa.typeA_pairing_A hm hPb hθb hbθ
  have hα : ∀ i, ggTypeANearFam m (-ggChainRoot m αJ αa 0) αJ αb i
      (ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb i) = 2 := fun i => by
    rw [hpair]
    simp [CartanMatrix.A]
  have hlinF : ∀ i w, ggLin (p := p) ι (ggTypeANearFam m
      (ggChainProd m φJ 0 * φa * (ggChainProd m φJ 0)⁻¹) φJ φb i) w =
      w - ggTypeANearFam m (-ggChainRoot m αJ αa 0) αJ αb i w •
        ggTypeANearFam m (-ggChainCoroot m hJ ha 0) hJ hb i := by
    intro i w
    rcases ggTypeANear_trichotomy i with hi | hi | hi
    · rw [ggTypeANearFam_of_eq_zero hi, ggTypeANearFam_of_eq_zero hi,
        ggTypeANearFam_of_eq_zero hi, hlinψ, LinearMap.neg_apply, neg_smul_neg]
    · rw [ggTypeANearFam_of_mid hi, ggTypeANearFam_of_mid hi, ggTypeANearFam_of_mid hi,
        hlinJ _ (by omega)]
    · rw [ggTypeANearFam_of_eq_succ hi, ggTypeANearFam_of_eq_succ hi,
        ggTypeANearFam_of_eq_succ hi, hlinb]
  have hlin : ∀ i, ggLin (p := p) ι (ggTypeANearFam m
      (ggChainProd m φJ 0 * φa * (ggChainProd m φJ 0)⁻¹) φJ φb i) = reflection (hα i) :=
    fun i => ggLin_eq_reflection ι (hα i) (hlinF i)
  have hφ : ∀ i, ggTypeANearFam m (ggChainProd m φJ 0 * φa * (ggChainProd m φJ 0)⁻¹) φJ φb i ∈
      ggInduced ⊤ Bs := fun i => by
    rcases ggTypeANear_trichotomy i with hi | hi | hi
    · rw [ggTypeANearFam_of_eq_zero hi]
      exact hψ
    · rw [ggTypeANearFam_of_mid hi]
      exact hφJ _ (by omega)
    · rw [ggTypeANearFam_of_eq_succ hi]
      exact hφb
  have hM : GGIsWeylMatrix (CoxeterMatrix.A (m + 2)) :=
    Or.inl ⟨m + 2, Equiv.refl _, by omega, Or.inl (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hCba : CartanMatrix.A (m + 2) ⟨m + 1, by omega⟩ ⟨0, by omega⟩ = 0 := by
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  have key := ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM (ggIntCartan_A (m + 2))
    (TauCeti.isFiniteType_cartanMatrix_A (m + 2)) _ hφ ι _ _ hα hlin
    (linearIndependent_ggTypeANearFam hcm hind) ⟨0, by omega⟩ ⟨m + 1, by omega⟩
    (fun i j _ => hpair i j) hCba
  rwa [range_ggTypeANearFam, Subgroup.closure_union,
    closure_union_conj _ _ _ (ggChainProd_mem_closure φJ (Nat.zero_le m))] at key

theorem ggWeylReflectionGroup_typeA (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 2 ≤ m) {φJ : ℕ → MulAut ↥Bs} {φa φb : MulAut ↥Bs}
    (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hφb : φb ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) (hu : αa hb = 0 ∨ αa hb = 1)
    (hind : LinearIndependent (ZMod p) (ggTypeAFam m hJ hb ha)) :
    GGWeylReflectionGroup p (Subgroup.closure (φJ '' Set.Iio m ∪ {φb}) ⊔
      Subgroup.closure (φJ '' Set.Iio m ∪ {φa})) :=
  hu.elim
    (fun h => ggWeylReflectionGroup_typeA_of_eq_zero hp2 hNT ι hm hφJ hφa hφb hPa hPb hlinJ hlina
      hlinb h hind)
    (fun h => ggWeylReflectionGroup_typeA_of_eq_one hp2 hNT ι hm hφJ hφa hφb hPa hPb hlinJ hlina
      hlinb h hind)

end GG

theorem ggCoxeterLabelTypeAInput_of_crossLabel (hX : GGTypeACrossLabelInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
        GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGScalarsOrWeyl' p B Bs x D J →
          ∀ [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
        (ι : Additive ↥Bs ≃+ V) (m : ℕ), 2 ≤ m → ∀ (φJ : ℕ → MulAut ↥Bs) (φa φb : MulAut ↥Bs)
        (hJ : ℕ → V) (αJ : ℕ → Module.Dual (ZMod p) V) (ha hb : V)
        (αa αb : Module.Dual (ZMod p) V),
        GGChainPairing m hJ αJ ha αa → GGChainPairing m hJ αJ hb αb →
        (∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j) →
        (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
        (∀ w, ggLin (p := p) ι φb w = w - αb w • hb) →
        ggAutomizer L Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φb}) →
        ggAutomizer K Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φa}) →
        LinearIndependent (ZMod p) (ggTypeAFam m hJ hb ha) →
        GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hsc _ V _ _ ι m hm φJ φa φb hJ αJ ha hb
    αa αb hPa hPb hlinJ hlina hlinb hL hK hind
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hu := hX G p B Bs x L D J hcfg hOp hID hNT y K hnbr hsc V ι m hm φJ φa φb hJ αJ ha hb αa
    αb hPa hPb hlinJ hlina hlinb hL hK
  have hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs := fun j hj =>
    mem_ggInduced_top_of_mem_ggAutomizer (H := L)
      (by rw [hL]; exact Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩))
  have hφb : φb ∈ ggInduced ⊤ Bs := mem_ggInduced_top_of_mem_ggAutomizer (H := L)
    (by rw [hL]; exact Subgroup.subset_closure (Or.inr rfl))
  have hφa : φa ∈ ggInduced ⊤ Bs := mem_ggInduced_top_of_mem_ggAutomizer (H := K)
    (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
  rw [hL, hK]
  exact ggWeylReflectionGroup_typeA hp2 hNT ι hm hφJ hφa hφb hPa hPb hlinJ hlina hlinb hu hind

end CFSG.StandardType
