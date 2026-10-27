module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {H : Type*} [Group H]

theorem commutator_finsetSup_le {ι : Type*} (s : Finset ι) (X : ι → Subgroup H) (Y Z : Subgroup H)
    [Y.Normal] (h : ∀ i ∈ s, ⁅X i, Y⁆ ≤ Z) : ⁅s.sup X, Y⁆ ≤ Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Subgroup.commutator_bot_left]
  | insert i s hi ih =>
    rw [Finset.sup_insert, Subgroup.commutator_sup_right]
    exact sup_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

noncomputable def lcsTop (M : Subgroup H) : ℕ → Subgroup H
  | 0 => ⊤
  | a + 1 => M.lowerCentralSeries a

theorem lcsTop_normal (M : Subgroup H) [M.Normal] (a : ℕ) : (lcsTop M a).Normal := by
  cases a with
  | zero => exact Subgroup.normal_top
  | succ a => exact Subgroup.lowerCentralSeries_normal M a

theorem commutator_lcsTop_le (M : Subgroup H) [M.Normal] (a : ℕ) :
    ⁅lcsTop M a, M⁆ ≤ lcsTop M (a + 1) := by
  cases a with
  | zero => exact Subgroup.commutator_le_right _ _
  | succ a => exact le_rfl

theorem commutator_lcsTop_le_self (M : Subgroup H) [M.Normal] (a : ℕ) (N : Subgroup H) :
    ⁅lcsTop M a, N⁆ ≤ lcsTop M a := by
  have := lcsTop_normal M a
  exact Subgroup.commutator_le_left _ _

noncomputable def fittingBound (M N : Subgroup H) (k : ℕ) : Subgroup H :=
  (Finset.range (k + 2)).sup fun a => lcsTop M a ⊓ lcsTop N (k + 1 - a)

theorem le_fittingBound (M N : Subgroup H) (k a : ℕ) (ha : a ≤ k + 1) :
    lcsTop M a ⊓ lcsTop N (k + 1 - a) ≤ fittingBound M N k :=
  Finset.le_sup (f := fun a => lcsTop M a ⊓ lcsTop N (k + 1 - a))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

theorem lowerCentralSeries_sup_le_fittingBound (M N : Subgroup H) [M.Normal] [N.Normal]
    (k : ℕ) : (M ⊔ N).lowerCentralSeries k ≤ fittingBound M N k := by
  induction k with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero]
    refine sup_le ?_ ?_
    · refine le_trans ?_ (le_fittingBound M N 0 1 le_rfl)
      exact le_inf le_rfl le_top
    · refine le_trans ?_ (le_fittingBound M N 0 0 (Nat.zero_le 1))
      exact le_inf le_top le_rfl
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    refine le_trans (Subgroup.commutator_mono_left ih) ?_
    refine commutator_finsetSup_le _ _ _ _ fun a ha => ?_
    have ha' : a ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have := lcsTop_normal M a
    have := lcsTop_normal N (k + 1 - a)
    rw [Subgroup.commutator_sup_left]
    refine sup_le ?_ ?_
    ·
      refine le_trans ?_ (le_fittingBound M N (k + 1) (a + 1) (by omega))
      refine le_inf ?_ ?_
      · exact le_trans (Subgroup.commutator_mono_left inf_le_left) (commutator_lcsTop_le M a)
      · have h : k + 1 + 1 - (a + 1) = k + 1 - a := by omega
        rw [h]
        exact le_trans (Subgroup.commutator_mono_left inf_le_right)
          (commutator_lcsTop_le_self N _ M)
    ·
      refine le_trans ?_ (le_fittingBound M N (k + 1) a (by omega))
      refine le_inf ?_ ?_
      · exact le_trans (Subgroup.commutator_mono_left inf_le_left)
          (commutator_lcsTop_le_self M a N)
      · have h : k + 1 + 1 - a = k + 1 - a + 1 := by omega
        rw [h]
        exact le_trans (Subgroup.commutator_mono_left inf_le_right)
          (commutator_lcsTop_le N (k + 1 - a))

theorem lcsTop_eq_bot (M : Subgroup H) {c a : ℕ} (hM : M.lowerCentralSeries c = ⊥)
    (ha : c + 1 ≤ a) : lcsTop M a = ⊥ := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [lcsTop, eq_bot_iff, ← hM]
  exact M.lowerCentralSeries_antitone (by omega)

theorem fitting_lowerCentralSeries_eq_bot (M N : Subgroup H) [M.Normal] [N.Normal] {c₁ c₂ : ℕ}
    (hM : M.lowerCentralSeries c₁ = ⊥) (hN : N.lowerCentralSeries c₂ = ⊥) :
    (M ⊔ N).lowerCentralSeries (c₁ + c₂) = ⊥ := by
  rw [eq_bot_iff]
  refine le_trans (lowerCentralSeries_sup_le_fittingBound M N (c₁ + c₂)) ?_
  refine Finset.sup_le fun a ha => ?_
  by_cases hac : c₁ + 1 ≤ a
  · rw [lcsTop_eq_bot M hM hac]
    exact inf_le_left
  · rw [lcsTop_eq_bot N hN (by omega : c₂ + 1 ≤ c₁ + c₂ + 1 - a)]
    exact inf_le_right

variable {G : Type*} [Group G]

theorem fitting_lowerCentralSeries_sup_eq_bot (A B : Subgroup G)
    (hA : A ⊔ B ≤ Subgroup.normalizer (A : Set G)) (hB : A ⊔ B ≤ Subgroup.normalizer (B : Set G))
    {c₁ c₂ : ℕ} (hAc : A.lowerCentralSeries c₁ = ⊥) (hBc : B.lowerCentralSeries c₂ = ⊥) :
    (A ⊔ B).lowerCentralSeries (c₁ + c₂) = ⊥ := by
  set K := A ⊔ B with hK
  have hAK : A ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  set A' := A.subgroupOf K
  set B' := B.subgroupOf K
  have : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hA
  have : B'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hB
  have hmapA : A'.map K.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAK]
  have hmapB : B'.map K.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
  have hinj : Function.Injective K.subtype := K.subtype_injective
  have hA' : A'.lowerCentralSeries c₁ = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ hinj, Subgroup.map_lowerCentralSeries, hmapA,
      hAc]
  have hB' : B'.lowerCentralSeries c₂ = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ hinj, Subgroup.map_lowerCentralSeries, hmapB,
      hBc]
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← Subgroup.map_injective hinj |>.eq_iff, Subgroup.map_sup, hmapA, hmapB,
      Subgroup.map_top, Subgroup.range_subtype]
  have h := fitting_lowerCentralSeries_eq_bot A' B' hA' hB'
  rw [hsup] at h
  rw [← Subgroup.top_subtype_lowerCentralSeries, h, Subgroup.map_bot]

end Sec6

end CFSG.Walter.W67
