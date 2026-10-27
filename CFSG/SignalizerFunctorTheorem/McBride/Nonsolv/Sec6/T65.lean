module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaNs_mem_nsSet
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaNs p A θ a ∈ nsSet p A (θ a) :=
  theorem_5_16_a (h.kSetting_apply ha ha1)

theorem thetaNs_le
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaNs p A θ a ≤ θ a :=
  (h.thetaNs_mem_nsSet ha ha1).1

theorem isFunctor_thetaNs
    (h : Counterexample p A θ) : IsFunctor p A (thetaNs p A θ) := by
  refine ⟨fun a ha ha1 => (h.thetaNs_le ha ha1).trans (h.isFunctor.le_centralizer a ha ha1),
    fun a ha ha1 => (h.isFunctor.coprime a ha ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (h.thetaNs_le ha ha1)),
    fun a ha ha1 => (h.thetaNs_mem_nsSet ha ha1).2.2.1, ?_⟩
  intro a ha ha1 b hb hb1
  have hba := h.thetaNs_le ha ha1
  have hYle : thetaNs p A θ a ⊓ Subgroup.centralizer {b} ≤ θ b :=
    (inf_le_inf_right _ hba).trans (h.isFunctor.balance a ha ha1 b hb hb1)
  have hY : thetaNs p A θ a ⊓ Subgroup.centralizer {b} ∈ nsSet p A (θ b) := by
    refine ⟨hYle, ?_, ?_, ?_⟩
    ·
      intro d hd
      have hdb : d ∈ θ a ⊓ Subgroup.centralizer (A : Set G) := by
        rw [h.isFunctor.inf_centralizer_self ha ha1, ← h.isFunctor.inf_centralizer_self hb hb1]
        exact hd
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨(h.thetaNs_mem_nsSet ha ha1).2.1 hdb, ?_⟩
      exact mem_normalizer_centralizer_singleton
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) hd.2)
    · intro a' ha'
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨(h.thetaNs_mem_nsSet ha ha1).2.2.1 ha', ?_⟩
      refine mem_normalizer_centralizer_singleton ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_mem_of_isMulCommutative h.elemAbelian.1 ha' hb
    · refine ⟨h.elemAbelian, hypB_mono hYle (h.hypC b hb hb1), ?_⟩
      have hle : thetaNs p A θ a ⊓ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (A : Set G) ≤
          thetaNs p A θ a ⊓ Subgroup.centralizer (A : Set G) :=
        inf_le_inf_right _ inf_le_left
      have : Group.IsSolvable (thetaNs p A θ a ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
        (h.thetaNs_mem_nsSet ha ha1).2.2.2.2.2
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact le_iSup₂_of_le _ hY le_rfl

theorem hypB_thetaNs
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    signalizerMcBrideHypothesisB p (thetaNs p A θ a) :=
  (h.thetaNs_mem_nsSet ha ha1).2.2.2.2.1

theorem theorem_6_5_a
    (h : Counterexample p A θ) :
    IsFunctor p A (thetaNs p A θ) ∧
      (∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (thetaNs p A θ a)) ∧
      IsCompleteIn (Msig p A (thetaNs p A θ)) := by
  refine ⟨h.isFunctor_thetaNs, fun a ha ha1 => h.hypB_thetaNs ha ha1, ?_⟩
  have hlt : size A (thetaNs p A θ) < size A θ := by
    obtain ⟨a, ha, ha1, hna⟩ := h.lemma_6_2_b
    refine size_lt_size (fun a ha ha1 => h.thetaNs_le ha ha1) ⟨a, ha, ha1, fun heq => hna ?_⟩
    have h1 := (h.thetaNs_mem_nsSet ha ha1).2.2.2
    rwa [heq] at h1
  exact h.complete_of_size_lt ⟨h.prime, h.odd, h.elemAbelian, h.card, h.isFunctor_thetaNs,
    fun a ha ha1 => h.hypB_thetaNs ha ha1⟩ hlt

theorem theorem_6_5_b
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {X : Subgroup G} (hX : IsDAInvariant A (θ a) X) (hK : kOf X = X) :
    X ≤ Subgroup.normalizer (thetaNs p A θ a : Set G) :=
  theorem_5_16_b (h.kSetting_apply ha ha1) hX hK

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
