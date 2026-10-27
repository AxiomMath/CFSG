module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Main
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm37
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BSets
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma_6_2_b
    (h : Counterexample p A θ) :
    ∃ a ∈ A, a ≠ 1 ∧ ¬ NearASolvableII p A (θ a) := by
  by_contra! hcon
  have hns : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ a) := fun a ha ha1 =>
    lemma_5_13 (h.isFunctor.normalized a ha ha1) (hcon a ha ha1)
  obtain ⟨W, hW, hWmax⟩ := near_main h.prime h.odd h.elemAbelian h.card h.isFunctor hns
  refine h.notComplete ⟨W, signalizers_mono_class
    (fun X hX => NearASolvable.hypothesisB h.prime hX) hW, fun X hX => ?_⟩
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hsol : Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
    have hle : X ⊓ Subgroup.centralizer (A : Set G) ≤ θ a ⊓ Subgroup.centralizer (A : Set G) :=
      le_inf ((inf_le_inf_left X (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr ha))).trans (hX.2.2.1 a ha ha1)) inf_le_right
    have : Group.IsSolvable (θ a ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
      (hcon a ha ha1).2.2
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact hWmax X ⟨hX.1, hX.2.1, hX.2.2.1, lemma_5_13 hX.1 ⟨h.elemAbelian, hX.2.2.2, hsol⟩⟩

theorem not_isSolvable_D
    (h : Counterexample p A θ) : ¬ Group.IsSolvable (thetaOf θ A) := by
  obtain ⟨a, ha, ha1, hna⟩ := h.lemma_6_2_b
  intro hD
  refine hna ⟨h.elemAbelian, h.hypC a ha ha1, ?_⟩
  rw [h.isFunctor.inf_centralizer_self ha ha1]
  exact hD

theorem not_isSolvable_apply
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ¬ Group.IsSolvable (θ a) := by
  intro hsol
  apply h.not_isSolvable_D
  have hle : thetaOf θ A ≤ θ a := thetaOf_le_apply ha ha1
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
