module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Kernel
public import CFSG.RankThree.GF2n.Stroth78.Sec3Single

import CFSG.RankThree.GF2n.Stroth78.Sec2Six

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_31 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    (Eset S a).Nonempty ∧ IsRootInvolutionSet (Eset S a) ∧
      (∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 4) ∧
      ∀ α ∈ Eset S a, ∀ α' : Hbar z, α' ∈ Eset S a ↔ ∃ x ∈ Xsub S a, α' = x * α * x⁻¹ := by
  obtain ⟨β, hβR, hβ1⟩ := (Subgroup.bot_or_exists_ne_one (Rbar S a)).resolve_left h.Rbar_ne_bot
  obtain ⟨hne, hroot, h4, hconj⟩ :=
    stroth78_31_of_kernelTwo_eq_bot S h hβR hβ1 (kernelTwo_eq_bot S h h217 hβR hβ1)
  refine ⟨hne, hroot, h4, fun α hα α' => ⟨hconj α hα α', ?_⟩⟩
  rintro ⟨x, -, rfl⟩
  exact Eset_conj_mem S a hα x

end CFSG.RankThree.GF2n.Stroth78
