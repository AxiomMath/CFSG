module

public import CFSG.RankThree.GF2n.Stroth78.Sec3One

import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.GroupTheory.ThreeTranspositions.NoLine

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_35 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α β : Hbar z} (hα : α ∈ Tset S a) (hβ : β ∈ Tset S a) : α * β ∉ Tset S a := by
  obtain ⟨-, hroot, -, hclass⟩ := stroth78_31 S h h217
  intro hαβ
  have hclass' : ∀ d ∈ Eset S a, ∀ e ∈ Eset S a,
      ∃ x ∈ Subgroup.closure (Eset S a), e = x * d * x⁻¹ := by
    intro d hd e he
    exact (hclass d hd e).mp he
  exact CFSG.GroupTheory.ThreeTranspositions.mul_not_mem (D := Eset S a)
    (fun d hd => hroot.1 d hd) h3 hclass'
    (Tset_subset_Eset S a hα) (Tset_subset_Eset S a hβ) (Tset_subset_Eset S a hαβ)

theorem card_Rbar_eq_two (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3) :
    Nat.card (Rbar S a) = 2 := by
  obtain ⟨-, hroot, -, -⟩ := stroth78_31 S h h217
  obtain ⟨⟨r, hr⟩, hrne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hr1 : r ≠ 1 := fun h1 => hrne (Subtype.ext h1)
  have hr2 : orderOf r = 2 :=
    hroot.1 r (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hr hr1))
  have hrinv : r⁻¹ = r :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two, hr2] using pow_orderOf_eq_one r)
  have hmem : ∀ s ∈ Rbar S a, s = 1 ∨ s = r := by
    intro s hs
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      by_contra hsr
      have hrs : r * s ∈ Rbar S a := (Rbar S a).mul_mem hr hs
      have hrs1 : r * s ≠ 1 := by
        intro h1
        apply hsr
        rw [show s = r⁻¹ * (r * s) by group, h1, hrinv, mul_one]
      exact stroth78_35 S h h217 h3 (h.mem_Tset_of_mem_Rbar hr hr1)
        (h.mem_Tset_of_mem_Rbar hs hs1) (h.mem_Tset_of_mem_Rbar hrs hrs1)
  refine (Nat.card_eq_two_iff' (1 : ↥(Rbar S a))).mpr ⟨⟨r, hr⟩, hrne, ?_⟩
  intro y hy
  have hy1 : (y : Hbar z) ≠ 1 := fun h1 => hy (Subtype.ext h1)
  rcases hmem (y : Hbar z) y.2 with h1 | h1
  · exact absurd h1 hy1
  · exact Subtype.ext h1

end CFSG.RankThree.GF2n.Stroth78
