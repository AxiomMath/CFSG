module

public import CFSG.Quasithin.EmptyFaithful.S152NTrans

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6

variable {G : Type} [Group G] [Finite G] {H V : Subgroup G}

omit [Finite G] in
theorem relIndex_sup_pCoreOf_eq {A : Subgroup G} (hA : A ≤ H) :
    (pCoreOf 2 H).relIndex (A ⊔ pCoreOf 2 H) = (A ⊓ pCoreOf 2 H).relIndex A := by
  have hAN : A ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hA.trans (le_normalizer_pCoreOf 2 H)
  rw [A4.relIndex_sup_eq_of_le_normalizer' hAN, inf_comm, Subgroup.inf_relIndex_right]

theorem relIndex_eq_two_of_mem_deltaSet
    (hex : ∃ A : Subgroup G, IsMaxElemAbelian H A ∧ ¬ A ≤ pCoreOf 2 H ∧
      (A ⊓ pCoreOf 2 H).relIndex A = 2) :
    ∀ A ∈ deltaSet H V, (A ⊓ pCoreOf 2 H).relIndex A = 2 := by
  obtain ⟨A', hA', hA'nle, hA'2⟩ := hex
  rintro A ⟨hA, hAnle, hmin, -⟩
  have h1 : Nat.card ↥(A ⊔ pCoreOf 2 H) ≤ Nat.card ↥(A' ⊔ pCoreOf 2 H) := hmin A' hA' hA'nle
  have hrel' : (pCoreOf 2 H).relIndex (A' ⊔ pCoreOf 2 H) = 2 := by
    rw [relIndex_sup_pCoreOf_eq hA'.1, hA'2]
  have e' := Subgroup.relIndex_mul_card (pCoreOf 2 H) (A' ⊔ pCoreOf 2 H)
  rw [inf_eq_left.mpr le_sup_right, hrel'] at e'
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 H) (A ⊔ pCoreOf 2 H)
  rw [inf_eq_left.mpr le_sup_right] at e
  have hne1 : (pCoreOf 2 H).relIndex (A ⊔ pCoreOf 2 H) ≠ 1 := by
    intro h
    exact hAnle (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
  have hpos : (pCoreOf 2 H).relIndex (A ⊔ pCoreOf 2 H) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
  rw [← e, ← e'] at h1
  have h2 : (pCoreOf 2 H).relIndex (A ⊔ pCoreOf 2 H) ≤ 2 := Nat.le_of_mul_le_mul_right h1 hQpos
  rw [← relIndex_sup_pCoreOf_eq hA.1]
  omega

end Gap6

@[expose] def Input15209Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∃ A : Subgroup G, IsMaxElemAbelian H A ∧
      ¬ A ≤ pCoreOf 2 H ∧ (A ⊓ pCoreOf 2 H).relIndex A = 2

theorem input15209Order_of_exists (h : Input15209Exists) : S152N.Input15209Order :=
  fun G _ _ T Mc M hs H hH A hA =>
    Gap6.relIndex_eq_two_of_mem_deltaSet (h G T Mc M hs H hH) A hA

end CFSG.Quasithin
