module

public import CFSG.Quasithin.Vol2.Ch11SecOE7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1

variable {G : Type} [Group G] [Finite G]

theorem le_nParam_of_forall_isE_le {n : ℕ} {T A P : Subgroup G} (hn : 2 ≤ n)
    (hT : IsSylowIn 2 T ⊤) (hP : P ≠ ⊤) (hA : IsElemAbelian 2 A)
    (hle : ∀ g : G, A1b.conjSub g A ≤ T → ∀ K : Subgroup G,
      IsE (n - 1) ⊤ T (A1b.conjSub g A) K → K ≤ P)
    (hN : Subgroup.normalizer
      (weakClosure T {B | ∃ g : G, B = A1b.conjSub g A} : Set G) ≤ P) :
    (n : ℕ∞) ≤ nParam (⊤ : Subgroup G) := by
  set Ω : Set (Subgroup G) := {B | ∃ g : G, B = A1b.conjSub g A} with hΩdef
  have hΩ : IsInvColl ⊤ Ω := isInvColl_conj hA
  have hE : eGen (n - 1) ⊤ T Ω ≤ P := by
    refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_
    obtain ⟨g, rfl⟩ := hB
    exact hle g hBT K hK
  have hnot : ¬ InEFor (n - 1) ⊤ T := by
    intro h
    have h1 := h Ω hΩ
    rw [top_inf_eq] at h1
    exact hP (top_le_iff.mp (h1 ▸ sup_le hE hN))
  by_contra hlt
  rw [not_le] at hlt
  have hn' : (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 := by
    rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm]
    simp
  rw [hn', ENat.lt_add_one_iff (ENat.natCast_ne_top _)] at hlt
  exact hnot ((nParam_le_iff (by omega)).1 hlt T hT)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
