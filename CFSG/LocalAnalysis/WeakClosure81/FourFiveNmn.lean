module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveComp
public import CFSG.Quasithin.Background.E1SolvProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem fourFive_nmn_subset {Q : Type} [Group Q] [Finite Q] {j : ℕ} {T N : Subgroup Q}
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) (hN : FourFiveNMN N)
    (hdich : ∀ J : Subgroup Q, IsComponentOf J N →
      J ≤ E1.eGen j ⊤ T Ω ⊔ T ∨ J ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set Q)) :
    (N : Set Q) ⊆ (E1.eGen j ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) := by
  classical
  let E : Subgroup Q := E1.eGen j ⊤ T Ω
  let W : Subgroup Q := E1.weakClosure T Ω
  let Nrm : Subgroup Q := Subgroup.normalizer (W : Set Q)
  let N₁ : Subgroup Q := ⨆ (J : Subgroup Q) (_ : IsComponentOf J N ∧ J ≤ E ⊔ T), J
  let N₂ : Subgroup Q := ⨆ (J : Subgroup Q) (_ : IsComponentOf J N ∧ ¬ J ≤ E ⊔ T), J
  have hTE : T ≤ Subgroup.normalizer (E : Set Q) := E1.le_normalizer_eGen j hΩ
  have hTN : T ≤ Nrm := E1.le_normalizer_weakClosure hΩ
  have hEsup : (↑(E ⊔ T) : Set Q) = (E : Set Q) * (T : Set Q) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E T hTE
  have hN₁_le : N₁ ≤ E ⊔ T :=
    iSup₂_le (f := fun J (_ : IsComponentOf J N ∧ J ≤ E ⊔ T) => J) fun _ hJ => hJ.2
  have hN₂_le : N₂ ≤ Nrm :=
    iSup₂_le (f := fun J (_ : IsComponentOf J N ∧ ¬ J ≤ E ⊔ T) => J) fun J hJ =>
      (hdich J hJ.1).resolve_left hJ.2
  have hN_le : N ≤ N₁ ⊔ N₂ := by
    rw [← fourFive_nmn_components_sup hN]
    refine iSup₂_le fun J hJ => ?_
    by_cases hJT : J ≤ E ⊔ T
    · exact (le_iSup₂ (f := fun J (_ : IsComponentOf J N ∧ J ≤ E ⊔ T) => J) J
        ⟨hJ, hJT⟩).trans le_sup_left
    · exact (le_iSup₂ (f := fun J (_ : IsComponentOf J N ∧ ¬ J ≤ E ⊔ T) => J) J
        ⟨hJ, hJT⟩).trans le_sup_right
  have hN₁cent : N₁ ≤ Subgroup.centralizer (N₂ : Set Q) := by
    refine iSup₂_le (f := fun J (_ : IsComponentOf J N ∧ J ≤ E ⊔ T) => J) fun J hJ => ?_
    refine (Subgroup.le_centralizer_iff (H := J) (K := N₂)).mpr ?_
    refine iSup₂_le (f := fun J' (_ : IsComponentOf J' N ∧ ¬ J' ≤ E ⊔ T) => J')
      fun J' hJ' => ?_
    have hne : J' ≠ J := by
      rintro rfl
      exact hJ'.2 hJ.2
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (fourFive_nmn_components_commute hN hJ'.1 hJ.1 hne)
  have hN₁N₂ : N₁ ≤ Subgroup.normalizer (N₂ : Set Q) :=
    hN₁cent.trans (Subgroup.centralizer_le_normalizer (N₂ : Set Q))
  have hN₁N₂prod : (↑(N₁ ⊔ N₂) : Set Q) = (N₁ : Set Q) * (N₂ : Set Q) :=
    Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ hN₁N₂
  intro x hx
  have hx' : x ∈ (N₁ : Set Q) * (N₂ : Set Q) := by
    rw [← hN₁N₂prod]
    exact hN_le hx
  rw [Set.mem_mul] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have ha' : a ∈ (E : Set Q) * (T : Set Q) := hEsup ▸ hN₁_le ha
  rw [Set.mem_mul] at ha'
  obtain ⟨e, he, t, ht, rfl⟩ := ha'
  exact Set.mem_mul.mpr ⟨e, he, t * b, Nrm.mul_mem (hTN ht) (hN₂_le hb), by group⟩

end CFSG.LocalAnalysis.WeakClosure81
