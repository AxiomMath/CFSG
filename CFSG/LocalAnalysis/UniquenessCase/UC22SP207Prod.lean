module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207L2
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207U3
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.LocalAnalysis.UniquenessCase.UC22P20l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem uc22sp207_hasCentralLongest_szL2Product {X : Type}
    [Group X] {n : ℕ} (h : IsSzL2Product X n) : HasCentralLongest X := by
  obtain ⟨A, C, _, _, ⟨e⟩, hA, hC⟩ := h
  have hsz : ∀ {Y : Type} [Group Y], (IsSz Y n ∨ IsL2 Y n) → HasCentralLongest Y := fun h =>
    h.elim uc22sp207_hasCentralLongest_Sz uc22sp207_hasCentralLongest_L2
  exact ((hsz hA).prod (hsz hC)).of_mulEquiv e.symm

theorem uc22sp207_hasCentralLongest_centralSquare {X : Type} [Group X] [Finite X]
    (hX : CFSG.pCore 2 X = ⊥) (h : IsSU3CentralSquare X) : HasCentralLongest X := by
  obtain ⟨K₁, K₂, hsup, hcomm, h₁, h₂, -⟩ := h
  have hcen : ∀ {K K' : Subgroup X}, K ⊔ K' = ⊤ → (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) →
      ¬ 2 ∣ Nat.card (center K) := fun {K K'} hsup hcomm =>
    uc22p20l_not_two_dvd_card_center hX K.subtype K.subtype_injective fun z hz => by
      have hle : K ⊔ K' ≤ centralizer {(z : X)} := sup_le
        (fun k hk => mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_center_iff.1 hz ⟨k, hk⟩)))
        (fun b hb => mem_centralizer_singleton_iff.2 (hcomm _ z.2 b hb).symm)
      exact mem_center_iff.2 fun x => mem_centralizer_singleton_iff.1 (hle (hsup ▸ mem_top x))
  obtain ⟨φ, hφ, hker⟩ := uc22p20l_exists_hom_central hsup hcomm
  exact ((uc22sp207_hasCentralLongest_SU3 (hcen hsup hcomm) h₁).prod
    (uc22sp207_hasCentralLongest_SU3 (hcen (sup_comm K₁ K₂ ▸ hsup)
      fun a ha b hb => (hcomm b hb a ha).symm) h₂)).map φ hφ hker

end CFSG.LocalAnalysis.UniquenessCase.UC22
