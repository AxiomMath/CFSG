module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame
import CFSG.LocalAnalysis.WeakClosure81.FiveSeven
import CFSG.LocalAnalysis.WeakClosure81.ThreeOne
import CFSG.Quasithin.Vol2.Ch12Sec6P31b

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem asc80ThmBCase_alt :
    Asc80ThmBCase fun X _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  intro G _ _ H A M hs hnab hcat hAH hA hM
  obtain ⟨n, hn5, ⟨e⟩⟩ := hcat
  have hn4 : 4 < n := by omega
  have hsetup := asc80BSetup hs hnab hAH hA hM
  have h1 : (maxOver H A).ncard = 1 := by
    rw [hM]
    exact Set.ncard_singleton M
  obtain ⟨⟨e5⟩, hSyl⟩ := five_seven r3_1_holds hsetup.sec5 hn4 ⟨e⟩ h1
  refine ⟨⟨2, Or.inl ?_⟩, ?_⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    obtain ⟨eL⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
    exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
      inferInstance, inferInstance, hK, ⟨e5.trans eL.symm⟩⟩
  ·
    let B : Subgroup G := H ⊓ Subgroup.normalizer (A : Set G)
    have hSylTwo : CFSG.QuasithinUnique.IsSylowTwoOf A H := hSyl
    have hBcard : Nat.card ↥B = 12 :=
      CFSG.Quasithin.H13.S126P31.card_inf_normalizer e5 hSylTwo
    have hHcard : Nat.card ↥H = 60 := CFSG.Quasithin.H13.S126P31.card_of_alt5 e5
    have hAB : A ≤ B := le_inf hAH Subgroup.le_normalizer
    have hBH : B ≤ H := inf_le_left
    have hBlt : B < H := by
      refine lt_of_le_of_ne hBH ?_
      intro hBH'
      have hcard : Nat.card ↥H = 12 := by rw [← hBH']; exact hBcard
      omega
    have hBM : B ≤ M := hsetup.le_of_lt B hAB hBlt
    have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp hM).1
    rcases CFSG.Quasithin.H13.S126P31.eq_or_eq_of_le_normalizer e5 hSylTwo hBM hMmax.1.le with
      hMB | hMH
    · exact ⟨A, hSyl, hMB⟩
    · exact absurd hMH (ne_of_lt hMmax.1)

end CFSG.LocalAnalysis.WeakClosure81

end
