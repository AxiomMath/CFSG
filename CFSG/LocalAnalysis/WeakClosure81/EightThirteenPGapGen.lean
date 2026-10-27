module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem centralKData_of_card_center_four {M : Type} [Group M] [Finite M] {S : Subgroup M}
    (hZ : Nat.card ↥(S ⊓ centralizer (S : Set M)) = 4)
    (h : CentralKData S (S ⊓ centralizer (S : Set M))) :
    ∀ A : Subgroup M, A ≤ S → A ≤ centralizer (S : Set M) → Nat.card ↥A = 4 →
      CentralKData S A := by
  intro A hAS hAc hA4
  have hAZ : A ≤ S ⊓ centralizer (S : Set M) :=
    fun a ha => Subgroup.mem_inf.mpr ⟨hAS ha, hAc ha⟩
  have hAeq : A = S ⊓ centralizer (S : Set M) :=
    Subgroup.eq_of_le_of_card_ge hAZ (by rw [hZ, hA4])
  exact hAeq ▸ h

theorem choiceOfKTop_of_central_data {M : Type} [Group M] [Finite M] (rk : Prop)
    (h : ∀ S : Subgroup M, IsSylowIn 2 S (⊤ : Subgroup M) →
      (∀ A : Subgroup M, A ≤ S → A ≤ centralizer (S : Set M) → IsElemAbelian 2 A →
        Nat.card ↥A = 4 → TISIn (⊤ : Subgroup M) A → CentralKData S A) ∧
      ((∀ x ∈ S, x * x = 1 → x ∈ centralizer (S : Set M)) ∨ RankTwoParabData S)) :
    ChoiceOfKTop M rk := by
  classical
  intro S A hS hAS hAe hA4 _hK1 hTIS
  obtain ⟨hcen, hcase⟩ := h S hS
  by_cases hcent : ∀ a ∈ A, a ∈ centralizer (S : Set M)
  ·
    obtain ⟨K, hAK, hnA, hshape, hsyl, hidx⟩ := hcen A hAS hcent hAe hA4 hTIS
    refine ⟨K, le_top, hAK, hnA, hshape, hsyl, hidx, ?_⟩
    intro _ hnot
    exact absurd (fun a ha s hs =>
      (Subgroup.mem_centralizer_iff.mp (hcent a ha) s hs).symm) hnot
  ·
    rcases hcase with hleft | hRTP
    · exfalso
      obtain ⟨a₀, ha₀⟩ := not_forall.mp hcent
      obtain ⟨ha₀A, ha₀not⟩ := not_imp.mp ha₀
      exact ha₀not (hleft a₀ (hAS ha₀A) (by rw [← pow_two]; exact hAe.2 a₀ ha₀A))
    · obtain ⟨P, hmax, hSK, hq, hidx, hcomm⟩ := hRTP
      have hex : ∃ i : Fin 2, ¬ A ≤ oTwoMod ⊥ (oddResMod ⊥ (P i)) := by
        by_contra hc
        have hAll : ∀ i, A ≤ oTwoMod ⊥ (oddResMod ⊥ (P i)) := by
          intro i
          by_contra hi
          exact hc ⟨i, hi⟩
        exact hcent fun a ha => Subgroup.mem_centralizer_iff.mpr fun s hs =>
          (hcomm a (hAll 0 ha) (hAll 1 ha) s hs).symm
      obtain ⟨i, hAi⟩ := hex
      refine ⟨oddResMod ⊥ (P i), le_top, hAS.trans (hSK i), hAi, hq i, ?_, hidx i, ?_⟩
      · rw [inf_eq_left.mpr (hSK i)]
        exact ⟨hSK i, hS.isPGroup, fun h2 => hS.not_dvd_relIndex
          ((Subgroup.relIndex_mul_relIndex S (oddResMod ⊥ (P i)) ⊤
            (hSK i) le_top) ▸ dvd_mul_of_dvd_left h2 _)⟩
      · intro _ _
        exact ⟨P i, hmax i, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
