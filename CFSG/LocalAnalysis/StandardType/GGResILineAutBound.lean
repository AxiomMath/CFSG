module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Permutation.FiveTransitive.ThreeGroupTwentySevenNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem not_five_dvd_card_mulAut_of_isPGroup_card_le
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 27) :
    ¬ 5 ∣ Nat.card (MulAut Q) := by
  intro h5
  have hfin : Finite (MulAut Q) := inferInstanceAs (Finite (Q ≃* Q))
  obtain ⟨a, ha⟩ := @exists_prime_orderOf_dvd_card' (MulAut Q) _ hfin 5 ⟨by norm_num⟩ h5
  have ha5 : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h1 : a = 1 :=
    CFSG.FiveTransitive.ThreeGroupTwentySevenNormalizer.aut_eq_one hQ hcard a ha5
  rw [h1, orderOf_one] at ha
  omega

theorem not_five_dvd_card_ggAutomizer_of_card_le
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian 3 A) (hcard : Nat.card A ≤ 27) :
    ¬ 5 ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := by
  have hQ : IsPGroup 3 ↥A := hA.isPGroup
  have hno := not_five_dvd_card_mulAut_of_isPGroup_card_le hQ hcard
  exact fun h5 => hno (h5.trans (Subgroup.card_subgroup_dvd_card _))

theorem GGTorusAutNotDvdSCJ_of_exact_order
    {labJ : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {N : ℕ}
    (hN : ¬ 5 ∣ N)
    (hOrder : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = N) :
    GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hcard hsc _
  by_cases h27 : Nat.card A ≤ 27
  · exact not_five_dvd_card_ggAutomizer_of_card_le hA h27
  · have h81 : 3 ^ 4 ≤ Nat.card A := by
      obtain ⟨k, hk⟩ := @IsPGroup.exists_card_eq 3 ↥A _ ⟨by norm_num⟩ _ hA.isPGroup
      have hlt : (3 : ℕ) ^ 3 < Nat.card A := by
        norm_num
        omega
      rw [hk] at hlt
      have h3k : 3 < k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
    rw [hOrder L' ψ hψ hker hperf A hA hAI h81 hsc]
    exact hN

theorem GGTorusAutNotDvdSCJ_of_exact_order_1152
    {labJ : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)}
    (hOrder : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) :
    GGTorusAutNotDvdSCJ 3 labJ R I 4 5 :=
  GGTorusAutNotDvdSCJ_of_exact_order (by norm_num) hOrder

end CFSG.StandardType

end
