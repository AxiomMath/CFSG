module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem coordinate_inversion_actual_central_cover_local_rank {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) {H : Type*} [Group H] (φ : Y →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {m : ℕ}
    (_hm : 1 ≤ m) (h w : Fin m → H) (hcomm : ∀ i j, Commute (h i) (h j))
    (hord : ∀ i, orderOf (h i) = r) (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) {z : H} (hz : orderOf z = 2)
    (hzh : ∀ i, Commute z (h i)) :
    IsElemAbelian r (Subgroup.closure (Set.range h)) ∧
      Nat.card (Subgroup.closure (Set.range h)) = r ^ m ∧
      (∀ x ∈ (Subgroup.closure (Set.range h)).comap φ,
        ∀ y ∈ (Subgroup.closure (Set.range h)).comap φ, x * y = y * x) ∧
      ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
        IsElemAbelian r A ∧ Nat.card A = r ^ m ∧
        A ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) ∧
        IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) ∧ m ≤ localRank r G := by
  obtain ⟨hDab, hDcard, hF⟩ := inversion_basis_package hφ hker hr hr2 h w hcomm hord hinv hfix
  rw [Fintype.card_fin] at hDcard
  have hzD : ∀ x ∈ Subgroup.closure (Set.range h), Commute z x := by
    intro x hx
    have hle : Subgroup.closure (Set.range h) ≤ Subgroup.centralizer {z} :=
      (Subgroup.closure_le _).2 (by
        rintro _ ⟨i, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (hzh i).eq.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  exact ⟨hDab, hDcard, hF, central_cover_involution_witness Y hφ hker hr hr2 hDab.2 hF hDcard.ge
    hz hzD⟩

end CFSG.RankThree.CentralCover
