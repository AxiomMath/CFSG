module

public import CFSG.LocalAnalysis.StandardType.GGPhanStandardGood
public import CFSG.LocalAnalysis.StandardType.PhanELiftFamily
public import CFSG.LocalAnalysis.StandardType.PhanELiftOfFamily
import CFSG.LocalAnalysis.StandardType.PhanELiftQuasi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem PhanFamilyE.IsUniversal.exists_marked_epimorphism_of_weakPhanSL
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {Y : Type} [Group Y]
    {S : PhanFamilyE F 2 f M Y} (hS : S.IsUniversal)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (hM : IsEShape M)
    (hY : CFSG.IsQuasisimple Y) {X : Type} [Group X]
    (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X)
    (hW : WeakPhanSL F 2 f M U W) :
    ∃ ψ : Y →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center Y ∧
      (∀ i, ((S.ι i).range).map ψ = U i) ∧
      ∀ i j : Fin n, i < j → M i j = 3 → ((S.θ i j).range).map ψ = W i j := by
  obtain ⟨T, hT, hinj⟩ := exists_phanFamilyE_of_isEShape hF hM hW
  have hgen : (⨆ i, (T.ι i).range) = ⊤ := by simpa only [hT] using hW.gen
  obtain ⟨ψ, hsurj, hker, hψ, hθ⟩ := hS.exists_central_epimorphism hF
    (by have := hM.1; omega) hY T hinj hgen
  refine ⟨ψ, hsurj, hker, ?_, ?_⟩
  · intro i
    rw [← MonoidHom.range_comp, hψ i, hT i]
  · intro i j hij h3
    rw [← MonoidHom.range_comp, hθ i j hij h3,
      T.range_θ_eq_sup hF (by omega) hij h3, hT i, hT j, ← hW.join i j (ne_of_lt hij)]



theorem PhanEInput2.exists_marked_epimorphism_E6
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {X : Type} [Group X]
    (U : Fin 6 → Subgroup X) (W : Fin 6 → Fin 6 → Subgroup X)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₆ U W) :
    ∃ ψ : (lieUniversal .twistedE6 0 2 f Nat.prime_two).K →* X,
      Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (lieUniversal .twistedE6 0 2 f Nat.prime_two).K ∧
      (∀ i, (((e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range).map ψ = U i) ∧
      ∀ i j : Fin 6, i < j → CoxeterMatrix.E₆ i j = 3 →
        (((e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.θ i j).range).map ψ = W i j := by
  exact PhanFamilyE.IsUniversal.exists_marked_epimorphism_of_weakPhanSL
    (PhanEInput2.standardFamily_isUniversal_E6 hF hq) hF hq isEShape_E₆
    (isQuasisimple_lieUniversal_twistedE6 f (one_le_of_four_le_two_pow hq)) U W hW

theorem PhanEInput2.exists_marked_epimorphism_E7
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X) (W : Fin 7 → Fin 7 → Subgroup X)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₇ U W) :
    ∃ ψ : (lieUniversal .E7 0 2 f Nat.prime_two).K →* X,
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (lieUniversal .E7 0 2 f Nat.prime_two).K ∧
      (∀ i, (((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range).map ψ = U i) ∧
      ∀ i j : Fin 7, i < j → CoxeterMatrix.E₇ i j = 3 →
        (((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.θ i j).range).map ψ = W i j := by
  exact PhanFamilyE.IsUniversal.exists_marked_epimorphism_of_weakPhanSL
    (PhanEInput2.standardFamily_isUniversal_E7 hF hq) hF hq isEShape_E₇
    (isQuasisimple_lieUniversal_E7 f) U W hW

theorem PhanEInput2.exists_marked_epimorphism_E8
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {X : Type} [Group X]
    (U : Fin 8 → Subgroup X) (W : Fin 8 → Fin 8 → Subgroup X)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₈ U W) :
    ∃ ψ : (lieUniversal .E8 0 2 f Nat.prime_two).K →* X,
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (lieUniversal .E8 0 2 f Nat.prime_two).K ∧
      (∀ i, (((e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range).map ψ = U i) ∧
      ∀ i j : Fin 8, i < j → CoxeterMatrix.E₈ i j = 3 →
        (((e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.θ i j).range).map ψ = W i j := by
  exact PhanFamilyE.IsUniversal.exists_marked_epimorphism_of_weakPhanSL
    (PhanEInput2.standardFamily_isUniversal_E8 hF hq) hF hq isEShape_E₈
    (isQuasisimple_lieUniversal_E8 f) U W hW

end CFSG.ClassicalInvolution.Phan.PhanE
