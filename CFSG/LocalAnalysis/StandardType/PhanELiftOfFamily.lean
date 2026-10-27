module

public import CFSG.LocalAnalysis.StandardType.PhanEReduction
import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal

theorem PhanFamilyE.range_θ_eq_sup {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {X : Type} [Group X] (S : PhanFamilyE K p f M X)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {i j : Fin n}
    (hij : i < j) (h3 : M i j = 3) :
    (S.θ i j).range = (S.ι i).range ⊔ (S.ι j).range := by
  rw [MonoidHom.range_eq_map, ← B12_sup_B23 hK hq, Subgroup.map_sup, B12, B23,
    ← MonoidHom.range_comp, ← MonoidHom.range_comp, S.left i j hij h3, S.right i j hij h3]

theorem one_lt_card_su_two {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) : 1 < Nat.card (Su K 2 f 2) := by
  have hcard : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hK
    omega
  have hq2 : 2 ≤ 2 ^ f := by
    have h1 : 1 < 2 ^ f := one_lt_pow' (show (1 : ℕ) < 2 by norm_num) hf0
    omega
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv P hP).toEquiv,
    CFSG.LieType.Steinberg.card_SU_two hK]
  have h3 : 3 ≤ (2 ^ f) ^ 2 - 1 := by
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  nlinarith [hq2, h3]

theorem PhanFamilyE.IsUniversal.exists_central_epimorphism
    {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}
    {M : CoxeterMatrix (Fin n)} {Y : Type} [Group Y] {S : PhanFamilyE K 2 f M Y}
    (hS : S.IsUniversal) (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 0 < n)
    (hY : CFSG.IsQuasisimple Y) {X : Type} [Group X] (F : PhanFamilyE K 2 f M X)
    (hFinj : ∀ i, Function.Injective (F.ι i))
    (hgen : (⨆ i, (F.ι i).range) = ⊤) :
    ∃ ψ : Y →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center Y ∧
      (∀ i, ψ.comp (S.ι i) = F.ι i) ∧
      ∀ i j : Fin n, i < j → M i j = 3 → ψ.comp (S.θ i j) = F.θ i j := by
  obtain ⟨ψ, hψ, hθ⟩ := hS X F
  refine ⟨ψ, ?_, ?_, hψ, hθ⟩
  · rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun i => ?_
    rw [← hψ i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hY ?_
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    have hsub : Subsingleton (Su K 2 f 2) := by
      refine ⟨fun a b => hFinj i ?_⟩
      rw [← hψ i, MonoidHom.comp_apply, MonoidHom.comp_apply, hall, hall]
    have hcard : Nat.card (Su K 2 f 2) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h1 : 1 < Nat.card (Su K 2 f 2) := one_lt_card_su_two hK
    omega

theorem phanELiftAt_of_family {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (hn : 0 < n) {M : CoxeterMatrix (Fin n)}
    {Y : LieUniversal} (hY : CFSG.IsQuasisimple Y.K)
    (hfam : ∀ {X : Type} [Group X] (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X),
      WeakPhanSL K 2 f M U W → ∃ F : PhanFamilyE K 2 f M X,
        (∀ i, (F.ι i).range = U i) ∧ ∀ i, Function.Injective (F.ι i)) :
    PhanELiftAt K f M Y := by
  rintro ⟨S, hS⟩ X _ U W hW
  obtain ⟨F, hFι, hFinj⟩ := hfam U W hW
  have hgen : (⨆ i, (F.ι i).range) = ⊤ := by simpa only [hFι] using hW.gen
  obtain ⟨ψ, hsurj, hker, -, -⟩ := hS.exists_central_epimorphism hK hn hY F hFinj hgen
  exact ⟨ψ, hsurj, hker⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
