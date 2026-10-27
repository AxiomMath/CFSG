module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQ
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQPSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQPSU
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
import CFSG.GroupTheory.WeirSylow.UniqueE27LinearFour
import CFSG.GroupTheory.WeirSylow.UniqueE27UnitaryFour
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Realize

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open CFSG.GroupTheory
open CFSG.GroupTheory.WeirSylow
  (uniqueElemSylow_statedProj_statedSL_four uniqueElemSylow_statedProj_statedSU_four
   scalar_pow_four_eq_one_of_mem_statedSL)

private theorem exists_isSumZeroCoords_of_stdDiag_model {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)}
    (hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ H → c ^ 4 = 1)
    {ζ : CubeRoot K} (hD : D₀ ζ ≤ H) {A₀ : Subgroup H}
    (h₀ : IsSumZeroCoords A₀ (stdDiagHomH ζ hD)) (hU : UniqueElemSylow 3 3 (StatedProj H))
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj H)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c := by
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 4) K).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H Nat.prime_three (by norm_num) hscal
  have hZ' : ¬ 3 ∣ Nat.card Z := by rw [hZ, Subgroup.card_bot]; norm_num
  exact IsSumZeroCoords.exists_of_model h₀ _ hN hU Z hZ' e hA h27

theorem forall_le_pRank_centralizer_of_stdDiag_model {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)}
    (hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ H → c ^ 4 = 1)
    {ζ : CubeRoot K} (hD : D₀ ζ ≤ H) {A₀ : Subgroup H}
    (h₀ : IsSumZeroCoords A₀ (stdDiagHomH ζ hD)) (hU : UniqueElemSylow 3 3 (StatedProj H))
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj H) {r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hroot : ∀ S : Set (Multiplicative (Fin 4 → ZMod 3)),
      ((∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) ∨
        ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer (stdDiagHomH ζ hD '' S)))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer (X : Set Y))) ∧
    ∀ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer
        ({c (Multiplicative.ofAdd ![1, 1, -1, -1]), c (Multiplicative.ofAdd ![1, -1, 0, 0])} :
          Set Y)) := by
  have hr1 : 1 < r := hr.one_lt
  have key : ∀ S : Set (Multiplicative (Fin 4 → ZMod 3)),
      ((∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) ∨
        ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) →
      ∀ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c →
        f ≤ CFSG.Open.pRank r (Subgroup.centralizer (c '' S)) :=
    fun S hS c hc => IsSumZeroCoords.le_pRank_centralizer_of_stdDiagHomH hscal hD h₀ hU Z hZ e hc S
      hr hr2 (hroot S hS)
  refine ⟨fun X hXA hX3 => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc⟩ := exists_isSumZeroCoords_of_stdDiag_model hscal hD h₀ hU Z hZ e hA h27
    refine IsSumZeroCoords.le_pRank_centralizer_of_points hr1 hc ?_ ?_ ?_ X hXA hX3
    · have := key {Multiplicative.ofAdd ![1, 1, -1, -1]} (Or.inl (by simp)) c hc
      rwa [Set.image_singleton] at this
    · have := key {Multiplicative.ofAdd ![1, -1, 0, 0]} (Or.inl (by simp)) c hc
      rwa [Set.image_singleton] at this
    · have := key {Multiplicative.ofAdd ![1, 1, 1, 0]} (Or.inr (by simp)) c hc
      rwa [Set.image_singleton] at this
  · have := key {Multiplicative.ofAdd ![1, 1, -1, -1], Multiplicative.ofAdd ![1, -1, 0, 0]}
      (Or.inl (by simp)) c hc
    rwa [Set.image_pair] at this

theorem two_le_pRank_centralizer_of_stdDiag_model {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)}
    (hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ H → c ^ 4 = 1)
    {ζ : CubeRoot K} (hD : D₀ ζ ≤ H) {A₀ : Subgroup H}
    (h₀ : IsSumZeroCoords A₀ (stdDiagHomH ζ hD)) (hU : UniqueElemSylow 3 3 (StatedProj H))
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (htor : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      (stdDiagHomH ζ hD '' (Set.univ : Set (Multiplicative (Fin 4 → ZMod 3))))))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (A : Set Y)) := by
  obtain ⟨c, hc⟩ := exists_isSumZeroCoords_of_stdDiag_model hscal hD h₀ hU Z hZ e hA h27
  have h := IsSumZeroCoords.le_pRank_centralizer_of_stdDiagHomH hscal hD h₀ hU Z hZ e hc Set.univ
    hp hp2 htor
  have hAc : (A : Set Y) = c '' Set.univ := by
    rw [Set.image_univ, ← MonoidHom.coe_range, hc.1]
  rw [hAc]
  exact h

private theorem nonempty_cubeRoot_of_card_eq_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) : Nonempty (CubeRoot K) := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h1
  have hd : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by zify [h1, h2]; ring⟩
  exact CubeRoot.exists_of_dvd (by rw [hK]; exact h3.trans hd)

theorem forall_le_pRank_centralizer_of_equiv_statedSL {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hK : Nat.card K = r ^ f) (hmod : r ^ f % 3 = 1)
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj (StatedSL 4 K))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer (X : Set Y))) ∧
    ∀ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer
        ({c (Multiplicative.ofAdd ![1, 1, -1, -1]), c (Multiplicative.ofAdd ![1, -1, 0, 0])} :
          Set Y)) := by
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; omega
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd h3
  have hD := d₀_le_sl ζ
  exact forall_le_pRank_centralizer_of_stdDiag_model (fun c hc =>
      scalar_pow_four_eq_one_of_mem_statedSL hc) hD
    (isSumZeroCoords_statedSL ζ) (uniqueElemSylow_statedProj_statedSL_four h3) Z hZ e hr hr2
    (fun S hS => hS.elim
      (fun h => le_pRank_centralizer_stdDiagHomH_sl hr hK ζ hD S (i := 2) (j := 3) (by decide) h)
      (fun h => le_pRank_centralizer_stdDiagHomH_sl hr hK ζ hD S (i := 0) (j := 1) (by decide) h))
    hA h27

theorem forall_le_pRank_centralizer_of_equiv_statedSU {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (r ^ f) ^ 2) (hmod : r ^ f % 3 = 2)
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj (StatedSU 4 (r ^ f) K))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer (X : Set Y))) ∧
    ∀ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c →
      f ≤ CFSG.Open.pRank r (Subgroup.centralizer
        ({c (Multiplicative.ofAdd ![1, 1, -1, -1]), c (Multiplicative.ofAdd ![1, -1, 0, 0])} :
          Set Y)) := by
  have h3 : 3 ∣ r ^ f + 1 := by omega
  obtain ⟨ζ⟩ := nonempty_cubeRoot_of_card_eq_sq hK h3
  have hD := d₀_le_statedSU h3 ζ
  have hU' : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K :=
    ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  exact forall_le_pRank_centralizer_of_stdDiag_model
    (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (r ^ f) K hc)) hD
    (isSumZeroCoords_statedSU (neg_one_pow_eq_neg_one_of_card_eq_sq hK) h3 ζ)
    (uniqueElemSylow_statedProj_statedSU_four hK h3) Z hZ e hr hr2
    (fun S hS => hS.elim
      (fun h => le_pRank_centralizer_stdDiagHomH_su hU' hr2 ζ hD S (i := 2) (j := 3)
        (Or.inr ⟨rfl, rfl⟩) h)
      (fun h => le_pRank_centralizer_stdDiagHomH_su hU' hr2 ζ hD S (i := 0) (j := 1)
        (Or.inl ⟨rfl, rfl⟩) h))
    hA h27

theorem two_le_pRank_centralizer_of_equiv_statedSL {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {q p : ℕ} (hK : Nat.card K = q) (hmod : q % 3 = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q - 1)
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj (StatedSL 4 K))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (A : Set Y)) := by
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; omega
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd h3
  have hD := d₀_le_sl ζ
  exact two_le_pRank_centralizer_of_stdDiag_model (fun c hc =>
      scalar_pow_four_eq_one_of_mem_statedSL hc) hD
    (isSumZeroCoords_statedSL ζ) (uniqueElemSylow_statedProj_statedSL_four h3) Z hZ e hp hp2
    (two_le_pRank_centralizer_stdDiagHomH_univ_sl hp (by rw [hK]; exact hpq) ζ hD) hA h27

theorem two_le_pRank_centralizer_of_equiv_statedSU {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] {q p : ℕ} (hK : Nat.card K = q ^ 2) (hmod : q % 3 = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1)
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj (StatedSU 4 q K))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (A : Set Y)) := by
  have h3 : 3 ∣ q + 1 := by omega
  obtain ⟨ζ⟩ := nonempty_cubeRoot_of_card_eq_sq hK h3
  have hD := d₀_le_statedSU h3 ζ
  exact two_le_pRank_centralizer_of_stdDiag_model
    (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 q K hc)) hD
    (isSumZeroCoords_statedSU (neg_one_pow_eq_neg_one_of_card_eq_sq hK) h3 ζ)
    (uniqueElemSylow_statedProj_statedSU_four hK h3) Z hZ e hp hp2
    (two_le_pRank_centralizer_stdDiagHomH_univ_su (by omega) hK hp hpq ζ hD) hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
