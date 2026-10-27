module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement

theorem commutator_le_of_card_lt_three_mul {Γ : Type*} [Group Γ] {O H : Subgroup Γ} [Finite O]
    (hHO : H ≤ O) (h3 : Nat.card O < 3 * Nat.card H) : ⁅O, O⁆ ≤ H := by
  set H' : Subgroup O := H.subgroupOf O with hH'
  have hcard : Nat.card H' = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHO).toEquiv
  have hmul : Nat.card H' * H'.index = Nat.card O := H'.card_mul_index
  have hidx0 : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : H'.index = 1 ∨ H'.index = 2 := by
    by_contra hne
    have h3le : 3 ≤ H'.index := by omega
    have := Nat.mul_le_mul_left (Nat.card H') h3le
    rw [hmul, hcard] at this
    omega
  have hle : commutator O ≤ H' := by
    rcases hidx with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact le_top
    · have := Subgroup.normal_of_index_eq_two h2
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (O ⧸ H') := isCyclic_of_prime_card h2
      infer_instance
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅(⟨a, ha⟩ : O), (⟨b, hb⟩ : O)⁆ ∈ H' :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact Subgroup.mem_subgroupOf.mp hab

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qw : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
private theorem polar_isometryEquiv {W : Type} [AddCommGroup W] [Module K W]
    {R : QuadraticForm K W} (ι : R.IsometryEquiv Qw) (x y : W) :
    polar Qw (ι x) (ι y) = polar R x y := by
  rw [polar, polar, ← map_add, ι.map_app, ι.map_app, ι.map_app]

private def hypPairMap {W : Type} [AddCommGroup W] [Module K W] {R : QuadraticForm K W}
    (ι : R.IsometryEquiv Qw) (P : HypPair R) : HypPair Qw where
  e := ι P.e
  f := ι P.f
  Q_e := by rw [ι.map_app]; exact P.Q_e
  Q_f := by rw [ι.map_app]; exact P.Q_f
  polar_ef := by rw [polar_isometryEquiv]; exact P.polar_ef

omit [Finite K] [FiniteDimensional K V] in
private theorem hypPairMap_orth {W : Type} [AddCommGroup W] [Module K W]
    {R : QuadraticForm K W} (ι : R.IsometryEquiv Qw) {P P' : HypPair R} (h : P.Orth P') :
    (hypPairMap ι P).Orth (hypPairMap ι P') :=
  ⟨(polar_isometryEquiv ι _ _).trans h.ee, (polar_isometryEquiv ι _ _).trans h.ef,
    (polar_isometryEquiv ι _ _).trans h.fe, (polar_isometryEquiv ι _ _).trans h.ff⟩

theorem exists_orth_hypPairs_of_finrank (hQ : (polarBilin Qw).Nondegenerate) {m : ℕ}
    (hm : 3 ≤ m) (hdim : finrank K V = 2 * m) : ∃ P₁ P₂ : HypPair Qw, P₁.Orth P₂ := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Qw hQ (n := m)
    (by omega) hdim with ⟨⟨e⟩⟩ | ⟨b, c, -, ⟨e⟩⟩
  · exact ⟨hypPairMap e.symm (plusPair K (⟨0, by omega⟩ : Fin m)),
      hypPairMap e.symm (plusPair K (⟨1, by omega⟩ : Fin m)),
      hypPairMap_orth e.symm (plusPair_orth (by simp [Fin.ext_iff]))⟩
  · exact ⟨hypPairMap e.symm (minusPair K b c (⟨0, by omega⟩ : Fin (m - 1))),
      hypPairMap e.symm (minusPair K b c (⟨1, by omega⟩ : Fin (m - 1))),
      hypPairMap_orth e.symm (minusPair_orth (by simp [Fin.ext_iff]))⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem elementaryGroup_le_commutator_of_isometry {W : Type} [AddCommGroup W]
    [Module K W] {R : QuadraticForm K W} (e : R.IsometryEquiv Qw)
    (hR : elementaryGroup R ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆) :
    elementaryGroup Qw ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Qw,
      TauCeti.QuadraticMap.orthogonalGroup Qw⁆ := by
  rw [← CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map e,
    ← CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.orthogonalGroup_map_isometry e,
    ← Subgroup.map_commutator]
  exact Subgroup.map_mono hR

theorem elementaryGroup_le_commutator_of_finrank (hQ : (polarBilin Qw).Nondegenerate) {m : ℕ}
    (hm : 3 ≤ m) (hdim : finrank K V = 2 * m) :
    elementaryGroup Qw ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Qw,
      TauCeti.QuadraticMap.orthogonalGroup Qw⁆ := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Qw hQ (n := m)
    (by omega) hdim with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
  · exact elementaryGroup_le_commutator_of_isometry e.symm
      (commutator_orthogonalGroup_quadPlus hm).ge
  · exact elementaryGroup_le_commutator_of_isometry e.symm
      (elementaryGroup_quadMinus_le_commutator (by omega) hirr)

private theorem orderFactor_pos {q : ℤ} (hq : 2 ≤ q) (m : ℕ) :
    0 < q ^ (m * (m - 1)) * ∏ i ∈ Finset.Icc 1 (m - 1), (q ^ (2 * i) - 1) := by
  refine mul_pos (pow_pos (by omega) _) (Finset.prod_pos fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have : q ^ 1 ≤ q ^ (2 * i) := pow_le_pow_right₀ (by omega) (by omega)
  rw [pow_one] at this
  linarith

private theorem card_orthogonalGroup_le [CharP K 2] (hQ : (polarBilin Qw).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : finrank K V = 2 * m) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qw) : ℤ) ≤
      2 * (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hq2 : (2 : ℤ) ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hA := orderFactor_pos hq2 (k + 1)
  rw [Nat.add_sub_cancel] at hA ⊢
  rw [show (k + 1) * k = k * (k + 1) by ring] at hA ⊢
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Qw hQ (n := k + 1)
    (by omega) hdim with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
  · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) k).2
    rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e] at h
    rw [h]
    nlinarith [hA]
  · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) k hirr).2
    rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e] at h
    exact h.le

theorem card_orthogonalGroup_lt_three_mul [CharP K 2] (hQ : (polarBilin Qw).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : finrank K V = 2 * m) {H : Subgroup (V ≃ₗ[K] V)}
    (hcard : (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) ≤ Nat.card H) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qw) < 3 * Nat.card H := by
  have hq2 : (2 : ℤ) ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hN : (8 : ℤ) ≤ (Nat.card K : ℤ) ^ m :=
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (Nat.card K : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) hq2 3
      _ ≤ (Nat.card K : ℤ) ^ m := pow_le_pow_right₀ (by omega) hm
  have hA := orderFactor_pos hq2 m
  have hO := card_orthogonalGroup_le hQ hm hdim
  set A : ℤ := (Nat.card K : ℤ) ^ (m * (m - 1)) *
    ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) with hAdef
  set N : ℤ := (Nat.card K : ℤ) ^ m with hNdef
  have hO' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qw) : ℤ) ≤ 2 * A * (N + 1) := by
    rw [hAdef]
    linarith [hO]
  have hcard' : A * (N - 1) ≤ Nat.card H := by
    rw [hAdef]
    linarith [hcard]
  have key : 2 * A * (N + 1) < 3 * (A * (N - 1)) := by
    nlinarith [mul_pos hA (show (0 : ℤ) < N - 5 by linarith)]
  have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qw) : ℤ) < 3 * Nat.card H := by
    linarith
  exact_mod_cast this

theorem elementaryGroup_le_of_card_ge [CharP K 2] (hQ : (polarBilin Qw).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : finrank K V = 2 * m) {H : Subgroup (V ≃ₗ[K] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Qw)
    (hcard : (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) ≤ Nat.card H) :
    elementaryGroup Qw ≤ H := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) fun f g hfg =>
      LinearEquiv.ext fun x => congrFun hfg x
  exact (elementaryGroup_le_commutator_of_finrank hQ hm hdim).trans
    (commutator_le_of_card_lt_three_mul hHO (card_orthogonalGroup_lt_three_mul hQ hm hdim hcard))

end CFSG.RankThree.GF2n.Stroth80
