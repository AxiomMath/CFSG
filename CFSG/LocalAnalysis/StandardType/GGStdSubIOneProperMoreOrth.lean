module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRankMinus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Matrix

namespace IOneMore

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_nonzero_singular_qPlus (k : ℕ) :
    (Nat.card {v : Fin (k + 1) ⊕ Fin (k + 1) → K //
        v ≠ 0 ∧ TableBOrth.qPlusForm K (k + 1) v = 0} : ℤ) =
      ((Nat.card K : ℤ) ^ (k + 1) - 1) * ((Nat.card K : ℤ) ^ k + 1) := by
  have h1 := OrthRestEnd.card_singular_eq_succ (TableBOrth.qPlusForm K (k + 1))
  have h3 := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) k).1
  change (Nat.card {v // TableBOrth.qPlusForm K (k + 1) v = 0} : ℤ) = _ at h3
  rw [h1] at h3
  push_cast at h3
  linarith

theorem not_dvd_card_nonzero_singular_qPlus {k p : ℕ} (hke : Even k) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card
      {v : Fin (k + 1) ⊕ Fin (k + 1) → K // v ≠ 0 ∧ TableBOrth.qPlusForm K (k + 1) v = 0} := by
  intro hdvd
  have h := card_nonzero_singular_qPlus (K := K) k
  have hq : (Nat.card K : ZMod p) = -1 := by
    have h1 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    push_cast at h1
    exact eq_neg_of_add_eq_zero_left h1
  have h0 : ((Nat.card {v : Fin (k + 1) ⊕ Fin (k + 1) → K //
      v ≠ 0 ∧ TableBOrth.qPlusForm K (k + 1) v = 0} : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [h] at h0
  push_cast at h0
  rw [hq, hke.neg_one_pow, (hke.add_one).neg_one_pow] at h0
  have h4 : ((4 : ℕ) : ZMod p) = 0 := by
    have e : ((4 : ℕ) : ZMod p) = -((-1 - 1) * (1 + 1)) := by push_cast; ring
    rw [e, h0, neg_zero]
  have h4' : p ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4'))

theorem card_le_plus_odd {m p : ℕ} (hmo : Odd m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (OrthRest.RPlus K m)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (m - 1) := by
  obtain ⟨j, rfl⟩ := hmo
  have : Fact p.Prime := ⟨hp⟩
  have hsc := TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) (m := 2 * j + 1) (by omega)
  set f : OrthRest.RPlus K (2 * j + 1) →* GL (Fin (2 * j + 1) ⊕ Fin (2 * j + 1)) K :=
    (LargeEvenOmega (LargeEvenQPlus K (2 * j + 1))).subtype.comp
      (TableBOrth.projMkEquiv hsc).symm.toMonoidHom with hf
  have hfi : Function.Injective f :=
    (LargeEvenOmega _).subtype_injective.comp (TableBOrth.projMkEquiv hsc).symm.injective
  have hiso : ∀ g ∈ E.map f, ∀ v, TableBOrth.qPlusForm K (2 * j + 1)
      ((g : Matrix _ _ K) *ᵥ v) = TableBOrth.qPlusForm K (2 * j + 1) v := by
    rintro _ ⟨r, -, rfl⟩ v
    rw [TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup
      (TableBOrth.omega_le_orth _ ((TableBOrth.projMkEquiv hsc).symm r).2) v
  have hcomm : ∀ g ∈ E.map f, ∀ h ∈ E.map f, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha ha']
  have hexp : ∀ g ∈ E.map f, g ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hpg : IsPGroup p (E.map f) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hexp g g.2)⟩
  obtain ⟨v, hv0, -, hvfix⟩ := OrthRestEnd.exists_fixed_singular
    (TableBOrth.qPlusForm K (2 * j + 1)) (E.map f) hpg hiso
    (not_dvd_card_nonzero_singular_qPlus (k := 2 * j) (even_two_mul j) hp hp2 hpq)
  have h := OrthRestEnd.card_le_of_isometry_fixed (TableBOrth.qPlusForm K (2 * j + 1))
    (TableBOrth.nondegenerate_qPlusForm (2 * j + 1)) hp hp2 (E.map f) hiso hcomm hexp hv0 hvfix
  have hc : Fintype.card (Fin (2 * j + 1) ⊕ Fin (2 * j + 1)) / 2 - 1 = 2 * j + 1 - 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rwa [hc, Subgroup.card_map_of_injective hfi] at h

end Plus

end IOneMore

section Certs


theorem recipeOmegaMinus_iRank_nonsplit {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hm : 3 ≤ m) (hmo : Odd m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hlift := ggOrthRestTorusLiftInput_holds.1 K n m p b c hK hm hp hpn hbc
  have hZ := (ggOrthRestCenterInput_holds.1 K n m p b c hK hm hp hpn hbc).1
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m, hlift,
    ggIRankLe_of_card_le fun X hXI hX => ?_⟩
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hZ hXI hX
  exact hAc ▸ ggOrthRestMinusRankInput_holds K n m p b c hK hm hmo hp hpn hbc A hA

theorem recipeOmegaMinus_bstarEq {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1)
    (hpn' : ¬ p ∣ n) (hm : 3 ≤ m) (hmo : Odd m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ, hr⟩ :=
    recipeOmegaMinus_iRank_nonsplit hp hp2 hpn hm hmo h
  have := charP_two_of_card hK
  have hlift := ggOrthRestTorusLiftInput_holds.1 K n m p b c hK hm hp hpn hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, ⟨m, hlift,
    ggInnerDiagBound_of_forall_mem fun φ hφ =>
      OrthRest.mem_range_conj_minus hm hbc hK hp hp2 hpn' hφ⟩, hr⟩

theorem recipeOmegaPlus_bstarEq_two {m : ℕ} (hm : 5 ≤ m) (hmo : Odd m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m (2 ^ 1) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ 1) fun R _ I F => Q R I F ∧
      (∃ r, GGTorusLift 3 r R ∧ GGInnerDiagBound 3 r R I) ∧
        ∃ r, GGTorusLift 3 r R ∧ GGIRankLe 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hlift := ggOrthRestTorusLiftInput_holds.2 K m hK2 (by omega)
  have hZ := (ggOrthRestCenterInput_holds.2 K m hK2 (by omega)).1
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ⟨m - 1, hlift,
    ggInnerDiagBound_of_forall_mem fun φ hφ => OrthRest.mem_range_conj_plus_two hm hK2 hφ⟩,
    m - 1, hlift, ggIRankLe_of_card_le fun X hXI hX => ?_⟩
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hZ hXI hX
  exact hAc ▸ IOneMore.card_le_plus_odd hmo Nat.prime_three (by norm_num) (by rw [hK2]) A hA

@[expose] def GGIOneMoreOrthEqLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.n) ∨
    (lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ lab.n = 1 ∧ p = 3)

theorem largeEvenLabelAll_bstarEq_orthEq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : GGIOneMoreOrthEqLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with ⟨ht, hl, hle, hpn, hpn'⟩ | ⟨ht, hl, hlo, hn, rfl⟩
  · dsimp only at ht hl hle hpn hpn'
    subst ht
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · have hmo : Odd (l - 1) := by
        obtain ⟨k, hk⟩ := hle
        exact ⟨k - 1, by omega⟩
      exact recipeOmegaMinus_bstarEq hp hp2 hpn hpn' (by omega) hmo hQ
  · dsimp only at ht hl hlo hn
    subst ht hn
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_bstarEq_two hl hlo hQ

theorem largeEvenLabelAll_iRank_orthMinus_even_nonsplit {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hle, hpn⟩ := h
  dsimp only at ht hl hle hpn ⊢
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2' : 2 ∣ 2 ^ n + 1 := hpn
    have h3 : 2 ∣ 1 := (Nat.dvd_add_right h2).mp h2'
    norm_num at h3
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · have hmo : Odd (l - 1) := by
      obtain ⟨k, hk⟩ := hle
      exact ⟨k - 1, by omega⟩
    exact recipeOmegaMinus_iRank_nonsplit hp hp2 hpn (by omega) hmo hQ

theorem ggStdSubIOneProperInputOn_orthEq (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreOrthEqLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun p lab hp hlab h _ => by
    have hp2 : p ≠ 2 := by
      rintro rfl
      rcases h with ⟨-, -, -, hpn, -⟩ | ⟨-, -, -, -, h3⟩
      · have h1 : 2 ∣ 2 ^ lab.n := dvd_pow_self 2 (by have := hlab.1; omega)
        have h2 := (Nat.dvd_add_right h1).mp hpn
        norm_num at h2
      · omega
    exact largeEvenLabelAll_bstarEq_orthEq hp hp2 h

end Certs

end CFSG.StandardType
