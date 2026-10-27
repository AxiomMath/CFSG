module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace IOneRest

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggIRankLe_omegaPlus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hm : 3 ≤ m) :
    GGIRankLe p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn
    (TableBOrth.center_omegaPlus_eq_bot hp hp2 hpq hm) hXI hX
  exact hAc ▸ OrthRest.card_le_plus (by omega) hp hp2 A hA

theorem card_le_omegaMinus_split {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {A : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ m := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo, -⟩ := TableBOrth.exists_zeta (K := K) hp hp2 hpq
  set e := TableBOrth.projMkEquiv
    (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c) with he
  set A' : Subgroup (GL (LargeEvenMinusIdx m) K) :=
    (A.map e.symm.toMonoidHom).map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype with hA'def
  have hA' : IsElemAbelian p A' := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective e.symm.injective]
  rw [← hcard]
  by_contra hlt
  have hle : p ^ m ≤ Nat.card A' := (not_le.mp hlt).le
  have hAO : A' ≤ LargeEvenOrthGroup (LargeEvenQMinus m b c) :=
    (Subgroup.map_subtype_le _).trans (TableBOrth.omega_le_orth _)
  obtain ⟨g, -, χ, hχ, -⟩ := TableBOrth.exists_orth_conj_minus hp2 hζo hirr hAO hA' hle
  have hexp : ∀ x : A', x ^ p = 1 := fun x => Subtype.ext (hA'.2 x x.2)
  set φ : A' → (Fin m → rootsOfUnity p K) := fun x k =>
    ⟨χ k x, (mem_rootsOfUnity p _).mpr (by rw [← map_pow, hexp, map_one])⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro x x' h
    have h1 : (fun k => χ k x) = fun k => χ k x' := funext fun k =>
      congrArg Subtype.val (congrFun h k)
    have h2 := hχ x
    rw [h1, ← hχ x'] at h2
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  have h3 : Nat.card A' ≤ p ^ m :=
    calc Nat.card A' ≤ Nat.card (Fin m → rootsOfUnity p K) :=
          Nat.card_le_card_of_injective φ hφinj
      _ = Nat.card (rootsOfUnity p K) ^ m := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
      _ ≤ p ^ m := Nat.pow_le_pow_left (card_rootsOfUnity K p) _
  exact hlt h3

theorem ggIRankLe_omegaMinus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGIRankLe p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn
    (TableBOrth.center_omegaMinus_eq_bot hp hp2 hpq hm hirr) hXI hX
  exact hAc ▸ card_le_omegaMinus_split hp hp2 hpq hirr hA

theorem recipeOmegaPlus_iRank {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 4 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
    ggIRankLe_omegaPlus hp hp2 hpq (by omega)⟩

theorem recipeOmegaMinus_iRank {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq hm b c, ggIRankLe_omegaMinus hp hp2 hpq hm hbc⟩

theorem largeEvenLabelAll_iRank_orthSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoOrthSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  have hp2 := ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_iRank hp hp2 hpn hl hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_iRank hp hp2 hpn (by omega) hQ

end IOneRest

open IOneRest

theorem ggStdSubIOneProperInputOn_orthSplit (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGCorFourTwoOrthSplitLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_and_iOne (largeEvenLabelAll_innerDiag_orthSplit hp hlab h)
      (largeEvenLabelAll_iRank_orthSplit hp hlab h)

end CFSG.StandardType
