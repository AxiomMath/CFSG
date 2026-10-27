module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Step
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsG24Good

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

section F4


theorem rankTwoParG_model_f4 {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RankTwoParG ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      (fun j => (F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  obtain ⟨-, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ := largeRee_named_covers a K hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : Nat.card K + 1 ≠ Nat.card K ^ 2 + 1 := by
    intro h
    have h1 : Nat.card K = Nat.card K ^ 2 := Nat.add_right_cancel h
    nlinarith
  have hinv := D4.invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  have hQP : ∀ j : Fin 2, F4.reeLocalParabolic K a (f4Index j) = F4.reeParabolic K a {f4Index j} :=
    fun j => (reeParabolic_singleton (t := F4) (K := K) (a := a) (f4Index j)).symm
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hP₁Γ : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hQ₀Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤ F4.reeGamma K a :=
    inf_le_right
  have hQ₁Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤ F4.reeGamma K a :=
    inf_le_right
  obtain ⟨hF₀, hF₁⟩ := largeReeParabolicFacts a K ha hK
  have hG₀ : GoodLocal
      ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
    refine ParabolicFacts.goodLocal (Q := (F4.reeFixedOrbitComplementUnipotent K a
      ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) ?_
    refine ParabolicFacts.of_map (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀Γ, Subgroup.map_subgroupOf_eq_of_le hQ₀Γ]
    exact hF₀
  have hG₁ : GoodLocal
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
    refine ParabolicFacts.goodLocal (Q := (F4.reeFixedOrbitComplementUnipotent K a
      ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) ?_
    refine ParabolicFacts.of_map (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁Γ, Subgroup.map_subgroupOf_eq_of_le hQ₁Γ]
    exact hF₁
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine ⟨large_Ree_residualOvergroupsAt hK, ?_, ?_, ?_⟩
  · intro j
    rcases hcases (f4Index j) with hj | hj
    ·
      left
      have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
      obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
        (isSimpleGroup_rankOneGroupOne ha hK).2
      let e : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
        (rankOneEquivSL K a hK).symm
      refine ⟨K, inferInstance, inferInstance, hchar, 2 * a + 1, hK, by omega,
        e.toMonoidHom.comp g, e.surjective.comp hg, ?_⟩
      have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        exact MulEquiv.map_eq_one_iff e
      rw [hkerEq]
      exact hk
    ·
      right
      have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
      obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
        (isSimpleGroup_rankOneGroupTwo ha hK).2
      let e : ↥(rankOneGroupTwo K a) ≃* CFSG.Blueprint.suzukiGroup a K :=
        rankOneEquivSuzuki K a ha hK
      refine ⟨2 * a + 1, a, K, inferInstance, inferInstance, ha, rfl, hK, e.toMonoidHom.comp g,
        e.surjective.comp hg, ?_⟩
      have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        exact MulEquiv.map_eq_one_iff e
      rw [hkerEq]
      exact hk
  · intro α hα j
    rw [← hQP j]
    rcases hcases (f4Index j) with h | h <;> rw [h]
    · exact (hinv α hα).1
    · exact (hinv α hα).2
  · intro j
    rw [← hQP j]
    rcases hcases (f4Index j) with h | h <;> rw [h]
    · exact hG₀
    · exact hG₁

theorem rankTwoParG_f4 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hY : Is2F4 f Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, RankTwoParG Y U P := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hY
  subst hfa
  have hU₀ := (largeRee_named_covers a K hK).1
  exact RankTwoParG.exists_of_equiv e (rankTwoParG_model_f4 ha hK) hU₀ hU

end F4

end CFSG.Quasithin.CLG2
