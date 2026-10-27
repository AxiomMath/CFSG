module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LieType.BorelTits.Ree

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace Sec1211He

variable {X : Type} [Group X] [Finite X] {m : ℕ}

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = r at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h1 with h2 | h2 <;> omega
  · omega

theorem not_heInspCfg_F4
    {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f) (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_reeTitsModel hX (by decide)).holdsTits
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine not_heInspCfg_of_model e hBT (isSylowTwoOf_subgroupOf_top hUsyl)
    (noLinOver_of_residual (large_Ree_residualOvergroupsAt hK) fun j => ?_) hm
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (f4Index j) with hj | hj
  ·
    have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, -, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
      (isSimpleGroup_rankOneGroupOne ha hK).2
    let e₁ : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (rankOneEquivSL K a hK).symm
    have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
    refine leviTarget_of_sl2 (e₁.toMonoidHom.comp g) ?_
    have hkerEq : (e₁.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e₁
    rw [hkerEq]
    exact hk
  ·
    have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, -, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
      (isSimpleGroup_rankOneGroupTwo ha hK).2
    let e₂ : ↥(rankOneGroupTwo K a) ≃* ↥(CFSG.Blueprint.suzukiGroup a K) :=
      rankOneEquivSuzuki K a ha hK
    refine ⟨↥(CFSG.Blueprint.suzukiGroup a K), inferInstance, e₂.toMonoidHom.comp g, ?_,
      Or.inr ?_⟩
    · have hkerEq : (e₂.toMonoidHom.comp g).ker = g.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        exact MulEquiv.map_eq_one_iff e₂
      rw [hkerEq]
      exact hk
    · rw [suzuki_order hK]
      exact not_three_dvd_suzuki_order a

end Sec1211He

end CFSG.Quasithin.H13
