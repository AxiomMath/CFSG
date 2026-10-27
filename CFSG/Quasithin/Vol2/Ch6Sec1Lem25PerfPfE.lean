module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfPfC
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfPfD
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4

public section

namespace CFSG.Quasithin.H13

namespace LiePerf

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

theorem hasBenderLevi_f4
    {S : Type} [Group S] [Finite S] {k : ℕ} (hS : Is2F4 k S) : HasBenderLevi S := by
  intro U hU
  obtain ⟨a, K, _, _, _, φ, ha, hka, hK, hφ, hres, -⟩ := even_rank_two_residual_largeRee hS hU
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hka]
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := by
    have h1 := hU.2.1.map φ.toMonoidHom
    rw [hφ] at h1
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hUC)
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK'
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨_, hres, fun j => benderLevi_map_equiv φ.symm ?_⟩
  rcases hcases (f4Index j) with hj | hj
  ·
    have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK').1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq) (isSimpleGroup_rankOneGroupOne ha hK').2
    let e : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (rankOneEquivSL K a hK').symm
    have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hK']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := sl2_isSimple hK4
    have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e
    refine Or.inr ⟨_, inferInstance, inferInstance, e.toMonoidHom.comp g, e.surjective.comp hg,
      ?_, 2 * a + 1, isBenderOf_sl2 hK' (by omega)⟩
    rw [hkerEq]
    have := hk.isNilpotent
    infer_instance
  ·
    have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK').1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq) (isSimpleGroup_rankOneGroupTwo ha hK').2
    refine Or.inr ⟨_, inferInstance, inferInstance, g, hg, ?_, 2 * a + 1, by omega,
      Or.inr (Or.inl ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK',
        ⟨rankOneEquivSuzuki K a ha hK'⟩⟩)⟩
    have := hk.isNilpotent
    infer_instance

end LiePerf

open LiePerf

theorem liePerfOvergroupFactRank2_holds :
    LiePerfOvergroupFactRank2 :=
  liePerfOvergroupFactRank2_of fun S _ _ ⟨k, hk, h⟩ => by
    rcases h with h | h | h | h | h
    · exact hasBenderLevi_l3 hk h
    · exact hasBenderLevi_sp4 hk h
    · exact hasBenderLevi_g2 hk h
    · exact hasBenderLevi_d4 (by omega) h
    · exact hasBenderLevi_f4 h

end CFSG.Quasithin.H13
