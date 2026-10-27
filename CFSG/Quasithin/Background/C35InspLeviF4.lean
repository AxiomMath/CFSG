module

public import CFSG.Quasithin.Background.C35InspLeviRes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C35Pf
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie

theorem levi_f4
    {A : Type} [Group A] [Finite A] {K Y : Subgroup A}
    (hZ : IsPGroup 2 ↥(centerOf K)) {f : ℕ} (hX : Is2F4 f (↥K ⧸ Subgroup.center ↥K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  obtain ⟨a, F, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag F) := finite_modGL
  have hchar : CharP F 2 := inferInstanceAs (CharP F F4.prime)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a F w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent F a ≤ F4.reeGamma F a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent F a) (F4.reeGamma F a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent F a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a F ha hK
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  let φ : ↥K →* ↥(F4.reeGamma F a) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  refine leviConcl_of_residual hZ hpar hne hX0 φ hφker.le hφs hU₀
    (large_Ree_residualOvergroupsAt hK) fun j _ => ?_
  have hF : ∃ Q, ParabolicFacts (F4.reeParabolic F a {f4Index j}) Q := by
    rw [reeParabolic_singleton (t := F4) (K := F) (a := a)]
    rcases hcases (f4Index j) with h | h <;> rw [h]
    · exact ⟨_, hF0⟩
    · exact ⟨_, hF1⟩
  obtain ⟨Q, hF⟩ := hF
  rcases hcases (f4Index j) with hj | hj
  ·
    have := (isSimpleGroup_rankOneGroupOne ha hK).1
    have hT := (isSimpleGroup_rankOneGroupOne ha hK).2
    obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := F) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne F a) (by rw [hj]; exact h0eq) hT
    refine ⟨_, inferInstance, inferInstance, inferInstance, g, hT, hg, hk,
      exists_noncomm_of_parabolicFacts (reeParabolic_le F4 F a _) hF hT g hg, ?_⟩
    exact (smallLevi_sl2 hK (by omega)).of_mulEquiv
      (rankOneEquivSL F a hK)
  ·
    have := (isSimpleGroup_rankOneGroupTwo ha hK).1
    have hT := (isSimpleGroup_rankOneGroupTwo ha hK).2
    obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := F) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo F a) (by rw [hj]; exact h1eq) hT
    refine ⟨_, inferInstance, inferInstance, inferInstance, g, hT, hg, hk,
      exists_noncomm_of_parabolicFacts (reeParabolic_le F4 F a _) hF hT g hg, ?_⟩
    exact Or.inr (Or.inl ⟨2 * a + 1, ⟨a, rfl⟩, by omega, rfl, a, ha, F, inferInstance,
      inferInstance, rfl, hK, ⟨rankOneEquivSuzuki F a ha hK⟩⟩)

end CFSG.Quasithin.C35Levi
