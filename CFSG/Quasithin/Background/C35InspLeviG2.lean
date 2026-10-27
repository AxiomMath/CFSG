module

public import CFSG.Quasithin.Background.C35InspLeviRes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C35Pf
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie

theorem levi_g2
    {A : Type} [Group A] [Finite A] {K Y : Subgroup A}
    (hZ : IsPGroup 2 ↥(centerOf K)) {f : ℕ} (hf2 : 2 ≤ f)
    (hX : IsG2 2 f (↥K ⧸ Subgroup.center ↥K)) (hpar : IsParabolic2 K Y) (hne : Y ≠ K)
    (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  obtain ⟨-, F, _, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine Vol2Native.A312L.exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let φ : ↥K →* ↥(adjointGroup Tag.G2 F) :=
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
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1)
  refine leviConcl_of_residual hZ hpar hne hX0 φ hφker.le hφs hU₀ G2_residualOvergroupsAt
    fun j _ => ?_
  obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.exists_levi_hom_adjoint (τ := Tag.G2) hcard hf2
    (g2Index j)
  have := Vol2Native.A312L.sl2_isSimple hK4
  have hT := Vol2Native.A312L.sl2_nonabelian hK4
  have hF : ParabolicFacts (parabolicSubgroup Tag.G2 F {g2Index j})
      (parabolicRadical Tag.G2 F {g2Index j}) := by
    rcases G2.fin_two_cases (g2Index j) with h | h <;> rw [h]
    · exact G2.parabolicFacts_zero hcard hf2
    · exact G2.parabolicFacts_one hcard hf2
  exact ⟨_, inferInstance, inferInstance, inferInstance, g, hT, hg, hk,
    exists_noncomm_of_parabolicFacts (parabolicSubgroup_le_adjointGroup _ _ _) hF hT g hg,
    smallLevi_sl2 hcard hf2⟩

end CFSG.Quasithin.C35Levi
