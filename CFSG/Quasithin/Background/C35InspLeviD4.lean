module

public import CFSG.Quasithin.Background.C35InspLeviRes
public import CFSG.Quasithin.Background.C35InspD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C35Pf
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie

theorem levi_d4
    {A : Type} [Group A] [Finite A] {K Y : Subgroup A}
    (hZ : IsPGroup 2 ↥(centerOf K)) {f : ℕ} (hX : Is3D4 2 f (↥K ⧸ Subgroup.center ↥K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  obtain ⟨hf, F, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card F = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 F 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 F σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite F
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  have hK4 : 4 ≤ Nat.card F := by
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let φ : ↥K →* ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom) :=
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
  have hcases : ∀ i : Fin TwistTag.D4.foldedTag.rank, i = D4.fa0 ∨ i = D4.fa1 := by decide
  refine leviConcl_of_residual hZ hpar hne hX0 φ hφker.le hφs hU₀
    (triality_residualOvergroupsAt σ) fun j hj => ?_
  rcases Vol2Native.A312L.fixed_leviData σ (d4Index j) hUsyl.2.1 with h0 | h
  · exact absurd h0 hj
  obtain ⟨L, _, _, _, m, hm, hm2, g, hg, hk⟩ := h
  have hL4 : ∃ s : Finset L, s.card = 4 := by
    refine Vol2Native.A312L.exists_finset_card_four ?_
    rw [hm]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have := Vol2Native.A312L.sl2_isSimple hL4
  have hT := Vol2Native.A312L.sl2_nonabelian hL4
  have hF : ∃ Q, ParabolicFacts (graphFixedParabolic TwistTag.D4 F σ.toRingHom {d4Index j}) Q := by
    rcases hcases (d4Index j) with h | h <;> rw [h]
    · exact ⟨_, D4.parabolicFacts_a0 σ hσ3 hK4⟩
    · exact ⟨_, D4.parabolicFacts_a1 σ hσ3⟩
  obtain ⟨Q, hF⟩ := hF
  exact ⟨_, inferInstance, inferInstance, inferInstance, g, hT, hg, hk,
    exists_noncomm_of_parabolicFacts (graphFixedParabolic_le _ _ _ _) hF hT g hg,
    smallLevi_sl2 hm hm2⟩

end CFSG.Quasithin.C35Levi
