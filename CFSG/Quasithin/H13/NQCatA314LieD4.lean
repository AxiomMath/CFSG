module

public import CFSG.Quasithin.H13.NQCatA314LieGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem lieP_perfectCore_D4
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf1 : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hσ3 : σ.toRingHom ^ 3 = 1)
    (j : Fin 2) :
    LieP (f = 2) (perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨σ', hσ', -, hcard', -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1 K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  have hcard : ∀ a, Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) =
      (2 ^ f) ^ (TwistTag.D4.orbit a).card := by
    rw [hσσ']
    exact hcard'
  have hU := isPGroup_posUnipotent σ hσ3
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  rcases foldedRank_D4_cases (d4Index j) with h | h
  ·
    have h' : d4Index j = fa0 := h
    rw [h']
    have h3 : (TwistTag.D4.orbit fa0).card = 3 := card_orbit_D4.1
    have hc0 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = (2 ^ f) ^ 3 := by
      rw [hcard, h3]
    have h8 : 8 ≤ (2 ^ f) ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq2 3
    have h4 : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) := by omega
    obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ fa0 hU (exists_finset_card_four h4)
    exact lieP_of_sl2 h4 g hg hker fun _ h => absurd h (by omega)
  ·
    have h' : d4Index j = fa1 := h
    rw [h']
    have h1 : (TwistTag.D4.orbit fa1).card = 1 := card_orbit_D4.2
    have hc1 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 ^ f := by
      rw [hcard, h1, pow_one]
    have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1} ≤
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
    by_cases hf2 : 2 ≤ f
    · have hX : LieP True (perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom
          {fa1}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
        lieP_perfectCore_subgroupOf_of hPC fun hA =>
          ⟨charTwo_of_parabolicFacts (parabolicFacts_a1 σ hσ3) hA, trivial⟩
      have h4 : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) := by
        rw [hc1]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ fa1 hU (exists_finset_card_four h4)
      exact lieP_of_sl2 h4 g hg hker fun hA h4' => ⟨(hX hA).1, eq_two_of_card_eq_four hc1 h4'⟩
    · have hf1' : f = 1 := by omega
      subst hf1'
      have h2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 := by
        rw [hc1]
        norm_num
      have hbot := perfectCore_bot_of_card_two σ fa1 hU h2
      refine lieP_perfectCore_subgroupOf_of hPC ?_
      rw [hbot]
      exact lieP_bot _

theorem lieP_d4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    LieP (f = 2) (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hL
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite K
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  refine lieP_perfectCore_of_equiv e ?_
  exact lieP_perfectCore_parabolic hU₀ (triality_residualOvergroupsAt σ)
    (fun j => lieP_perfectCore_D4 hf σ hK hσ hσ3 j) (isParabolic2_top_map_equiv e hpa)
    (CFSG.QuasithinUnique.A5.G3.map_ne_top_of_equiv e hna)

end CFSG.Quasithin.H13.NQCat.A314D
