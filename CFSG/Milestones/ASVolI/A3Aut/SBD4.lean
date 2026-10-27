module

public import CFSG.Milestones.ASVolI.A3Aut.SBBase

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6

section Fixed

variable {t : TwistTag} {K : Type} [Field K]

theorem burnsideAut_solvBorel_graphFixed
    [Finite K] (σ : K ≃+* K)
    (hL : ∀ a, 4 ≤ Nat.card (orbitField t K σ.toRingHom a)) :
    burnsideAut_SolvBorel ↥(graphFixedRootGroup t K σ.toRingHom)
      ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom)) := by
  intro Y hUY hYs
  set Y' : Subgroup (ModGL t.tag K) := Y.map (graphFixedRootGroup t K σ.toRingHom).subtype
    with hY'
  have hY'C : Y' ≤ graphFixedRootGroup t K σ.toRingHom := Subgroup.map_subtype_le Y
  have hUY' : graphFixedPosUnipotent t K σ.toRingHom ≤ Y' := fun u hu =>
    ⟨⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom hu⟩,
      hUY (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  have hY's : Group.IsSolvable ↥Y' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Y _ Subtype.val_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  have hJ : ∀ a, a ∉ {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ Y'} := by
    intro a ha
    have hx : ∀ c, (orbitX t K σ.toRingHom a c : ModGL t.tag K) ∈ Y' := fun c =>
      hUY' (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a c)
    have hy : ∀ c, (orbitY t K σ.toRingHom a c : ModGL t.tag K) ∈ Y' := fun c => by
      rw [← canonicalRep_orbitReflection_conj_orbitX t σ.toRingHom a c]
      exact mul_mem (mul_mem ha (hx _)) (inv_mem ha)
    have hR : (orbitRankOneHom t K σ.toRingHom a).range ≤ Y' := by
      rw [orbitRankOneHom_range a, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hx c
      · exact hy c
    have hR1 : orbitRankOneHom t K σ.toRingHom a (uSL 1) ≠ 1 := by
      rw [orbitRankOneHom_uSL a]
      intro h
      have h2 : orbitX t K σ.toRingHom a 1 = orbitX t K σ.toRingHom a 0 := by
        apply Subtype.ext
        rw [orbitX_zero]
        exact h
      exact one_ne_zero (orbitX_injective σ.toRingHom a h2)
    haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
      (orbitField t K σ.toRingHom a) (hL a)
    exact burnsideAut_not_isSolvable_of_perfect_hom _ hR1 hR hY's
  have hY'B : Y' ≤ graphFixedRootBorel t K σ.toRingHom := by
    have h := le_graphFixedParabolic_of_posUnipotent_le σ.surjective hY'C hUY'
    rwa [Set.eq_empty_of_forall_notMem hJ, graphFixedParabolic, Set.image_empty,
      Subgroup.closure_empty, sup_bot_eq] at h
  have hBN : graphFixedRootBorel t K σ.toRingHom ≤
      Subgroup.normalizer (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(sup_le torusGroup_le_normalizer_posUnipotent Subgroup.le_normalizer : borelGroup t.tag K ≤ _)
        hx.1.1, Subgroup.le_normalizer hx.1.2⟩
  intro y hy
  rw [← Subgroup.subgroupOf_normalizer_eq
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)]
  exact Subgroup.mem_subgroupOf.2 (hBN (hY'B ⟨y, hy, rfl⟩))

theorem burnsideAut_isSylowTwoOf_graphFixedPosUnipotent
    [Finite K] [CharP K 2] (σ : K ≃+* K) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition t K 2 σ w₀ hw₀).1
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

end Fixed

theorem burnsideAut_solvBorel_3D4 :
    ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f → CFSG.Quasithin.Is3D4 2 f X →
      ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → burnsideAut_SolvBorel X S := by
  intro X _ _ f hf hX S hS
  obtain ⟨hf1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨σ', hσ', -, hcard, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1 K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ'
  have hL : ∀ a, 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) := by
    intro a
    rw [hcard a]
    have h1 : 1 ≤ (TwistTag.D4.orbit a).card :=
      Finset.card_pos.2 ⟨_, TwistTag.D4.orbitMin_mem a⟩
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ (TwistTag.D4.orbit a).card :=
        Nat.pow_le_pow_right (by positivity) h1
  exact burnsideAut_solvBorel_of_isSylow e (burnsideAut_isSylowTwoOf_graphFixedPosUnipotent σ)
    (burnsideAut_solvBorel_graphFixed σ hL) hS

end CFSG.ASVolI
