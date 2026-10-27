module

public import CFSG.Quasithin.Vol2.Ch11SecAKE5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {t : TwistTag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
  (a : Fin t.foldedTag.rank)

theorem perfectCore_eq_bot_of_card_two [CharP K 2]
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent t K σ.toRingHom))
    (hm : Nat.card ↥(orbitField t K σ.toRingHom a) = 2) :
    perfectCore ((graphFixedParabolic t K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := Vol2Native.A312L.fixed_structure σ a
  have hVU : graphFixedSimpleComplement t K σ.toRingHom a ≤
      graphFixedPosUnipotent t K σ.toRingHom := graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement t K σ.toRingHom a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement t K σ.toRingHom a) := by
    have := hV2.isNilpotent
    infer_instance
  have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField t K σ.toRingHom a)) := by
    refine Vol2Native.A312L.isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm]
    norm_num
  have hMs : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
  have hNs : Group.IsSolvable ↥(fixedPosWeylGroup t K σ.toRingHom a) :=
    Vol2Native.A312L.isSolvable_of_levi hVN hNV hsup hVs hMs
  have hpcN : perfectCore (fixedPosWeylGroup t K σ.toRingHom a) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp hNs
  have hPC : graphFixedParabolic t K σ.toRingHom {a} ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  apply Subgroup.map_injective (graphFixedRootGroup t K σ.toRingHom).subtype_injective
  rw [Vol2Native.A312L.perfectCore_map_subgroupOf hPC, Vol2Native.A312L.fixed_perfectCore_eq σ a,
    hpcN, Subgroup.map_bot]

theorem param_D4 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : Is3D4 2 f X) {P : Subgroup X}
    (hP : IsMaxParabolic2 ⊤ P) {m : ℕ} (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) :
    m = f ∨ m = 3 * f := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hP', hm'⟩ := maxParabolic_map e hP hm
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  refine param_of_residual (R := fun n => n = f ∨ n = 3 * f) (triality_residualOvergroupsAt σ)
    (isSylowTwoOf_subgroupOf_top hUsyl) (fun j => ?_) hP' hm'
  have hcard := card_orbitField_D4_orientation Nat.prime_two hf hK (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) (d4Index j)
  have horb : (TwistTag.D4.orbit (d4Index j)).card = 1 ∨
      (TwistTag.D4.orbit (d4Index j)).card = 3 := by
    obtain ⟨n, hn⟩ := d4Index j
    have hn' : n < 2 := hn
    interval_cases n
    · exact Or.inr (by decide +revert)
    · exact Or.inl (by decide +revert)
  set c := (TwistTag.D4.orbit (d4Index j)).card with hc
  have hc2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j)) = 2 ^ (f * c) := by
    rw [hcard, pow_mul]
  by_cases h2 : 2 ≤ f * c
  · obtain ⟨g, hg, hker⟩ := Vol2Native.A312L.exists_levi_hom_fixed σ (d4Index j) hUsyl.2.1
      (H13.NQCat.exists_finset_card_four_of_card h2 hc2)
    refine LeviParam.of_sl2 hc2 h2 ?_ g hg hker
    rcases horb with h | h <;> rw [h] <;> omega
  · left
    have hfc : f * c = 1 := by
      rcases horb with h | h <;> rw [h] at h2 ⊢ <;> omega
    exact perfectCore_eq_bot_of_card_two σ (d4Index j) hUsyl.2.1 (by rw [hc2, hfc]; rfl)

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
