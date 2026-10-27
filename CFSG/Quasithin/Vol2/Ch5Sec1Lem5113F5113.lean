module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.Quasithin.H13.NQCatBND4
public import CFSG.Quasithin.H13.NQCatBNRee

public section

namespace CFSG.Quasithin.H13.F5113

open Matrix CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Quasithin (perfectCore isSolvable_iff_perfectCore_eq_bot perfectCore_eq_self_of_perfect
  perfectCore_perfect)

theorem exists_coatom_of_conj {Y : Type} [Group Y] [Finite Y] {U₀ U P : Subgroup Y}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) (hUP : U₀ ≤ P) (hP : P ⋖ ⊤)
    (hs : Group.IsSolvable ↥P) :
    ∃ P' : Subgroup Y, U ≤ P' ∧ P' ⋖ ⊤ ∧ Group.IsSolvable ↥P' := by
  obtain ⟨g, rfl⟩ := NQCat.exists_conj_map_eq hU₀ hU
  set e := MulAut.conj g
  refine ⟨P.map e.toMonoidHom, Subgroup.map_mono hUP, ?_, ?_⟩
  · have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup e)).mpr hP
    have h2 : MulEquiv.mapSubgroup e ⊤ = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
    rw [h2] at h1
    exact h1
  · exact Group.isSolvable_of_surjective
      (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.surjective _)

theorem exists_coatom_linear_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) {Y : Type} [Group Y] [Finite Y]
    (π : SpecialLinearGroup (Fin 3) K →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ scalars 3 K) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Subgroup Y, U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨1, by rw [hK2]; norm_num⟩
  have hres := Vol2Native.A312L.linear_three_residual_of_cover hK π hπ hker
  have hbot : perfectCore (Setup.X7a.Q3 K 0) = ⊥ := by
    have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
      refine Vol2Native.A312L.isSolvable_of_card_two_three (a := 1) (b := 1) ?_
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
      norm_num
    have hkerS : Group.IsSolvable (Vol2Native.A312L.blk3 (K := K) 0).ker := by
      have := (Vol2Native.A312L.blk3_ker_isPGroup hK 0).isNilpotent
      infer_instance
    have hN : Group.IsSolvable ↥(perfectCore (Setup.X7a.Q3 K 0)) :=
      Group.isSolvable_of_ker_le_range (Vol2Native.A312L.blk3 (K := K) 0).ker.subtype
        (Vol2Native.A312L.blk3 0) (by rw [Subgroup.range_subtype])
    have := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Setup.X7a.Q3 K 0))).mp hN
    rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at this
  have hQs : Group.IsSolvable ↥(Setup.X7a.Q3 K 0) :=
    (isSolvable_iff_perfectCore_eq_bot _).mpr hbot
  have hPs : Group.IsSolvable ↥((Setup.X7a.Q3 K 0).map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap _) (π.subgroupMap_surjective _)
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf ((unitriangular 3 K).map π) ⊤ :=
    NQCat.BN.isSylowTwoOf_map π hπ (hQ ▸ isSylowTwoOf_top_of_sylow Q)
  exact exists_coatom_of_conj hU₀ hU (hres.2.1 0) ((hres.2.2.1 _ (hres.2.1 0)).mpr ⟨0, rfl⟩) hPs

theorem exists_coatom_psl3_two {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Quasithin.IsPSL 3 2 1 Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Subgroup Y, U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  let φ : projectiveSL 3 K ≃* Y := (e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 K)).symm
  refine exists_coatom_linear_two (by rw [hK]; norm_num) (φ.toMonoidHom.comp (proj 3 K))
    (φ.surjective.comp (proj_surjective 3 K)) (fun x hx => ?_) hU
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff] at hx
  exact proj_eq_one_iff.mp hx

theorem exists_coatom_sl3_two {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Quasithin.IsSL3 (2 ^ 1) Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Subgroup Y, U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  let φ : SpecialLinearGroup (Fin 3) K ≃* Y := (specialLinearGroupEquivStatedSL 3 K).trans e.symm
  refine exists_coatom_linear_two (by rw [hK]; norm_num) φ.toMonoidHom φ.surjective
    (fun x hx => ?_) hU
  rw [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem solvOver_sl3 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    NQCat.SolvOver (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K) := fun A hUA hA => by
  rw [normalizer_unitriangular]
  exact NQCat.SL3.le_upperTriangular_of_isSolvable hK4 hUA hA

theorem solvOver_of_isSL3 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 2 ≤ f)
    (hY : CFSG.Quasithin.IsSL3 (2 ^ f) Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 := NQCat.exists_finset_card_four_of_card hf hK
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  exact NQCat.solvOver_of_sylow (solvOver_sl3 hK4) (hQ ▸ isSylowTwoOf_top_of_sylow Q)
    ((specialLinearGroupEquivStatedSL 3 K).trans e.symm) hU

theorem exists_coatom_d42
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Quasithin.Is3D4 2 1 Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Subgroup Y, U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, σ, φ, hK, hσ, hφ, hres, -⟩ := Setup.X6.even_rank_two_residual_triality hY hU
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1 * 3) (by norm_num)
      (by rw [hK, ← pow_mul])
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set a : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩ with ha
  obtain ⟨j, hj⟩ := Setup.X6.d4Index_surjective a
  have hm : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2 ^ 1 := by
    have h1 := card_orbitField_D4_orientation (K := K) Nat.prime_two (f := 1) le_rfl hK
      (r := 1) (Or.inl rfl) (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) a
    have h2 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
    rw [h2, pow_one] at h1
    exact h1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUp : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    have h1 : IsPGroup 2 ↥((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← hφ]
      exact hU.2.1.map _
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hUC)
  obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := Vol2Native.A312L.fixed_structure σ a
  have hVU : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a ≤
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) :=
    IsPGroup.of_injective hUp (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) := by
    have := hV2.isNilpotent
    infer_instance
  have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom a)) := by
    refine Vol2Native.A312L.isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm]
    norm_num
  have hMs : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
  have hNs : Group.IsSolvable ↥(Setup.X6.fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a) :=
    Vol2Native.A312L.isSolvable_of_levi hVN hNV hsup hVs hMs
  have hpcN : perfectCore (Setup.X6.fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp hNs
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
  have hbot : perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = ⊥ := by
    apply Subgroup.map_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
    rw [Vol2Native.A312L.perfectCore_map_subgroupOf hPC, Vol2Native.A312L.fixed_perfectCore_eq σ a,
      hpcN, Subgroup.map_bot]
  have hs : Group.IsSolvable ↥((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (isSolvable_iff_perfectCore_eq_bot _).mpr hbot
  refine ⟨_, hres.2.1 j, (hres.2.2.1 _ (hres.2.1 j)).mpr ⟨j, rfl⟩, ?_⟩
  beta_reduce
  rw [hj]
  exact Group.isSolvable_of_surjective
    (f := (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).equivMapOfInjective
      φ.symm.toMonoidHom φ.symm.injective).toMonoidHom) (MulEquiv.surjective _)

theorem exists_coatom_tits
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Quasithin.IsTits Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Subgroup Y, U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  obtain ⟨H, N, -, hUH, -, hH, hN, hlat, hHs, -⟩ := Setup.X6.titsSylowOvergroupLattice Y hY U hU
  obtain ⟨hHt, -⟩ := Setup.X6.ne_top_of_card hH hN
  refine ⟨H, hUH, ⟨lt_top_iff_ne_top.mpr hHt, fun M hHM hMt => ?_⟩, hHs⟩
  rcases hlat M (hUH.trans hHM.le) with rfl | rfl | rfl | rfl
  · exact absurd (hUH.trans_lt hHM) (lt_irrefl _)
  · exact lt_irrefl _ hHM
  · have h1 := Subgroup.card_le_of_le hHM.le
    rw [hH, hN] at h1
    omega
  · exact lt_irrefl _ hMt

theorem factF5113_holds :
    FactF5113 := by
  intro Y _ _ hY U hU hmax Z hUZ hZ
  have hno : ∀ P : Subgroup Y, U ≤ P → P ⋖ ⊤ → Group.IsSolvable ↥P → False :=
    fun P h1 h2 h3 => hmax P h1 h2 h3
  rcases hY with ⟨f, ⟨hf, hL⟩ | ⟨hf, hSL⟩ | ⟨hf, hSp⟩ | ⟨hf, hG⟩ | ⟨hf, hD⟩ | ⟨-, -, hF⟩⟩ | hT
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨P, h1, h2, h3⟩ := exists_coatom_psl3_two hL hU
      exact (hno P h1 h2 h3).elim
    · exact NQCat.lieOvergroupFactL3Sp4_holds Y
        (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 f hL).2 ⟨f, hf2, Or.inl hL⟩ U hU Z hUZ hZ
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨P, h1, h2, h3⟩ := exists_coatom_sl3_two hSL hU
      exact (hno P h1 h2 h3).elim
    · exact solvOver_of_isSL3 hf2 hSL hU Z hUZ hZ
  · exact NQCat.lieOvergroupFactL3Sp4_holds Y
      (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 2 2 f hSp)
      ⟨f, hf, Or.inr hSp⟩ U hU Z hUZ hZ
  · exact NQCat.BN.solvOver_of_isG2 hf hG hU Z hUZ hZ
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨P, h1, h2, h3⟩ := exists_coatom_d42 hD hU
      exact (hno P h1 h2 h3).elim
    · exact NQCat.BN.solvOver_of_is3D4 hf2 hD hU Z hUZ hZ
  · exact NQCat.BN.solvOver_of_is2F4 hF hU Z hUZ hZ
  · obtain ⟨P, h1, h2, h3⟩ := exists_coatom_tits hT hU
    exact (hno P h1 h2 h3).elim

end CFSG.Quasithin.H13.F5113
