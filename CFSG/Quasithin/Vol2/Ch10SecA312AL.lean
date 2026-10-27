module

public import CFSG.Quasithin.Vol2.Ch10SecA312AJ
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Gen

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {S : Type} [Group S] [Finite S]

theorem sup_ne_top_not_solvable (hq : CFSG.IsQuasisimple S) {U B : Subgroup S}
    (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) : B ⊔ U ≠ ⊤ ∧ ¬ Group.IsSolvable ↥(B ⊔ U) := by
  have hB' : B ∈ cComp (B ⊔ U) := hB
  refine ⟨fun htop => ?_, fun hs => ?_⟩
  · rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  · exact not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ U))
        (Subgroup.inclusion_injective _))

theorem eq_of_le_residual (hq : CFSG.IsQuasisimple S) {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hP : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt S U P) {B : Subgroup S}
    (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) {j k : Fin 2} (hj : B ≤ P j) (hk : B ≤ P k) :
    j = k := by
  obtain ⟨hne, hns⟩ := sup_ne_top_not_solvable hq hB hBtop
  obtain ⟨i, hi, -⟩ := hP.2.2.2.2.1 (B ⊔ U) le_sup_right hne hns
  rw [(hi j).1 (sup_le hj (hP.2.1 j)), (hi k).1 (sup_le hk (hP.2.1 k))]

end General

section F4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem f4_center_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : ModGL F4.tag K}
    (hxV : x ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (hxC : x ∈ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K))) :
    ∃ c : K, x = centralZ K a c := by
  have hxU : x ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le _ hxV
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hxU
  have hx12 : y 1 = 0 ∧ y 2 = 0 := by
    refine coord_one_two_eq hK hxV ?_
    rw [sylowB_zero_zero, one_mul]
  have e : sylowVec a K y = sylowV a K (y 0) 0 0 (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) := by
    simp only [sylowVec, hx12.1, hx12.2]
  have hcomm : ∀ n ∈ testsV1, sylowV a K (y 0) 0 0 (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) * fam a K n 1 = fam a K n 1 * sylowV a K (y 0) 0 0 (y 3) (y 4) (y 5)
        (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) := by
    intro n hn
    have hn' : (n = 0 ∨ 3 ≤ n) ∧ n ≤ 11 := by
      simp only [testsV1, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    have hnV := fam_mem_V1 hK hn'.1 hn'.2 (1 : K)
    have := Subgroup.mem_centralizer_iff.1 hxC _ hnV
    rw [e] at this
    exact this.symm
  obtain ⟨ha0, hd, he, hf, hg, hh, hj, hk, hl⟩ := center_V1_forced (m := a) (y 0) (y 3) (y 4)
    (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) hcomm
  refine ⟨y 8, ?_⟩
  rw [e, ha0, hd, he, hf, hg, hh, hj, hk, hl, sylowV_one_split]
  simp only [fam_zero (m := a) (K := K) (n := 0) (by norm_num),
    fam_zero (m := a) (K := K) (n := 3) (by norm_num),
    fam_zero (m := a) (K := K) (n := 4) (by norm_num),
    fam_zero (m := a) (K := K) (n := 5) (by norm_num),
    fam_zero (m := a) (K := K) (n := 6) (by norm_num),
    fam_zero (m := a) (K := K) (n := 7) (by norm_num),
    fam_zero (m := a) (K := K) (n := 9) (by norm_num),
    fam_zero (m := a) (K := K) (n := 10) (by norm_num),
    fam_zero (m := a) (K := K) (n := 11) (by norm_num), one_mul, mul_one]
  exact sylowH_zero_eq_centralZ (y 8)

theorem f4_perfectCore_one_le
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) ≤ centralizerZ K a := by
  rw [perfectCore_parabolic]
  obtain ⟨-, -, hsup, -⟩ := Vol2Native.A312L.ree_structure (K := K) (a := a) ⟨1, by decide⟩
  obtain ⟨-, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  rw [h1eq] at hsup
  rw [← hsup]
  exact perfectCore_le _

theorem f4_perfectCore_zero_le
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : K} (hc : c ≠ 0)
    (hzB : ∀ x ∈ perfectCore (F4.reeParabolic K a {⟨0, by decide⟩}),
      centralZ K a c * x = x * centralZ K a c) :
    perfectCore (F4.reeParabolic K a {⟨0, by decide⟩}) ≤
      F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have hinj : Function.Injective (fun x : K => x ^ 2 ^ a) := fun x y h =>
    (iterateFrobenius K 2 a).injective (by simpa [iterateFrobenius_def] using h)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) c⁻¹
  have hx' : x ^ 2 ^ a = c⁻¹ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hx'
    exact hc (inv_eq_zero.mp hx'.symm)
  set t := CFSG.LieType.Ree.LargeReeCover.torusPair a (Units.mk0 x hx0, 1) with ht
  have htP : t ∈ F4.reeParabolic K a {⟨0, by decide⟩} :=
    reeFixedBorel_le_reeParabolic F4 K a _
      (reeFixedTorus_le_reeFixedBorel (rankOne_torusPair_mem_reeFixedTorus hK _ _))
  have hconj : t * centralZ K a c * t⁻¹ = centralZ K a 1 := by
    rw [ht, torusPair_conj_centralZ hK, Units.val_mk0, hx', inv_mul_cancel₀ hc]
  intro y hy
  have htN : t⁻¹ ∈ Subgroup.normalizer
      (perfectCore (F4.reeParabolic K a {⟨0, by decide⟩}) : Set (ModGL F4.tag K)) :=
    inv_mem (normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer htP))
  have hy' : t⁻¹ * y * t ∈ perfectCore (F4.reeParabolic K a {⟨0, by decide⟩}) := by
    have h := (Subgroup.mem_normalizer_iff.1 htN y).1 hy
    rwa [inv_inv] at h
  have h1 := hzB _ hy'
  have hyz : y * centralZ K a 1 = centralZ K a 1 * y := by
    rw [← hconj]
    calc y * (t * centralZ K a c * t⁻¹) = t * ((t⁻¹ * y * t) * centralZ K a c) * t⁻¹ := by
          group
      _ = t * (centralZ K a c * (t⁻¹ * y * t)) * t⁻¹ := by rw [h1]
      _ = t * centralZ K a c * t⁻¹ * y := by group
  have hyΓ : y ∈ F4.reeGamma K a := reeParabolic_le F4 K a _ (perfectCore_le _ hy)
  exact reeGamma_inf_centralizer_le_reeLocalParabolic ha hK
    ⟨hyΓ, Subgroup.mem_centralizer_singleton_iff.2 hyz⟩

theorem zcentFor_F4
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hq : CFSG.IsQuasisimple ↥(F4.reeGamma K a)) : ZCentFor ↥(F4.reeGamma K a) := by
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
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hres := large_Ree_residualOvergroupsAt hK
  have hsimple : ∀ j, ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T),
      (∃ x y : T, x * y ≠ y * x) ∧ ∃ g : ↥(perfectCore ((F4.reeParabolic K a {f4Index j}).subgroupOf
        (F4.reeGamma K a))) →* T, Function.Surjective g ∧ Group.IsSolvable g.ker := by
    intro j
    rcases hcases (f4Index j) with hj | hj
    · have := (isSimpleGroup_rankOneGroupOne ha hK).1
      obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq) (isSimpleGroup_rankOneGroupOne ha hK).2
      exact ⟨_, inferInstance, inferInstance, (isSimpleGroup_rankOneGroupOne ha hK).2, g, hg,
        by have := hk.isNilpotent; infer_instance⟩
    · have := (isSimpleGroup_rankOneGroupTwo ha hK).1
      obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := K) (a := a) hUp (f4Index j)
        (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq) (isSimpleGroup_rankOneGroupTwo ha hK).2
      exact ⟨_, inferInstance, inferInstance, (isSimpleGroup_rankOneGroupTwo ha hK).2, g, hg,
        by have := hk.isNilpotent; infer_instance⟩
  refine ZCentFor.of_sylow _ (isSylowTwoOf_subgroupOf_top hUsyl) fun B hB hBtop z => ?_
  obtain ⟨j, rfl⟩ := Vol2Native.A312L.rank2_eq_perfectCore hq hres hsimple hB hBtop
  have hPC : ∀ i, F4.reeParabolic K a {i} ≤ F4.reeGamma K a := fun i => reeParabolic_le F4 K a _
  have hup : ∀ i, ∀ x ∈ perfectCore (F4.reeParabolic K a {i}), ∃ y ∈ perfectCore
      ((F4.reeParabolic K a {i}).subgroupOf (F4.reeGamma K a)), (y : ModGL F4.tag K) = x :=
    fun i x hx => by
      rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC i)] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩
  intro hzT hz1 hzc hzB
  rcases hcases (f4Index j) with hj | hj
  · exfalso
    obtain ⟨j0, hj0⟩ := f4Index_surjective (⟨0, by decide⟩ : Fin F4.fixedOrbitCount)
    obtain ⟨j1, hj1⟩ := f4Index_surjective (⟨1, by decide⟩ : Fin F4.fixedOrbitCount)
    rw [hj] at hzB
    have hzZ : (z : ModGL F4.tag K) ∈ Set.range (centralZ K a) := by
      rw [← coe_center_eq_range_centralZ ha hK]
      refine ⟨⟨z, Subgroup.mem_subgroupOf.1 hzT⟩, Subgroup.mem_center_iff.2 fun u => ?_, rfl⟩
      have := hzc ⟨u, hUC u.2⟩ (Subgroup.mem_subgroupOf.2 u.2)
      exact Subtype.ext (congrArg Subtype.val this).symm
    obtain ⟨c, hc⟩ := hzZ
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hz1 (Subtype.ext (by rw [← hc, centralZ_zero]; rfl))
    have hle := f4_perfectCore_zero_le ha hK hc0 fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hup _ x hx
      rw [hc]
      exact congrArg Subtype.val (hzB y hy)
    have hB0 : perfectCore ((F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a)) ≤
        (F4.reeParabolic K a {f4Index j0}).subgroupOf (F4.reeGamma K a) := by
      rw [hj, hj0]
      exact perfectCore_le _
    have hB1 : perfectCore ((F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a)) ≤
        (F4.reeParabolic K a {f4Index j1}).subgroupOf (F4.reeGamma K a) := by
      intro y hy
      rw [hj] at hy
      rw [Subgroup.mem_subgroupOf, hj1, reeParabolic_singleton]
      refine hle ?_
      rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC _)]
      exact ⟨y, hy, rfl⟩
    have h01 := eq_of_le_residual hq hres hB hBtop hB0 hB1
    rw [h01, hj1] at hj0
    exact absurd (congrArg Fin.val hj0) (by decide)
  · rw [hj] at hzB ⊢
    intro v hv hvc _ b hb
    have hPL : F4.reeParabolic K a {⟨1, by decide⟩} = F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
      reeParabolic_singleton _
    have hVB : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤
        perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) :=
      (generation_one ha hK).trans (commutator_perfectCore_le_of_le (rad_le_parabolic _))
    have hQO := subgroupOf_le_pCoreOf (C := F4.reeGamma K a)
      (B := perfectCore ((F4.reeParabolic K a {⟨1, by decide⟩}).subgroupOf (F4.reeGamma K a)))
      (isPGroup_rad ha hK _) (fun q hq => hup _ q (by rw [hPL]; exact hVB hq))
      (fun b hb => parabolic_le_normalizer_rad _ (by
        rw [← hPL]; exact Subgroup.mem_subgroupOf.1 (perfectCore_le _ hb)))
    have hvC : (v : ModGL F4.tag K) ∈ Subgroup.centralizer
        (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) :=
      Subgroup.mem_centralizer_iff.2 fun q hq => congrArg Subtype.val
        (hvc ⟨q, hPC _ (by rw [hPL]; exact rad_le_parabolic _ hq)⟩ (hQO hq))
    have hvB : v ∈ perfectCore ((F4.reeParabolic K a {⟨1, by decide⟩}).subgroupOf
        (F4.reeGamma K a)) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hv
    have hvP : (v : ModGL F4.tag K) ∈ F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
      rw [← hPL]; exact Subgroup.mem_subgroupOf.1 (perfectCore_le _ hvB)
    obtain ⟨c, hc⟩ := f4_center_one hK (selfCentralizing_one ha hK ⟨hvP, hvC⟩) hvC
    have hb' : (b : ModGL F4.tag K) ∈ perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
      rw [← hPL, ← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC _)]
      exact ⟨b, hb, rfl⟩
    refine Subtype.ext ?_
    show (b : ModGL F4.tag K) * v = v * b
    rw [hc]
    exact Subgroup.mem_centralizer_singleton_iff.1
      (centralizerZ_le_centralizer ha hK c (f4_perfectCore_one_le ha hK hb'))

end F4

theorem zcentFor_of_is2F4
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ} (h : Is2F4 f X) :
    ZCentFor X := by
  obtain ⟨a, K, _, _, _, ha, rfl, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h
  exact ZCentFor.of_mulEquiv e (zcentFor_F4 ha hK (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end CFSG.Quasithin.Vol2.Ch10.A312A
