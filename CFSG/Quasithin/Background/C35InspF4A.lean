module

public import CFSG.Quasithin.Background.C35InspD4A
public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Gen
public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeInvolutionFusionStrata
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Schreier.J4SFrattini

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique Matrix CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fuel comm_famL₂ fam_zero fam_mem_U
  fam_mem_V0 fam_mem_V1 sylowV_zero_split sylowV_one_split center_V0_forced center_V1_forced
  testsV0 testsV1 rad_le_parabolic parabolic_le_normalizer_rad isPGroup_rad perfectCore_parabolic
  levi_hom generation_zero generation_one sylowV_zero_zero weylTwo_conj_fam)
open scoped commutatorElement

section F4

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem f4_comm_AF
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅sylowA a K s, sylowF a K 0 t⁆ = sylowH a K 0 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  have h : ⁅fam a K 0 s, fam a K 6 t⁆ = fam a K 8 (s * t) := by
    simpa [polyEval, monoEval, coordVal] using this
  exact h

theorem f4_FH_comm
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (i : K) :
    u * sylowH a K 0 i = sylowH a K 0 i * u := by
  rw [sylowH_zero_eq_centralZ]
  exact commute_centralZ ha hK hu i

theorem f4_F_mul
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g g' : K) :
    sylowF a K 0 g * sylowF a K 0 g' = sylowF a K 0 (g + g') := by
  rw [← weylOne_conj_sylowH g, ← weylOne_conj_sylowH g', ← weylOne_conj_sylowH (g + g'),
    ← sylowH_mul hK g g']
  group

theorem f4_FH_mul
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (g i g' i' : K) :
    sylowF a K 0 g * sylowH a K 0 i * (sylowF a K 0 g' * sylowH a K 0 i') =
      sylowF a K 0 (g + g') * sylowH a K 0 (i + i') := by
  have hc := f4_FH_comm ha hK (fam_mem_U (m := a) hK (n := 6) (by norm_num) g') i
  rw [← f4_F_mul hK, ← sylowH_mul hK]
  calc sylowF a K 0 g * sylowH a K 0 i * (sylowF a K 0 g' * sylowH a K 0 i') =
        sylowF a K 0 g * (sylowH a K 0 i * sylowF a K 0 g') * sylowH a K 0 i' := by group
    _ = sylowF a K 0 g * (sylowF a K 0 g' * sylowH a K 0 i) * sylowH a K 0 i' := by
        rw [show fam a K 6 g' = sylowF a K 0 g' from rfl] at hc
        rw [← hc]
    _ = _ := by group

omit [Finite K] in
theorem f4_FH_eq_sylowV
    (g i : K) :
    sylowF a K 0 g * sylowH a K 0 i = sylowV a K 0 0 0 0 0 0 g 0 i 0 0 0 := by
  rw [sylowV_zero_split]
  simp only [fam_zero (m := a) (K := K) (n := 1) (by norm_num),
    fam_zero (m := a) (K := K) (n := 2) (by norm_num),
    fam_zero (m := a) (K := K) (n := 3) (by norm_num),
    fam_zero (m := a) (K := K) (n := 4) (by norm_num),
    fam_zero (m := a) (K := K) (n := 5) (by norm_num),
    fam_zero (m := a) (K := K) (n := 7) (by norm_num),
    fam_zero (m := a) (K := K) (n := 9) (by norm_num),
    fam_zero (m := a) (K := K) (n := 10) (by norm_num),
    fam_zero (m := a) (K := K) (n := 11) (by norm_num), one_mul, mul_one]
  rfl

theorem f4_FH_inj
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g i g' i' : K}
    (h : sylowF a K 0 g * sylowH a K 0 i = sylowF a K 0 g' * sylowH a K 0 i') :
    g = g' ∧ i = i' := by
  rw [f4_FH_eq_sylowV, f4_FH_eq_sylowV] at h
  have hv := (bijOn_sylowVec (m := a) hK).2.1 (Set.mem_univ ![0, 0, 0, 0, 0, 0, g, 0, i, 0, 0, 0])
    (Set.mem_univ ![0, 0, 0, 0, 0, 0, g', 0, i', 0, 0, 0]) h
  exact ⟨congrFun hv 6, congrFun hv 8⟩

@[expose] noncomputable def coordFH
    (a : ℕ) (z : ModGL F4.tag K) : Fin 2 → K :=
  open Classical in
  if h : ∃ w : Fin 2 → K, z = sylowF a K 0 (largeReeRhoHom K a (w 1)) *
      sylowH a K 0 (largeReeRhoHom K a (w 0)) then h.choose else 0

theorem coordFH_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (w : Fin 2 → K) :
    coordFH a (sylowF a K 0 (largeReeRhoHom K a (w 1)) *
      sylowH a K 0 (largeReeRhoHom K a (w 0))) = w := by
  have h : ∃ w' : Fin 2 → K, sylowF a K 0 (largeReeRhoHom K a (w 1)) *
      sylowH a K 0 (largeReeRhoHom K a (w 0)) = sylowF a K 0 (largeReeRhoHom K a (w' 1)) *
        sylowH a K 0 (largeReeRhoHom K a (w' 0)) := ⟨w, rfl⟩
  rw [coordFH, dite_eq_left h]
  obtain ⟨h1, h0⟩ := f4_FH_inj hK h.choose_spec
  have hinj := (largeReeRhoHom K a).injective
  ext i
  fin_cases i
  · exact (hinj h0).symm
  · exact (hinj h1).symm

theorem centerV0_f4
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : ModGL F4.tag K}
    (hxV : x ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩)
    (hxC : x ∈ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K))) :
    ∃ g i : K, x = sylowF a K 0 g * sylowH a K 0 i := by
  have hxU : x ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le _ hxV
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hxU
  have hy0 : y 0 = 0 := eq_zero_of_sylowV_mem_complement hK hxV
  have e : sylowVec a K y = sylowV a K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) := by
    simp only [sylowVec, hy0]
  have hcomm : ∀ n ∈ testsV0, sylowV a K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) * fam a K n 1 = fam a K n 1 * sylowV a K 0 (y 1) (y 2) (y 3) (y 4) (y 5)
        (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) := by
    intro n hn
    have hn' : 1 ≤ n ∧ n ≤ 11 := by
      simp only [testsV0, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    have hnV := fam_mem_V0 hK hn'.1 hn'.2 (1 : K)
    have := Subgroup.mem_centralizer_iff.1 hxC _ hnV
    rw [e] at this
    exact this.symm
  obtain ⟨hb, hc, hd, he, hf, hh, hj, hk, hl⟩ := center_V0_forced (m := a) (y 1) (y 2) (y 3)
    (y 4) (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) hcomm
  refine ⟨y 6, y 8, ?_⟩
  rw [e, hb, hc, hd, he, hf, hh, hj, hk, hl, f4_FH_eq_sylowV]

theorem centerV1_f4
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : ModGL F4.tag K}
    (hxV : x ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (hxC : x ∈ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K))) :
    ∃ i : K, x = centralZ K a i := by
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

theorem pCoreOf_perfectCore_f4
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    pCoreOf 2 (perfectCore (F4.reeLocalParabolic K a j)) =
      F4.reeFixedOrbitComplementUnipotent K a j := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model
    ha hK
  have hj : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    rcases j with ⟨j, hj⟩
    have hj2 : j < 2 := hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hj with rfl | rfl
  · have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, hg, hk⟩ := (levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K a) h0eq
      (isSimpleGroup_rankOneGroupOne ha hK).2).1
    exact H13.NQCat.G2Rad.pCoreOf_perfectCore_eq (rad_le_parabolic _)
      (parabolic_le_normalizer_rad _) (isPGroup_rad ha hK _)
      ⟨generation_zero ha hK, ↥(rankOneGroupOne K a), inferInstance, g, inferInstance, hg, hk⟩
  · have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, hg, hk⟩ := (levi_hom ha hK ⟨1, by decide⟩ (M := rankOneGroupTwo K a) h1eq
      (isSimpleGroup_rankOneGroupTwo ha hK).2).1
    exact H13.NQCat.G2Rad.pCoreOf_perfectCore_eq (rad_le_parabolic _)
      (parabolic_le_normalizer_rad _) (isPGroup_rad ha hK _)
      ⟨generation_one ha hK, ↥(rankOneGroupTwo K a), inferInstance, g, inferInstance, hg, hk⟩

theorem rankOneGroupTwo_centralizes_centralZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    rankOneGroupTwo K a ≤ Subgroup.centralizer {centralZ K a c} := by
  rw [rankOneGroupTwo, Subgroup.closure_le]
  have hcomm : ∀ {g x : ModGL F4.tag K}, g * x * g⁻¹ = x → g * x = x * g := fun {g x} h => by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  rintro g ((hg | ⟨v, rfl⟩) | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact commute_centralZ ha hK (reeFixedOrbitUnipotent_le _ hg) c
  · have h := torusPair_conj_centralZ hK 1 v c
    rw [Units.val_one, one_pow, one_mul, rankOneTorusPair_right] at h
    exact hcomm h
  · have h := weylTwo_conj_fam (m := a) (K := K) (n := 8) (n' := 8) (by decide +kernel) c
    rw [show fam a K 8 c = centralZ K a c from sylowH_zero_eq_centralZ c] at h
    exact hcomm h

theorem perfectCore_P1_le_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) ≤
      Subgroup.centralizer {centralZ K a c} := by
  rw [perfectCore_parabolic]
  refine (perfectCore_le _).trans ?_
  obtain ⟨-, -, hsup, -⟩ := ree_structure (K := K) (a := a) ⟨1, by decide⟩
  obtain ⟨-, ⟨h1eq, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  rw [← hsup, h1eq]
  refine sup_le (fun v hv => ?_) (rankOneGroupTwo_centralizes_centralZ ha hK c)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_centralZ ha hK (reeFixedOrbitComplementUnipotent_le _ hv) c

theorem a1Hom_uSL_f4
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    largeReeA1Hom K a (uSL c) = sylowA a K (largeReeRhoHom K a c) := by
  have h1 : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl
  have h0 : LargeReeCover.nTwo K 0 = 1 := by
    rw [LargeReeCover.nTwo, show LargeReeCover.kTwo 0 = ⟨0, by decide⟩ from rfl, h1,
      canonicalRep_one]
  rw [largeReeA1Hom_uSL, sylowA_eq, twoCoordG, h0, one_mul, inv_one, mul_one, stdTwoG_eq_xUnit,
    largeReeRhoHom_apply, largeReeSigma_pow hK]

omit [Finite K] in
theorem a1Hom_WSL_f4 :
    largeReeA1Hom K a WSL = weylOne K := by
  change largeReeA1Hom K a WSL =
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)
  rw [largeReeA1Hom_WSL, canonicalRep_F4_fixedOrbitElement_zero]

theorem levi_proj_f4
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ g : ↥(perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩)) →*
        ↥(largeReeA1Hom K a).range, Function.Surjective g ∧
      ∀ x, ((g x : ↥(largeReeA1Hom K a).range) : ModGL F4.tag K)⁻¹ * (x : ModGL F4.tag K) ∈
        F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hVN, hNV, hsup, hMnorm⟩ := ree_structure (K := K) (a := a) ⟨0, by decide⟩
  obtain ⟨⟨h0eq, -, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  rw [h0eq, rankOneGroupOne_eq_range hK] at hsup hMnorm
  have hV2 := isPGroup_rad ha hK ⟨0, by decide⟩
  have : IsSimpleGroup (SL2 K) := isSimpleGroup_SL2 ha hK
  have : IsSimpleGroup ↥(largeReeA1Hom K a).range :=
    (MonoidHom.ofInjective largeReeA1Hom_injective).symm.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := exists_SL2_mul_ne_mul (K := K)
  have hnab : ∃ x y : ↥(largeReeA1Hom K a).range, x * y ≠ y * x :=
    ⟨⟨_, x, rfl⟩, ⟨_, y, rfl⟩, fun h => hxy (largeReeA1Hom_injective (by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h))⟩
  have hMperf := perfect_of_isSimpleGroup_nonabelian hnab
  have hVM := inf_eq_bot_of_simple hMnorm hV2 hMperf
  obtain ⟨g, hg, hk⟩ := exists_levi_proj hVN hNV hVM hsup le_rfl hMperf (perfectCore_le _)
  have hpc := perfectCore_parabolic (K := K) (a := a) ⟨0, by decide⟩
  refine ⟨g.comp (MulEquiv.subgroupCongr hpc).toMonoidHom,
    hg.comp (MulEquiv.subgroupCongr hpc).surjective, fun x => ?_⟩
  have h2 := hk (MulEquiv.subgroupCongr hpc x)
  rwa [MulEquiv.subgroupCongr_apply] at h2

theorem f4_action
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (D : SL2 K) (w : Fin 2 → K) :
    largeReeA1Hom K a D * (sylowF a K 0 (largeReeRhoHom K a (w 1)) *
        sylowH a K 0 (largeReeRhoHom K a (w 0))) * (largeReeA1Hom K a D)⁻¹ =
      sylowF a K 0 (largeReeRhoHom K a (((D : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1)) *
        sylowH a K 0 (largeReeRhoHom K a (((D : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0)) := by
  set ρ := largeReeRhoHom K a with hρ
  set R := largeReeA1Hom K a with hR
  revert w
  refine SL2_induction_uW (p := fun D => ∀ w : Fin 2 → K,
    R D * (sylowF a K 0 (ρ (w 1)) * sylowH a K 0 (ρ (w 0))) * (R D)⁻¹ =
      sylowF a K 0 (ρ (((D : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1)) *
        sylowH a K 0 (ρ (((D : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0))) ?_ ?_ ?_ ?_ D
  · intro g g' hg hg' w
    have e : R (g * g') * (sylowF a K 0 (ρ (w 1)) * sylowH a K 0 (ρ (w 0))) * (R (g * g'))⁻¹ =
        R g * (R g' * (sylowF a K 0 (ρ (w 1)) * sylowH a K 0 (ρ (w 0))) * (R g')⁻¹) *
          (R g)⁻¹ := by
      rw [map_mul]
      group
    rw [e, hg', hg]
    have hm : ((g * g' : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w =
        (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ((g' : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hm]
  · intro g hg w
    have h1 := hg (((g⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    have hm : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (((g⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec]
      have h : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
        congrArg (fun z : SL2 K => (z : Matrix (Fin 2) (Fin 2) K)) (mul_inv_cancel g)
      rw [h, Matrix.one_mulVec]
    rw [hm] at h1
    rw [map_inv, inv_inv, ← h1]
    group
  · intro c w
    rw [hR, a1Hom_uSL_f4 hK c, ← hρ, uSL_mulVec c w]
    have hAU : sylowA a K (ρ c) ∈ F4.reeFixedPosUnipotent K a :=
      fam_mem_U (m := a) hK (n := 0) (by norm_num) (ρ c)
    have h1 : sylowA a K (ρ c) * sylowF a K 0 (ρ (w 1)) * (sylowA a K (ρ c))⁻¹ =
        sylowH a K 0 (ρ c * ρ (w 1)) * sylowF a K 0 (ρ (w 1)) := by
      rw [← f4_comm_AF hK, commutatorElement_def]
      group
    have h2 : sylowA a K (ρ c) * sylowH a K 0 (ρ (w 0)) * (sylowA a K (ρ c))⁻¹ =
        sylowH a K 0 (ρ (w 0)) := by
      rw [f4_FH_comm ha hK hAU, mul_inv_cancel_right]
    have hFU : sylowF a K 0 (ρ (w 1)) ∈ F4.reeFixedPosUnipotent K a :=
      fam_mem_U (m := a) hK (n := 6) (by norm_num) (ρ (w 1))
    have e1 : sylowA a K (ρ c) * (sylowF a K 0 (ρ (w 1)) * sylowH a K 0 (ρ (w 0))) *
        (sylowA a K (ρ c))⁻¹ =
          (sylowA a K (ρ c) * sylowF a K 0 (ρ (w 1)) * (sylowA a K (ρ c))⁻¹) *
            (sylowA a K (ρ c) * sylowH a K 0 (ρ (w 0)) * (sylowA a K (ρ c))⁻¹) := by
      group
    rw [e1, h1, h2, ← (f4_FH_comm ha hK hFU _), mul_assoc, sylowH_mul hK]
    have e2 : ρ (![w 0 + c * w 1, w 1] 0) = ρ c * ρ (w 1) + ρ (w 0) := by
      show ρ (w 0 + c * w 1) = _
      rw [map_add, map_mul, add_comm]
    rw [e2]
    rfl
  · intro w
    rw [hR, a1Hom_WSL_f4 (K := K) (a := a)]
    have hneg : ∀ x : K, -x = x := by
      have : CharP K 2 := ‹CharP K F4.prime›
      exact fun x => CharTwo.neg_eq x
    rw [WSL_mulVec_of_neg hneg w]
    have e1 : weylOne K * (sylowF a K 0 (ρ (w 1)) * sylowH a K 0 (ρ (w 0))) * (weylOne K)⁻¹ =
        (weylOne K * sylowF a K 0 (ρ (w 1)) * (weylOne K)⁻¹) *
          (weylOne K * sylowH a K 0 (ρ (w 0)) * (weylOne K)⁻¹) := by
      group
    have hFU : sylowF a K 0 (ρ (w 0)) ∈ F4.reeFixedPosUnipotent K a :=
      fam_mem_U (m := a) hK (n := 6) (by norm_num) (ρ (w 0))
    rw [e1, weylOne_conj_sylowF, weylOne_conj_sylowH, ← f4_FH_comm ha hK hFU]
    rfl

end F4

end CFSG.Quasithin.C35Pf
