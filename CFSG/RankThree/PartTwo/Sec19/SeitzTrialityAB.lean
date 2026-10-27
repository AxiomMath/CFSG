module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel
public import CFSG.RankThree.PartOne.SEITZ8.D4Main
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofCentS

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

structure D4Par (n : ℕ) (X : Type) [Field X] [Finite X] (σ : X ≃+* X) : Prop where
  one_le : 1 ≤ n
  card : Nat.card X = (2 ^ n) ^ 3
  frob : ∀ c : X, σ c = c ^ (2 ^ n)

section Par

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem D4Par.charP (P : D4Par n X σ) : CharP X 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := n * 3) (Nat.mul_pos P.one_le (by norm_num)) (by rw [P.card, ← pow_mul])

theorem D4Par.sigma_cube (P : D4Par n X σ) (c : X) : σ (σ (σ c)) = c :=
  CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) P.card P.frob c

theorem D4Par.sigma_cube_hom (P : D4Par n X σ) :
    ∀ c : X, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := fun c => P.sigma_cube c

theorem D4Par.sigma_pow_three (P : D4Par n X σ) : σ ^ 3 = 1 :=
  RingEquiv.ext fun c => by
    rw [pow_succ, pow_two]
    exact P.sigma_cube c

theorem D4Par.card_fix (P : D4Par n X σ) : Nat.card (fixSubfield σ) = 2 ^ n :=
  CFSG.RankThree.PartOne.SEITZ8.card_fixedField P.one_le P.card (σ := σ.toRingHom) P.frob

theorem D4Par.card_eq_cube (P : D4Par n X σ) : Nat.card X = Nat.card (fixSubfield σ) ^ 3 := by
  rw [P.card, P.card_fix]

theorem D4Par.exists_not_fixed (P : D4Par n X σ) : ∃ c : X, σ c ≠ c := by
  by_contra h
  push Not at h
  have hall : ∀ c : X, c ∈ fixSubfield σ := fun c => h c
  have hsub : Nat.card (fixSubfield σ) = Nat.card X := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [P.card_fix, P.card] at hsub
  have h1 : 2 ^ n < (2 ^ n) ^ 3 := by
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := P.one_le; omega)
    calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
      _ < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
  omega

theorem D4Par.four_le_card_fix (P : D4Par n X σ) (hn : 2 ≤ n) : 4 ≤ Nat.card (fixSubfield σ) := by
  rw [P.card_fix]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem D4Par.four_dvd_card_fix (P : D4Par n X σ) (hn : 2 ≤ n) : 4 ∣ Nat.card (fixSubfield σ) := by
  rw [P.card_fix]
  exact (Nat.pow_dvd_pow 2 hn : 2 ^ 2 ∣ 2 ^ n)

end Par

section OrbitFacts

theorem orbit_card_three : (TwistTag.D4.orbit KS11Lie4Proof.d4Outer).card = 3 := by decide

theorem orbit_perm_vals :
    (TwistTag.D4.perm ^ 0) (TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer) =
      CFSG.LieType.Steinberg.TwistedD4.nd 0 ∧
    (TwistTag.D4.perm ^ 1) (TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer) =
      CFSG.LieType.Steinberg.TwistedD4.nd 1 ∧
    (TwistTag.D4.perm ^ 2) (TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer) =
      CFSG.LieType.Steinberg.TwistedD4.nd 3 := by decide

end OrbitFacts

section Transfer

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem graphFixed_eq_map_twisted (P : D4Par n X σ) :
    graphFixedRootGroup TwistTag.D4 X σ.toRingHom =
      (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom).map
        (adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X).subtype := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) P.one_le
  exact (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two P.one_le X P.card
      σ.toRingHom P.frob).2.2.1.symm.trans
    (CFSG.LieType.Steinberg.TwistedD4.commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 P.card
      P.frob)

@[expose] noncomputable def eC (P : D4Par n X σ) :
    C0 σ ≃* CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom :=
  CFSG.RankThree.PartOne.SEITZ8.eGamma (graphFixed_eq_map_twisted P)

theorem coe_eC (P : D4Par n X σ) (x : C0 σ) :
    (((eC P x : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
      adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
        ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) = (x : ModGL TwistTag.D4.tag X) :=
  CFSG.RankThree.PartOne.SEITZ8.coe_eGamma (graphFixed_eq_map_twisted P) x

@[expose] noncomputable def iotaA (P : D4Par n X σ) : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
  (eC P).symm.toMonoidHom.comp
    (CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom)

@[expose] noncomputable def etaB (P : D4Par n X σ) :
    Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) →* C0 σ :=
  (eC P).symm.toMonoidHom.comp
    (CFSG.RankThree.PartOne.SEITZ7.psiB σ.toRingHom P.sigma_cube_hom)

theorem iotaA_injective (P : D4Par n X σ) : Function.Injective (iotaA P) :=
  (eC P).symm.injective.comp
    (CFSG.LieType.Steinberg.TwistedD4.slShort_injective (σ := σ.toRingHom)
      P.sigma_cube_hom)

theorem etaB_injective (P : D4Par n X σ) : Function.Injective (etaB P) :=
  (eC P).symm.injective.comp
    (CFSG.RankThree.PartOne.SEITZ7.psiB_injective σ.toRingHom P.sigma_cube_hom)

open CFSG.RankThree.PartOne.SEITZ7 in
theorem xd_simple_unit (i : Fin CFSG.LieType.Steinberg.TwistedD4.d4.rank) {p : ℕ}
    (hp : CFSG.LieType.Steinberg.TwistedD4.d4Root p = Pi.single i 1) (c : X) :
    ((xd p c : adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
      ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) =
        xUnit CFSG.LieType.Steinberg.TwistedD4.d4 X i c := by
  apply Units.ext
  exact CFSG.RankThree.PartOne.SEITZ8.coe_xe_simple_end i hp c

open CFSG.RankThree.PartOne.SEITZ7 in
theorem xd_neg_simple_unit (i : Fin CFSG.LieType.Steinberg.TwistedD4.d4.rank) {p : ℕ}
    (hp : CFSG.LieType.Steinberg.TwistedD4.d4Root p = -Pi.single i 1) (c : X) :
    ((xd p c : adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
      ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) =
        yUnit CFSG.LieType.Steinberg.TwistedD4.d4 X i c := by
  apply Units.ext
  exact CFSG.RankThree.PartOne.SEITZ8.coe_xe_neg_end i hp c

@[expose] noncomputable def orbitIncl (P : D4Par n X σ) :
    X →+* orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer :=
  (RingHom.id X).codRestrict _ (fun c => KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c)

theorem map_orbitIncl_surjective (P : D4Par n X σ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (orbitIncl P) :
      Matrix.SpecialLinearGroup (Fin 2) X →*
        Matrix.SpecialLinearGroup (Fin 2) (orbitField TwistTag.D4 X σ.toRingHom
          KS11Lie4Proof.d4Outer)) := by
  intro g'
  let v : orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer →+* X := Subfield.subtype _
  have hdet : (v.mapMatrix g'.1).det = 1 := by
    rw [← RingHom.map_det, g'.2, map_one]
  refine ⟨⟨v.mapMatrix g'.1, hdet⟩, ?_⟩
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  show orbitIncl P ((g'.1 i j).1) = g'.1 i j
  exact Subtype.ext rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_upper_eq_orbit (P : D4Par n X σ) (c : X) :
    (((slShort σ.toRingHom P.sigma_cube_hom (CFSG.LieType.Steinberg.sl2Upper c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (uSL (⟨c, KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c⟩ :
        orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer)) := by
  haveI := P.charP
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (slShort_upper_xA σ.toRingHom P.sigma_cube_hom c)
  refine h1.trans ?_
  rw [orbitRankOneHom_uSL, coe_orbitX]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [e0, e1, e2]
  simp only [xA, Subgroup.coe_mul]
  rw [xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_0,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_1,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_lower_eq_orbit (P : D4Par n X σ) (c : X) :
    (((slShort σ.toRingHom P.sigma_cube_hom (CFSG.LieType.Steinberg.sl2Lower c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (vSL (⟨c, KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c⟩ :
        orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer)) := by
  haveI := P.charP
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (slShort_lower_xAm σ.toRingHom P.sigma_cube_hom c)
  refine h1.trans ?_
  rw [orbitRankOneHom_vSL, coe_orbitY]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [e0, e1, e2]
  simp only [xAm, Subgroup.coe_mul]
  rw [xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_0,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_1,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_eq_orbit (P : D4Par n X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    (((slShort σ.toRingHom P.sigma_cube_hom g : twistedGroup σ.toRingHom) :
      adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (Matrix.SpecialLinearGroup.map (orbitIncl P) g) := by
  let Φ₂ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL d4 X :=
    (adjointGroup d4 X).subtype.comp ((twistedGroup σ.toRingHom).subtype.comp
      (slShort σ.toRingHom P.sigma_cube_hom))
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL TwistTag.D4.tag X :=
    (orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer).comp
      (Matrix.SpecialLinearGroup.map (orbitIncl P))
  have hgen : Set.EqOn Φ₂ Φ₁ (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have h := slShort_upper_eq_orbit P c
      have e : Matrix.SpecialLinearGroup.map (orbitIncl P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c) = uSL (orbitIncl P c) :=
        map_uSL (f := orbitIncl P) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (orbitIncl P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c))
      rw [e]
      exact h
    · have h := slShort_lower_eq_orbit P c
      have e : Matrix.SpecialLinearGroup.map (orbitIncl P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c) = vSL (orbitIncl P c) :=
        map_vSL (f := orbitIncl P) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (orbitIncl P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c))
      rw [e]
      exact h
  exact MonoidHom.eqOn_closure hgen
    (by rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)]
        exact Set.mem_univ _)

theorem iotaA_range (P : D4Par n X σ) : (iotaA P).range = Asub σ := by
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) X,
      ((iotaA P g : C0 σ) : ModGL TwistTag.D4.tag X) =
        orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
          (Matrix.SpecialLinearGroup.map (orbitIncl P) g) := by
    intro g
    have h1 := coe_eC P (iotaA P g)
    have h2 : eC P (iotaA P g) =
        CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom g :=
      (eC P).apply_symm_apply _
    rw [h2] at h1
    rw [← h1]
    exact slShort_eq_orbit P g
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact Subgroup.mem_comap.mpr ⟨Matrix.SpecialLinearGroup.map (orbitIncl P) g, (key g).symm⟩
  · intro hx
    obtain ⟨g', hg'⟩ := Subgroup.mem_comap.mp hx
    obtain ⟨g, rfl⟩ := map_orbitIncl_surjective P g'
    refine ⟨g, Subtype.ext ?_⟩
    rw [key g]
    exact hg'

theorem iotaA_etaB_commute (P : D4Par n X σ) (M : Matrix.SpecialLinearGroup (Fin 2) X)
    (N : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :
    iotaA P M * etaB P N = etaB P N * iotaA P M := by
  haveI := P.charP
  have h := (CFSG.RankThree.PartOne.SEITZ7.slShort_commute_psi σ.toRingHom
    P.sigma_cube_hom M N).eq
  apply (eC P).injective
  simp only [iotaA, etaB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
    MulEquiv.apply_symm_apply]
  exact h

open CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof in
theorem card_centralizer_Asub_le (P : D4Par n X σ) :
    Nat.card (Subgroup.centralizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ))) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) := by
  haveI := P.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := AlgebraicClosure X
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have hcomm : ∀ c, algebraMap X L (σ c) = Fr (algebraMap X L c) := fun c => by
    rw [P.frob, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  let k := RingHom.eqLocusField Fr (RingHom.id L)
  have hZex : ∀ z : Subgroup.centralizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ)),
      ∃ Zk : Matrix.SpecialLinearGroup (Fin 2) k,
        thetaHom L (Matrix.SpecialLinearGroup.map k.subtype Zk) = triEmb X σ L (z : C0 σ) := by
    intro z
    obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer P.one_le (by norm_num : (2 : ℕ) ≠ 3)
      P.card P.frob L hFr z.2
    have hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z := thetaHom_injective (by
      rw [← twistHom_thetaHom Fr hfixθ, hZ]
      exact triEmb_fixed Fr (RingHom.ext hcomm) z)
    obtain ⟨Zk, hZk⟩ := exists_sl2_eqLocus Fr Z hFZ
    exact ⟨Zk, by rw [hZk, hZ]⟩
  choose g hg using hZex
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply triEmb_injective (L := L)
    rw [← hg a, ← hg b, hab]
  have hk : Nat.card k = 2 ^ n := natCard_eqLocusField_frob Nat.prime_two P.one_le hFr
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h1 := Nat.card_le_card_of_injective g hinj
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk] at h1
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, P.card_fix]
  exact h1

theorem finite_C0 : Finite (C0 σ) :=
  haveI : Finite (ModGL TwistTag.D4.tag X) := finite_modGL
  Subtype.finite

theorem Asub_Bsub_commute {a b : C0 σ} (ha : a ∈ Asub σ) (hb : b ∈ Bsub σ) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp hb a ha

theorem etaB_range_le (P : D4Par n X σ) : (etaB P).range ≤ Bsub σ := by
  rintro _ ⟨N, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  rw [← iotaA_range P] at ha
  obtain ⟨M, rfl⟩ := ha
  exact iotaA_etaB_commute P M N

theorem Bsub_eq_range_etaB (P : D4Par n X σ) : Bsub σ = (etaB P).range := by
  haveI : Finite (C0 σ) := finite_C0
  symm
  refine Subgroup.eq_of_le_of_card_ge (etaB_range_le P) ?_
  have h1 := card_centralizer_Asub_le P
  have h2 : Nat.card (etaB P).range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :=
    (Nat.card_congr (MonoidHom.ofInjective (etaB_injective P)).toEquiv).symm
  rw [h2]
  exact h1

@[expose] noncomputable def asubEquiv (P : D4Par n X σ) : Matrix.SpecialLinearGroup (Fin 2) X ≃* Asub σ :=
  (MonoidHom.ofInjective (iotaA_injective P)).trans (MulEquiv.subgroupCongr (iotaA_range P))

@[expose] noncomputable def bsubEquiv (P : D4Par n X σ) :
    Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) ≃* Bsub σ :=
  (MonoidHom.ofInjective (etaB_injective P)).trans
    (MulEquiv.subgroupCongr (Bsub_eq_range_etaB P).symm)

theorem Asub_inf_Bsub (P : D4Par n X σ) : Asub σ ⊓ Bsub σ = ⊥ := by
  haveI := P.charP
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨hgA, hgB⟩ := hg
  rw [← iotaA_range P] at hgA
  obtain ⟨M, rfl⟩ := hgA
  have hc : ∀ M' : Matrix.SpecialLinearGroup (Fin 2) X, M' * M = M * M' := fun M' =>
    iotaA_injective P (by
      rw [map_mul, map_mul]
      exact Asub_Bsub_commute (iotaA_range P ▸ ⟨M', rfl⟩) hgB)
  have hM : M ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) X) :=
    Subgroup.mem_center_iff.mpr fun M' => hc M'
  rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.mem_bot] at hM
  rw [hM, map_one]
  exact Subgroup.one_mem _

theorem isSimple_nonab_C0 (P : D4Par n X σ) :
    IsSimpleGroup (C0 σ) ∧ ∃ x y : C0 σ, x * y ≠ y * x := by
  haveI := P.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := AlgebraicClosure X
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  obtain ⟨-, -, -, hsimple, hnonab⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group 2 n Nat.prime_two P.one_le X
      P.card L 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact P.frob c)
      (iterateFrobenius L 2 n) (fun c => iterateFrobenius_def 2 n c)
  exact ⟨hsimple, hnonab⟩

theorem center_C0_eq_bot (P : D4Par n X σ) : Subgroup.center (C0 σ) = ⊥ := by
  obtain ⟨hs, x, y, hxy⟩ := isSimple_nonab_C0 P
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (C0 σ)) with h | h
  · exact h
  · exfalso
    apply hxy
    have hx : x ∈ Subgroup.center (C0 σ) := h ▸ Subgroup.mem_top x
    exact ((Subgroup.mem_center_iff.mp hx) y).symm

theorem conj_ne_one (P : D4Par n X σ) {g : C0 σ} (hg : g ≠ 1) :
    (MulAut.conj g : MulAut (C0 σ)) ≠ 1 := by
  intro h1
  apply hg
  have hmem : g ∈ Subgroup.center (C0 σ) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut (C0 σ) => φ h) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [center_C0_eq_bot P, Subgroup.mem_bot] at hmem
  exact hmem

theorem Asub_ne_bot (P : D4Par n X σ) : Asub σ ≠ ⊥ := by
  intro h
  have h1 : iotaA P (CFSG.LieType.Steinberg.sl2Upper (1 : X)) = 1 := by
    have : iotaA P (CFSG.LieType.Steinberg.sl2Upper (1 : X)) ∈ Asub σ := by
      rw [← iotaA_range P]; exact ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have h2 := iotaA_injective P (h1.trans (map_one (iotaA P)).symm)
  have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) X => (M : Matrix (Fin 2) (Fin 2) X) 0 1) h2
  simp [CFSG.LieType.Steinberg.sl2Upper] at h3

theorem Bsub_ne_bot (P : D4Par n X σ) : Bsub σ ≠ ⊥ := by
  intro h
  have h1 : etaB P (CFSG.LieType.Steinberg.sl2Upper (1 : fixSubfield σ)) = 1 := by
    have : etaB P (CFSG.LieType.Steinberg.sl2Upper (1 : fixSubfield σ)) ∈ Bsub σ := by
      rw [Bsub_eq_range_etaB P]; exact ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have h2 := etaB_injective P (h1.trans (map_one (etaB P)).symm)
  have h3 := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) =>
      (M : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) 0 1) h2
  simp [CFSG.LieType.Steinberg.sl2Upper] at h3

theorem Asub_sup_Bsub_ne_top (P : D4Par n X σ) : Asub σ ⊔ Bsub σ ≠ ⊤ := by
  obtain ⟨hs, -⟩ := isSimple_nonab_C0 P
  intro htop
  have hnorm : (Asub σ).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr ?_
    rw [← htop]
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc : ∀ h ∈ Asub σ, h * b = b * h := fun h hh => Asub_Bsub_commute hh hb
    constructor
    · intro hy
      have : b * y * b⁻¹ = y := by rw [← hc y hy, mul_inv_cancel_right]
      rw [this]
      exact hy
    · intro hw
      have h1 := hc _ hw
      have h2 : y = b * y * b⁻¹ := by
        have h3 : b * y = b * (b * y * b⁻¹) := by
          calc b * y = (b * y * b⁻¹) * b := by group
            _ = b * (b * y * b⁻¹) := h1
        exact mul_left_cancel h3
      rw [h2]
      exact hw
  haveI := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (Asub σ) with h | h
  · exact Asub_ne_bot P h
  · apply Bsub_ne_bot P
    rw [eq_bot_iff]
    intro b hb
    have : b ∈ Subgroup.center (C0 σ) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Asub_Bsub_commute (h ▸ Subgroup.mem_top g) hb
    rw [center_C0_eq_bot P] at this
    exact this

end Transfer

end CFSG.RankThree.PartTwo.Sec19
