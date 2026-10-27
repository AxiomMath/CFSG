module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423Basic
public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4Aux
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFix

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.D4

section ThreeSixPow

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Matrix Subgroup
open scoped Matrix Pointwise MatrixGroups commutatorElement

theorem threeSix_pow_two
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq2 : ℓ ^ f = 2)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    ∀ y ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      y ^ 648 = 1 := by
  classical
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hstab := threeSix_stab hFr hε ha hv
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω ℓ]
    exact hℓ3
  obtain ⟨-, hMset, hQM, -, -, -, hMder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK a hord v
      hv.symm
  obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ π _ b
    fun i j hij t => by rw [hb, hFr]
  have hcard := CFSG.RankThree.PartOne.D4RC.rcl_card_fix_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ _ H hH
  rw [hq2] at hcard
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω := fun u hu =>
    (Subgroup.mem_inf.1 (hQM hu)).1
  have hR := threeSixSingularR_eq_comap hrange hgG hFg v
  have hD := CFSG.RankThree.Chevalley.centralizer_eq_comap hrange hgG hFg hx
  have hRmem : ∀ y, y ∈ threeSixSingularR Ω K σ Fr (-1) v g ↔
      threeSixEmb' Ω K σ g y ∈ tsQv Ω v := fun y => by
    rw [hR, Subgroup.mem_comap]
  have hfixι : ∀ y, threeSixFrob Ω Fr (-1) (threeSixEmb' Ω K σ g y) =
      threeSixEmb' Ω K σ g y :=
    fun y => ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  let eR : threeSixSingularR Ω K σ Fr (-1) v g ≃* threeSixRΩ Ω Fr (-1) v :=
    MulEquiv.ofBijective (((threeSixEmb' Ω K σ g).comp
      (threeSixSingularR Ω K σ Fr (-1) v g).subtype).codRestrict (threeSixRΩ Ω Fr (-1) v)
        fun y => Subgroup.mem_inf.2 ⟨(hRmem y).1 y.2, hfixι y⟩)
      ⟨fun y y' h => Subtype.ext (threeSixEmb'_injective g (congrArg Subtype.val h)), fun u => by
        obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg u).2
          ⟨hQG (Subgroup.mem_inf.1 u.2).1, (Subgroup.mem_inf.1 u.2).2⟩
        refine ⟨⟨y, (hRmem y).2 ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact (Subgroup.mem_inf.1 u.2).1⟩
  let eRF := eR.trans (threeSixRΩEquivFix Fr hFrs hε v hstab)
  have hRcard : Nat.card (threeSixSingularR Ω K σ Fr (-1) v g) = 216 := by
    rw [Nat.card_congr eRF.toEquiv, hcard]
    norm_num
  have hd : ((3 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * (ℓ ^ f : ℕ) + 1 := by
    rw [hq2]
    norm_num
  intro y hy
  have hpow : y ^ 3 ∈ threeSixSingularR Ω K σ Fr (-1) v g := by
    rw [hD, Subgroup.mem_comap] at hy
    rw [hRmem, map_pow]
    have hy' : threeSixEmb' Ω K σ g y ∈
        (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω v : Set (ModGL Tag.D4 Ω)) := by
      rw [← hMset]
      exact hy
    exact pow_mem_d4A2Qv_of_fixed Fr hFrs hFr hε v hstab hd hy' (hfixι y)
  have hfin : Finite (threeSixSingularR Ω K σ Fr (-1) v g) :=
    Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
  have h1 := pow_card_eq_one' (G := threeSixSingularR Ω K σ Fr (-1) v g)
    (x := (⟨y ^ 3, hpow⟩ : threeSixSingularR Ω K σ Fr (-1) v g))
  rw [hRcard] at h1
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_pow] at h2
  rw [show (648 : ℕ) = 3 * 216 by norm_num, pow_mul]
  exact h2

section Conj

open CFSG CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD

theorem pow_648_of_mem_short_two
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hq2 : 2 ^ f = 2) (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∀ y ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      y ^ 648 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := f * 3)
    (by omega) (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 2] at h'
    exact absurd h' (by decide)
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  have hζ3 := pow_three_of_orderOf hζ
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hqε : ((2 ^ f : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
    rw [hq2]
    decide
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := 2) hf L (threeSixN L (-1))
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L (-1) := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj Nat.prime_two hf hK hσ hFr hgG hFg' ha
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  have hxk : triEmb K σ L x = (g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹) *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          (g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹)⁻¹ := by
    change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  have hk : g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ ∈
        adjointGroup TwistTag.D4.tag L :=
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _))
  have hpow := threeSix_pow_two Nat.prime_two (by decide) hf hq2 K hK σ hσ L Fr hFr g hgG hFg'
    (tup ζ gT) ha hord vT hv x hx
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc'⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  intro y hy
  have hy' : c * y * c⁻¹ ∈ Subgroup.centralizer ({x} : Set _) := by
    rw [← hc']
    exact (CFSG.RankThree.PartTwo.Sec19.mem_centralizer_conj_iff c z _).2 (by
      have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      rw [e]
      exact hy)
  have h648 := hpow _ hy'
  rw [conj_pow] at h648
  exact conj_eq_one_iff.mp h648

end Conj

end ThreeSixPow

section ThetaTwo

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
  CFSG.RankThree.PartTwo.Sec4.RonanK423

section Generic

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_exp {b : G} {D : Subgroup G} (hbD : b ∈ D)
    (hDc : ∀ a ∈ D, ∀ c ∈ D, a * c = c * a)
    (hexp : ∀ y ∈ Subgroup.centralizer ({b} : Set G), y ^ 648 = 1)
    (hno : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → ¬ D ≤ Subgroup.normalizer (T : Set G)) :
    aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({b} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  have hΘC : Θ ≤ C := inSubgroup_theta_le C
  have h3 : ¬ 3 ∣ Nat.card Θ := not_three_dvd_card_inSubgroup_theta C
  have hΘ2 : IsPGroup 2 Θ := by
    intro y
    have h1 : orderOf y ∣ 648 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa using hexp (y : G) (hΘC y.2)))
    have h2 : orderOf y ∣ Nat.card Θ := orderOf_dvd_natCard y
    have h4 : Nat.Coprime (orderOf y) (3 ^ 4) := by
      refine Nat.Coprime.pow_right 4 ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h => h3 (h.trans h2)
    have h5 : orderOf y ∣ 2 ^ 3 :=
      h4.dvd_of_dvd_mul_right (show orderOf y ∣ 2 ^ 3 * 3 ^ 4 by simpa using h1)
    exact ⟨3, orderOf_dvd_iff_pow_eq_one.mp h5⟩
  have hΘbot : Θ = ⊥ := by
    by_contra hne
    refine hno Θ hΘ2 hne fun d hd => ?_
    have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hDc d hd b hbD)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => conj_mem_inSubgroup_theta' hdC hh
    · intro hh
      have := conj_mem_inSubgroup_theta' (inv_mem hdC) hh
      have e : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
      rwa [e] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hΘbot

theorem theta_centralizer_conj_eq_bot (g b : G)
    (h : aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({g * b * g⁻¹} : Set G)) = ⊥) :
    aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({b} : Set G)) = ⊥ := by
  let e : ↥(Subgroup.centralizer ({b} : Set G)) ≃*
      ↥(Subgroup.centralizer ({g * b * g⁻¹} : Set G)) :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (centralizer_conj_eq_map g b).symm)
  exact CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof.theta_eq_bot_of_mulEquiv e h

theorem closure_centralizers_of_planes {D : Subgroup G}
    (h : Subgroup.closure (CFSG.RankThree.PartOne.CTP.fixUnion
      (D.map (MulAut.conj : G →* MulAut G))) = ⊤) :
    (⊤ : Subgroup G) ≤ Subgroup.closure {x : G | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x} := by
  rw [← h]
  refine Subgroup.closure_mono ?_
  rintro x ⟨F, hFE, hF, hfix⟩
  obtain ⟨φ, hφF, hφ1⟩ : ∃ φ ∈ F, φ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hF (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  obtain ⟨d, hdD, rfl⟩ := hFE hφF
  refine ⟨d, hdD, fun h1 => hφ1 (by rw [h1, map_one]), ?_⟩
  have hx := hfix _ hφF
  exact Subgroup.mem_centralizer_singleton_iff.mp
    ((CFSG.RankThree.PartTwo.Sec19.fixed_conj_iff d x).1 hx)

end Generic

section Models

open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

variable {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem pow_648_of_classX_two
    (P : D4Par 1 X σ) {b : C0 σ} (hb : IsClassX σ b) :
    ∀ y ∈ Subgroup.centralizer ({b} : Set _), y ^ 648 = 1 := by
  obtain ⟨hb3, hb1, g, hg⟩ := hb
  have hz3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3]; group
  have hz1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    simp only [e] at this
    simpa using this)
  have h := pow_648_of_mem_short_two (K := X) (f := 1) le_rfl (by norm_num) P.card P.frob hg hz3
    hz1
  intro y hy
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer ({g * b * g⁻¹} : Set (C0 σ)) := by
    rw [mem_centralizer_conj_iff]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e]
    exact hy
  have h648 := h _ hy'
  rw [conj_pow] at h648
  exact conj_eq_one_iff.mp h648

theorem theta_eq_bot_of_mem_Bsub_two
    (P : D4Par 1 X σ) {z : C0 σ} (hz : z ∈ Bsub σ)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({z} : Set _)) = ⊥ := by
  haveI : Finite (C0 σ) := finite_C0
  have hL := layerOK_of_mem_Bsub P hz hz3 hz1
  have hcen := theta_central_of_derived z hL.1 hL.hZ3
  have h3 : ¬ 3 ∣ 2 ^ 1 := by decide
  obtain ⟨-, hord⟩ := KS11Lie6Proof.d4ThreeBCent_holds X (2 ^ 1) σ P.card P.frob h3 z hz hz3 hz1
  set C := Subgroup.centralizer ({z} : Set _) with hC
  have hAC : (Asub σ : Subgroup (C0 σ)) ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute ha hz)
  have hbot : inSubgroup (aschbacherSolvableCore 3) C = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hyC : y ∈ C := inSubgroup_theta_le C hy
    have hyA : y ∈ Subgroup.centralizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcen y hy a (hAC ha)).symm
    have hy3 : y ^ 3 = 1 := by
      have h := hord y hyC hyA
      have e : (2 ^ 1) ^ 2 - 1 = 3 := by norm_num
      rw [e] at h
      exact h
    have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have h2 : orderOf (⟨y, hy⟩ : ↥(inSubgroup (aschbacherSolvableCore 3) C)) ∣
        Nat.card (inSubgroup (aschbacherSolvableCore 3) C) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd h2 (Res423Two.not_three_dvd_card_inSubgroup_theta C)
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hbot

theorem alphaVanishes_C0_two
    (P : D4Par 1 X σ)
    (hgen : ∀ D : Subgroup (C0 σ), (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → (∀ x ∈ D, x ^ 3 = 1) →
      Nat.card D = 9 → (⊤ : Subgroup (C0 σ)) ≤
        Subgroup.closure {x : C0 σ | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x})
    {D : Subgroup (C0 σ)} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) : AlphaVanishes (C0 σ) D := by
  haveI := P.charP
  haveI : Finite (C0 σ) := finite_C0
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three σ 1 P.card P.frob
  refine alphaVanishes_of_core (center_C0_eq_bot P) hDc (fun b hb hb1 => ?_) (hgen D hDc hDexp hD9)
  have hno : ∀ T : Subgroup (C0 σ), IsPGroup 2 T → T ≠ ⊥ →
      ¬ D ≤ Subgroup.normalizer (T : Set (C0 σ)) :=
    fun T hT2 hT1 hDT => RonanKChevTwo.false_of_le_normalizer_of_odd (f := 1) odd_one P.card hσ3
      hDexp hD9.ge hT2 hT1 hDT
  rcases three_conj_dichotomy σ 1 le_rfl P.card P.frob (hDexp b hb) hb1 with hX | ⟨g, hg⟩
  · exact theta_eq_bot_of_exp hb hDc (pow_648_of_classX_two P hX) hno
  · have hz3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hDexp b hb]; group
    have hz1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
      have := congrArg (fun y => g⁻¹ * y * g) h
      have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      simp only [e] at this
      simpa using this)
    exact theta_centralizer_conj_eq_bot g b (theta_eq_bot_of_mem_Bsub_two P hg hz3 hz1)

end Models

end ThetaTwo

end CFSG.RankThree.PartTwo.Sec4.RonanK423.D4
