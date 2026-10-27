module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourAux
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSing
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.D4

section Generic

variable {G : Type*} [Group G]

theorem centralizer_conj_eq_map (g b : G) :
    Subgroup.centralizer ({g * b * g⁻¹} : Set G) =
      (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext k
  rw [Subgroup.mem_map]
  constructor
  · intro hk
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · exact (CFSG.RankThree.PartTwo.Sec19.mem_centralizer_conj_iff g b k).1 hk
    · show g * (g⁻¹ * k * g) * g⁻¹ = k
      group
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.RankThree.PartTwo.Sec19.mem_centralizer_conj_iff]
    show g⁻¹ * (g * y * g⁻¹) * g ∈ Subgroup.centralizer ({b} : Set G)
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
    exact hy

theorem derived_centralizer_conj (g b : G) :
    ⁅Subgroup.centralizer ({g * b * g⁻¹} : Set G), Subgroup.centralizer ({g * b * g⁻¹} : Set G)⁆ =
      (⁅Subgroup.centralizer ({b} : Set G), Subgroup.centralizer ({b} : Set G)⁆).map
        (MulAut.conj g).toMonoidHom := by
  rw [centralizer_conj_eq_map, Subgroup.map_commutator]

theorem layer_conj_nonempty (g b : G) :
    Nonempty (↥⁅Subgroup.centralizer ({b} : Set G), Subgroup.centralizer ({b} : Set G)⁆ ≃*
      ↥⁅Subgroup.centralizer ({g * b * g⁻¹} : Set G),
        Subgroup.centralizer ({g * b * g⁻¹} : Set G)⁆) :=
  ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (derived_centralizer_conj g b).symm)⟩

@[expose] def LayerOK (b : G) : Prop :=
  CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({b} : Set G), Subgroup.centralizer ({b} : Set G)⁆ ∧
    Nat.card ↥(Subgroup.center ↥⁅Subgroup.centralizer ({b} : Set G),
      Subgroup.centralizer ({b} : Set G)⁆) ∣ 3

theorem LayerOK.conj {b : G} (h : LayerOK b) (g : G) : LayerOK (g * b * g⁻¹) := by
  obtain ⟨e⟩ := layer_conj_nonempty g b
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1, ?_⟩
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact h.2

theorem LayerOK.hZ3 {b : G} (h : LayerOK b) :
    ∀ z ∈ Subgroup.center ↥⁅Subgroup.centralizer ({b} : Set G),
      Subgroup.centralizer ({b} : Set G)⁆, ∃ k : ℕ, z ^ 3 ^ k = 1 := by
  intro z hz
  refine ⟨1, ?_⟩
  have h1 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥⁅Subgroup.centralizer ({b} : Set G),
      Subgroup.centralizer ({b} : Set G)⁆)) ∣ 3 := (orderOf_dvd_natCard _).trans h.2
  have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
  have h3 := congrArg Subtype.val h2
  simpa using h3

end Generic

section ThreeA

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

theorem exists_threeA_model_card
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq2 : 2 < ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({x} : Set _),
        Subgroup.centralizer ({x} : Set _)⁆ ∧
      Nat.card ↥(Subgroup.center ↥⁅Subgroup.centralizer ({x} : Set _),
        Subgroup.centralizer ({x} : Set _)⁆) = 3 := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hq3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
    have : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
    omega
  obtain ⟨ε, hε, hqε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((ℓ ^ f : ℕ) : ZMod 3) = ε := by
    rcases hq3 with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L ε)
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L ε := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG hFg' ha
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
  obtain ⟨d, hdε⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    refine ⟨_, Int.toNat_of_nonneg ?_⟩
    have h0 : (0 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := Int.natCast_nonneg _
    rcases hε with rfl | rfl
    · positivity
    · nlinarith [sq_nonneg (((ℓ ^ f : ℕ) : ℤ) - 1)]
  obtain ⟨-, -, hcomm, -, -, hquasi, hcent, -, -, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.triality_three_six_singular_fixed_centralizers_gen hℓp hf K
      hK σ hσ L Fr hFr hε hdε g hgG hFg' Nat.prime_three (by decide) hℓ3 hq2 (tup ζ gT) ha hord vT
      hv x hx
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · rw [hcomm]
    exact hquasi
  · rw [hcomm, hcent]
    have h3 : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (((ℓ ^ f : ℕ) : ℤ) - ε) 3).1 (by
        rw [Int.cast_sub, Int.cast_natCast, hqε, sub_self])
      exact_mod_cast this
    have h1 : Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) ∣ 3 := by
      have := Int.gcd_dvd_left (a := 3) (b := ((ℓ ^ f : ℕ) : ℤ) - ε)
      exact_mod_cast this
    have h2 : 3 ∣ Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) := by
      exact_mod_cast Int.dvd_gcd (dvd_refl (3 : ℤ)) h3
    exact Nat.dvd_antisymm h1 h2

theorem threeA_layer_of_mem_short
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf2 : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set _),
        Subgroup.centralizer ({z} : Set _)⁆ ∧
      Nat.card ↥(Subgroup.center ↥⁅Subgroup.centralizer ({z} : Set _),
        Subgroup.centralizer ({z} : Set _)⁆) = 3 := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hf2)
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
  obtain ⟨x, k, hk, hxk, hq, hc⟩ := exists_threeA_model_card hf1 (by decide) hq2 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc'⟩ := exists_conj_of_triEmb_conj hf1 hK hσ (isPointIrreducible_gA hζ) hk' hk hzk
    hxk
  subst hc'
  obtain ⟨e⟩ := layer_conj_nonempty c z
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hc

theorem layerOK_of_classX
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf2 : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hb : CFSG.RankThree.PartTwo.Sec19.IsClassX σ b) : LayerOK b := by
  obtain ⟨hb3, hb1, g, hg⟩ := hb
  have hz3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3]; group
  have hz1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    simp only [e] at this
    simpa using this)
  obtain ⟨hq, hc⟩ := threeA_layer_of_mem_short hf2 hK hσ hg hz3 hz1
  have h := LayerOK.conj (⟨hq, by rw [hc]⟩ : LayerOK (g * b * g⁻¹)) g⁻¹
  have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
  rwa [e] at h

end ThreeA

section ClassY

open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_eq_Asub_of_mem_Bsub
    (P : D4Par n X σ) {z : C0 σ} (hz : z ∈ Bsub σ) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    ⁅Subgroup.centralizer ({z} : Set (C0 σ)), Subgroup.centralizer ({z} : Set (C0 σ))⁆ =
      Asub σ := by
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨hcomm, -⟩ := KS11Lie6Proof.d4ThreeBCent_holds X (2 ^ n) σ P.card P.frob h3 z hz hz3 hz1
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three σ n P.card P.frob
  have hK4 : 4 ≤ Nat.card X := four_le_card_of_cube n P.one_le P.card
  have hAC : (Asub σ : Subgroup (C0 σ)) ≤ Subgroup.centralizer ({z} : Set (C0 σ)) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute ha hz)
  haveI : Group.IsPerfect ↥(Asub σ) := (RonanKChevTwo.isQuasisimple_d4Short hσ3 hK4).1
  apply le_antisymm
  · exact Subgroup.commutator_le.2 fun x hx y hy => hcomm x hx y hy
  · calc (Asub σ : Subgroup (C0 σ)) = ⁅Asub σ, Asub σ⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ _ := Subgroup.commutator_mono hAC hAC

theorem layerOK_of_mem_Bsub
    (P : D4Par n X σ) {z : C0 σ} (hz : z ∈ Bsub σ) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : LayerOK z := by
  have hA := layer_eq_Asub_of_mem_Bsub P hz hz3 hz1
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three σ n P.card P.frob
  have hK4 : 4 ≤ Nat.card X := four_le_card_of_cube n P.one_le P.card
  have hq := RonanKChevTwo.isQuasisimple_d4Short hσ3 hK4
  have hc : Subgroup.center ↥(Asub σ) = ⊥ := by
    haveI := P.charP
    have h := Subgroup.map_center_eq (asubEquiv P)
    rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.map_bot] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact hq
  · rw [hA, hc]
    simp

theorem layerOK_of_order_three
    (P : D4Par n X σ) (hn : 2 ≤ n) {b : C0 σ} (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) : LayerOK b := by
  rcases three_conj_dichotomy σ n P.one_le P.card P.frob hb3 hb1 with hX | ⟨g, hg⟩
  · exact layerOK_of_classX (K := X) (f := n) hn P.card P.frob hX
  · have hz3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3]; group
    have hz1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
      have := congrArg (fun y => g⁻¹ * y * g) h
      have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      simp only [e] at this
      simpa using this)
    have h := LayerOK.conj (layerOK_of_mem_Bsub P hg hz3 hz1) g⁻¹
    have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
    rwa [e] at h

theorem center_C0_eq_bot
    (P : D4Par n X σ) : Subgroup.center (C0 σ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply conj_injective_C0 σ n P.one_le P.card P.frob
  rw [map_one]
  refine MulEquiv.ext fun y => ?_
  have h := Subgroup.mem_center_iff.mp hx y
  show x * y * x⁻¹ = y
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm

end ClassY

end CFSG.RankThree.PartTwo.Sec4.RonanK423.D4
