module

public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.Classical2 CFSG.RankThree.SL3RootPermuting
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Matrix Pointwise MatrixGroups commutatorElement

theorem threeSix_fix_unitary_iso {Ω : Type} [Field Ω] {K : Type} [Field K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Φ : SL(3, Ω) ≃* SL(3, Ω)) (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Ωˣ)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single (π j) (π i) ((b i j : Ω) * Fr t)) :
    ∃ U : Subgroup (GL (Fin 3) Ω), (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
      Nonempty (fixSubgroup Φ ≃* U) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ := sl3_root_permuting_frobenius_fixed_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ π Φ b
    fun i j hij t => by rw [hΦ, hFr]
  set hG := Matrix.SpecialLinearGroup.toGL H with hhG
  set U : Subgroup (GL (Fin 3) Ω) := ((fixSubgroup Φ).map Matrix.SpecialLinearGroup.toGL).map
    (MulAut.conj hG⁻¹).toMonoidHom with hU
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(3, Ω) →* GL (Fin 3) Ω) :=
    fun X Y h => Subtype.ext (congrArg Units.val h)
  let e : fixSubgroup Φ ≃* U :=
    ((fixSubgroup Φ).equivMapOfInjective _ hinj).trans
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj hG⁻¹).injective)
  refine ⟨U, ?_, ⟨e⟩⟩
  ext Y
  simp only [SetLike.mem_coe, hU, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    obtain ⟨Y', hY', hXY⟩ := (hH X).1 hX
    rw [hXY]
    simpa [hhG, mul_assoc] using hY'
  · intro hY
    have hdet : (Y : Matrix (Fin 3) (Fin 3) Ω).det = 1 := hY.2.1
    set Y₀ : SL(3, Ω) := ⟨Y, hdet⟩
    have hY₀ : Matrix.SpecialLinearGroup.toGL Y₀ = Y := Units.ext rfl
    refine ⟨_, ⟨H * Y₀ * H⁻¹, (hH _).2 ⟨Y, hY, ?_⟩, rfl⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hY₀]
    · rw [map_mul, map_mul, map_inv, hY₀, ← hhG]
      group



theorem threeSix_unitary_model_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
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
    threeSixSingularR Ω K σ Fr (-1) v g ≤
        centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
    (∀ y ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      ∀ z ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        y * z * y⁻¹ * z⁻¹ ∈ threeSixSingularR Ω K σ Fr (-1) v g) ∧
    ∃ U : Subgroup (GL (Fin 3) Ω), (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
      Nonempty (threeSixSingularR Ω K σ Fr (-1) v g ≃* U) := by
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
  obtain ⟨-, -, hQM, -, -, -, hMder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK a hord v
      hv.symm
  obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
  obtain ⟨U, hU, ⟨e⟩⟩ := threeSix_fix_unitary_iso hℓ hf hK hσ _ π b hFr hb
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
  set D := centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hDdef
  have hDD : ⁅D, D⁆ ≤ threeSixSingularR Ω K σ Fr (-1) v g := by
    rw [hR]
    intro y hy
    rw [Subgroup.mem_comap]
    have h1 : threeSixEmb' Ω K σ g y ∈ (⁅D, D⁆).map (threeSixEmb' Ω K σ g) :=
      Subgroup.mem_map_of_mem _ hy
    rw [Subgroup.map_commutator] at h1
    have h2 : D.map (threeSixEmb' Ω K σ g) ≤ toralCentralizer TwistTag.D4.tag Ω a := by
      rw [hD]
      exact Subgroup.map_comap_le _ _
    have h3 := Subgroup.commutator_mono h2 h2 h1
    change _ ∈ ⁅toralCentralizer Tag.D4 Ω a, toralCentralizer Tag.D4 Ω a⁆ at h3
    rw [hMder] at h3
    exact h3
  refine ⟨?_, fun y hy z hz => ?_, U, hU, ⟨eRF.trans e⟩⟩
  ·
    rw [hR, hD]
    exact Subgroup.comap_mono hQM
  · have h1 := hDD (Subgroup.commutator_mem_commutator hy hz)
    rwa [commutatorElement_def] at h1


theorem exists_threeA_model_unitary_two {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    [hℓ : Fact ℓ.Prime] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2)
    (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        R ≤ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
        (∀ y ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          ∀ z ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
            y * z * y⁻¹ * z⁻¹ ∈ R) ∧
        x ∈ R ∧
        ∃ U : Subgroup (GL (Fin 3) (AlgebraicClosure K)),
          (U : Set (GL (Fin 3) (AlgebraicClosure K))) = unitarySet (ℓ ^ f) 3 ∧
          Nonempty (R ≃* U) := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
    rw [← ZMod.natCast_mod, hq1]
    rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L (-1))
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L (-1) := hFg
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
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · obtain ⟨hRC, hcomm, U, hU, hne⟩ := threeSix_unitary_model_two hℓp hℓ3 hf K hK σ hσ L Fr
      hFr g hgG hFg' (tup ζ gT) ha hord vT hv x hx
    refine ⟨_, hRC, hcomm, ?_, U, hU, hne⟩
    have hrange := range_threeSixEmb hℓp hf hK hσ Fr hFr
    rw [threeSixSingularR_eq_comap hrange hgG hFg' vT, Subgroup.mem_comap,
      threeSixEmb'_apply, hx]
    have e1 : g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹) * g =
        rootDiagUnit TwistTag.D4.tag (tup ζ gT) := by group
    rw [e1]
    exact rootDiagUnit_tup_gT_mem_tsQv hζ


theorem d4_threeA_model_unitary_two
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      c * z * c⁻¹ ∈ R ∧
      R ≤ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      (∀ a ∈ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        ∀ b ∈ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          a * b * a⁻¹ * b⁻¹ ∈ R) ∧
      ∃ U : Subgroup (GL (Fin 3) (AlgebraicClosure K)),
        (U : Set (GL (Fin 3) (AlgebraicClosure K))) = unitarySet (ℓ ^ f) 3 ∧
        Nonempty (R ≃* U) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  obtain ⟨x, k, hk, hxk, R, hRC, hcomm, hxR, U, hU, hRU⟩ :=
    exists_threeA_model_unitary_two hf hℓ3 hq1 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  refine ⟨c, R, ?_, ?_, ?_, U, hU, hRU⟩
  · rw [hc]
    exact hxR
  · rw [hc]
    exact hRC
  · rw [hc]
    exact hcomm

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof

end
