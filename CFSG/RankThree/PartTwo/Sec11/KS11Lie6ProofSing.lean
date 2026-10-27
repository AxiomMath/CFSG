module

public import CFSG.RankThree.PartOne.D4RC.RxOrder
public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularIso
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularTools

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 CFSG.RankThree.Chevalley Matrix Subgroup
open scoped Matrix Pointwise MatrixGroups commutatorElement

theorem threeSix_singular_three
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : ε = 1 ∨ 2 < ℓ ^ f)
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ =
        threeSixSingularR Ω K σ Fr ε v g ∧
    CFSG.IsQuasisimple (threeSixSingularR Ω K σ Fr ε v g) ∧
    Nat.card (center (threeSixSingularR Ω K σ Fr ε v g)) = Int.gcd 3 ((ℓ ^ f : ℕ) - ε) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have h1q : 1 ≤ ℓ ^ f := Nat.one_le_iff_ne_zero.2 hq0
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
  have hfix : CFSG.IsQuasisimple (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) ∧
      Nat.card (center (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab))) =
        Int.gcd 3 ((ℓ ^ f : ℕ) - ε) := by
    rcases hε with rfl | rfl
    · obtain ⟨π, b, hb⟩ := threeSix_phi_split Fr hFrs v hstab
      obtain ⟨-, hQ, hcard, -⟩ := threeSix_fix_split hℓ hf hK hσ hFr _ π b hb
      refine ⟨hQ, ?_⟩
      rw [hcard, ← Int.gcd_natCast_natCast, Nat.cast_sub h1q]
      rfl
    · have hq2 : 2 < ℓ ^ f := by
        rcases hq with h | h
        · exact absurd h (by decide)
        · exact h
      obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
      obtain ⟨-, hQ, -, hcard, -⟩ := threeSix_fix_unitary hℓ hf hK hσ hFr hq2 _ π b hb
      refine ⟨hQ, ?_⟩
      rw [hcard, ← Int.gcd_natCast_natCast, Nat.cast_add, sub_neg_eq_add]
      rfl
  obtain ⟨hQS, hZcard⟩ := hfix
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω := fun u hu =>
    (Subgroup.mem_inf.1 (hQM hu)).1
  have hrange' : (threeSixEmb' Ω K σ g).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (threeSixFrob Ω Fr ε).eqLocus (MonoidHom.id _) := by
    ext u
    exact mem_range_threeSixEmb' hrange hgG hFg u
  have hRΩ : tsQv Ω v ⊓ (threeSixEmb' Ω K σ g).range = threeSixRΩ Ω Fr ε v := by
    rw [hrange', ← inf_assoc, inf_eq_left.2 hQG]
    rfl
  have hR := threeSixSingularR_eq_comap hrange hgG hFg v
  have hD := CFSG.RankThree.Chevalley.centralizer_eq_comap hrange hgG hFg hx
  have hRmem : ∀ y, y ∈ threeSixSingularR Ω K σ Fr ε v g ↔
      threeSixEmb' Ω K σ g y ∈ tsQv Ω v := fun y => by
    rw [hR, Subgroup.mem_comap]
  have hfixι : ∀ y, threeSixFrob Ω Fr ε (threeSixEmb' Ω K σ g y) = threeSixEmb' Ω K σ g y :=
    fun y => ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  have hperf : ⁅threeSixRΩ Ω Fr ε v, threeSixRΩ Ω Fr ε v⁆ = threeSixRΩ Ω Fr ε v := by
    have hP := (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (threeSixRΩEquivFix Fr hFrs hε v hstab).symm hQS).1
    rw [Group.isPerfect_def] at hP
    rw [← Subgroup.map_subtype_commutator, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eR : threeSixSingularR Ω K σ Fr ε v g ≃* threeSixRΩ Ω Fr ε v :=
    MulEquiv.ofBijective (((threeSixEmb' Ω K σ g).comp
      (threeSixSingularR Ω K σ Fr ε v g).subtype).codRestrict (threeSixRΩ Ω Fr ε v)
        fun y => Subgroup.mem_inf.2 ⟨(hRmem y).1 y.2, hfixι y⟩)
      ⟨fun y y' h => Subtype.ext (threeSixEmb'_injective g (congrArg Subtype.val h)), fun u => by
        obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg u).2
          ⟨hQG (Subgroup.mem_inf.1 u.2).1, (Subgroup.mem_inf.1 u.2).2⟩
        refine ⟨⟨y, (hRmem y).2 ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact (Subgroup.mem_inf.1 u.2).1⟩
  let eRF := eR.trans (threeSixRΩEquivFix Fr hFrs hε v hstab)
  refine ⟨?_, CFSG.LocalCores.isQuasisimple_of_mulEquiv eRF.symm hQS, ?_⟩
  ·
    apply Subgroup.map_injective (threeSixEmb'_injective (K := K) (σ := σ) g)
    rw [Subgroup.map_commutator, hD, hR, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
      inf_comm _ (toralCentralizer TwistTag.D4.tag Ω a), inf_comm _ (tsQv Ω v)]
    exact commutator_inf_eq hQM hMder (by rw [hRΩ]; exact hperf)
  ·
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.centerCongr eRF).toEquiv

theorem threeSix_solvable_two
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
    Group.IsSolvable (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
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
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ π _ b
    fun i j hij t => by rw [hb, hFr]
  have hcard := CFSG.RankThree.PartOne.D4RC.rcl_card_fix_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ _ H hH
  rw [hq2] at hcard
  have hfixsol : Group.IsSolvable (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) := by
    have : Finite (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have : Fintype (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
      (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
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
  have hRsol : Group.IsSolvable (threeSixSingularR Ω K σ Fr (-1) v g) :=
    Group.isSolvable_of_isSolvable_injective (f := eRF.toMonoidHom) eRF.injective
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
  have hDsol : Group.IsSolvable
      (⁅D, D⁆ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDD)
      (Subgroup.inclusion_injective hDD)
  have hmap : (commutator D).map D.subtype = ⁅D, D⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let e : commutator D ≃* (⁅D, D⁆ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : Group.IsSolvable (commutator D) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_commutator_iff.1 this

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
