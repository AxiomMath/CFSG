module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofShort
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofSing
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofModelA
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof Subgroup

theorem threeACent_transfer {G : Type*} [Group G] [Finite G] {x z c : G} (hcz : c * z * c⁻¹ = x)
    (h : Group.IsSolvable (centralizer ({x} : Set G)) ∨
      ∃ R : Subgroup G, ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ = R ∧
        CFSG.IsQuasisimple R ∧ Nat.card (center R) = 3) :
    Group.IsSolvable (centralizer ({z} : Set G)) ∨
      ∃ N : Subgroup G, N ≤ centralizer ({z} : Set G) ∧
        (∀ a ∈ centralizer ({z} : Set G), ∀ b ∈ centralizer ({z} : Set G),
          a * b * a⁻¹ * b⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧ ∃ y ∈ N, (∀ n ∈ N, y * n = n * y) ∧ y ≠ 1 ∧ y ^ 3 = 1 := by
  classical
  have hmem : ∀ a, a ∈ centralizer ({z} : Set G) ↔ c * a * c⁻¹ ∈ centralizer ({x} : Set G) := by
    intro a
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hcz]
    constructor
    · intro ha
      calc c * a * c⁻¹ * (c * z * c⁻¹) = c * (a * z) * c⁻¹ := by group
        _ = c * (z * a) * c⁻¹ := by rw [ha]
        _ = c * z * c⁻¹ * (c * a * c⁻¹) := by group
    · intro ha
      have h1 : c * (a * z) * c⁻¹ = c * (z * a) * c⁻¹ := by
        calc c * (a * z) * c⁻¹ = c * a * c⁻¹ * (c * z * c⁻¹) := by group
          _ = c * z * c⁻¹ * (c * a * c⁻¹) := ha
          _ = c * (z * a) * c⁻¹ := by group
      calc a * z = c⁻¹ * (c * (a * z) * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (z * a) * c⁻¹) * c := by rw [h1]
        _ = z * a := by group
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({x} : Set G) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hmem a).1 ha
    · intro hy
      refine ⟨c⁻¹ * y * c, (hmem _).2 ?_, ?_⟩
      · simpa [mul_assoc] using hy
      · simp [MulAut.conj_apply, mul_assoc]
  let e : centralizer ({z} : Set G) ≃* centralizer ({x} : Set G) :=
    ((centralizer ({z} : Set G)).equivMapOfInjective _ (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hmap)
  rcases h with hsol | ⟨R, hR, hRq, hZ⟩
  · left
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · right
    set N := R.map (MulAut.conj c⁻¹).toMonoidHom with hN
    have hRC : R ≤ centralizer ({x} : Set G) := by
      rw [← hR]
      exact commutator_le.2 fun a ha b hb =>
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hNmem : ∀ n, n ∈ N ↔ c * n * c⁻¹ ∈ R := by
      intro n
      rw [hN, Subgroup.mem_map]
      constructor
      · rintro ⟨r, hr, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hr
      · intro hn
        exact ⟨c * n * c⁻¹, hn, by simp [mul_assoc]⟩
    refine ⟨N, fun n hn => (hmem n).2 (hRC ((hNmem n).1 hn)), fun a ha b hb => ?_, ?_, ?_⟩
    · rw [hNmem]
      have h1 := commutator_mem_commutator ((hmem a).1 ha) ((hmem b).1 hb)
      rw [hR, commutatorElement_def] at h1
      convert h1 using 1
      group
    · let eN : R ≃* N := R.equivMapOfInjective _ (MulAut.conj c⁻¹).injective
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eN hRq
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : Finite (center R) := inferInstance
      obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := center R) 3 (by rw [hZ])
      have hr3 : r ^ 3 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
      have hr1 : r ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hr
        exact absurd hr (by decide)
      refine ⟨c⁻¹ * ((r : R) : G) * c, (hNmem _).2 (by simp [mul_assoc]),
        fun n hn => ?_, fun h1 => hr1 ?_, ?_⟩
      · have hrc := (mem_center_iff.1 r.2) ⟨c * n * c⁻¹, (hNmem n).1 hn⟩
        have hrc' : c * n * c⁻¹ * ((r : R) : G) = ((r : R) : G) * (c * n * c⁻¹) :=
          congrArg Subtype.val hrc
        calc c⁻¹ * ((r : R) : G) * c * n = c⁻¹ * (((r : R) : G) * (c * n * c⁻¹)) * c := by group
          _ = c⁻¹ * (c * n * c⁻¹ * ((r : R) : G)) * c := by rw [hrc']
          _ = n * (c⁻¹ * ((r : R) : G) * c) := by group
      · have h2 : ((r : R) : G) = 1 := by
          calc ((r : R) : G) = c * (c⁻¹ * ((r : R) : G) * c) * c⁻¹ := by group
            _ = 1 := by rw [h1]; group
        exact Subtype.ext (Subtype.ext h2)
      · have h2 : ((r : R) : G) ^ 3 = 1 := by
          have := congrArg (fun t : center R => ((t : R) : G)) hr3
          simpa using this
        rw [show c⁻¹ * ((r : R) : G) * c = c⁻¹ * ((r : R) : G) * c⁻¹⁻¹ by rw [inv_inv], conj_pow,
          h2]
        group

section Model


theorem exists_threeA_model {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      (Group.IsSolvable (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∨
        ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
            centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ = R ∧
          CFSG.IsQuasisimple R ∧ Nat.card (center R) = 3) := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hq2' : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓp.one_lt
  have hq3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
    have : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
    omega
  obtain ⟨ε, hε, hqε, hcase⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((ℓ ^ f : ℕ) : ZMod 3) = ε ∧
      ((ε = 1 ∨ 2 < ℓ ^ f) ∨ (ε = -1 ∧ ℓ ^ f = 2)) := by
    rcases hq3 with h | h
    · refine ⟨1, Or.inl rfl, ?_, Or.inl (Or.inl rfl)⟩
      rw [← ZMod.natCast_mod, h]
      rfl
    · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · rw [← ZMod.natCast_mod, h]
        rfl
      · by_cases hq2 : ℓ ^ f = 2
        · exact Or.inr ⟨rfl, hq2⟩
        · exact Or.inl (Or.inr (by omega))
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
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · rcases hcase with hq | ⟨rfl, hq2⟩
    · right
      obtain ⟨hcomm, hquasi, hcent⟩ := threeSix_singular_three hℓp hℓ3 hf K hK σ hσ L Fr hFr hε
        hq g hgG hFg' (tup ζ gT) ha hord vT hv x hx
      refine ⟨_, hcomm, hquasi, ?_⟩
      rw [hcent]
      have h3 : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε := by
        have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (((ℓ ^ f : ℕ) : ℤ) - ε) 3).1 (by
          rw [Int.cast_sub, Int.cast_natCast, hqε, sub_self])
        exact_mod_cast h
      have h := Int.gcd_eq_left (by norm_num : (0 : ℤ) ≤ 3) h3
      exact_mod_cast h
    · left
      exact threeSix_solvable_two hℓp hℓ3 hf hq2 K hK σ hσ L Fr hFr g hgG hFg' (tup ζ gT) ha
        hord vT hv x hx

end Model

theorem exists_units_orderOf_three (L : Type) [Field L] [IsAlgClosed L] (h3 : (3 : L) ≠ 0) :
    ∃ ζ : Lˣ, orderOf ζ = 3 := by
  have : NeZero ((3 : ℕ) : L) := ⟨by exact_mod_cast h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  refine ⟨(hζ.isUnit (by norm_num)).unit, ?_⟩
  have h : IsPrimitiveRoot ((hζ.isUnit (by norm_num)).unit : L) 3 := by
    rw [IsUnit.unit_spec]
    exact hζ
  exact (IsPrimitiveRoot.coe_units_iff.1 h).eq_orderOf.symm

theorem d4ThreeACent_holds :
    KS11Lie4Proof.D4ThreeACent := by
  intro K _ _ q σ hK hσ h3 z hzS hz3 hz1
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (dvd_pow_self 3 (by omega))
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
  obtain ⟨x, k, hk, hxk, hcent⟩ := exists_threeA_model hf hℓ3 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  exact threeACent_transfer hc hcent

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
