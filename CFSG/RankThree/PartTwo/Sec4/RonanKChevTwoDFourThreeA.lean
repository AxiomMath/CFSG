module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourDefs
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSing

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup

theorem exists_threeA_model_odd
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq2 : 2 < ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ = R ∧
        IsQuasisimple R ∧ Odd (Nat.card (center R)) ∧
        Odd (R.relIndex (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))))
          := by
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
  obtain ⟨-, -, hcomm, -, -, hquasi, hcent, -, hidx, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.triality_three_six_singular_fixed_centralizers_gen hℓp hf K
      hK σ hσ L Fr hFr hε hdε g hgG hFg' Nat.prime_three (by decide) hℓ3 hq2 (tup ζ gT) ha hord vT
      hv x hx
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, _, hcomm, hquasi, ?_, hidx⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  ·
    rw [hcent]
    have h3 : (Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) : ℤ) ∣ 3 := Int.gcd_dvd_left ..
    have h3' : Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) ∣ 3 := by exact_mod_cast h3
    exact (by decide : Odd 3).of_dvd_nat h3'

theorem dFourThreeAKill_holds :
    DFourThreeAKill := by
  intro K _ _ f σ hf hK hσ z hzS hz3 hz1 hz
  have hf1 : 1 ≤ f := by omega
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hf)
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
  obtain ⟨x, k, hk, hxk, R, hR, hRq, hZ, hidx⟩ :=
    exists_threeA_model_odd hf1 (by decide) hq2 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf1 hK hσ (isPointIrreducible_gA hζ) hk' hk hzk
    hxk
  have hx : PullDatum (MulAut.conj x) := by
    have h := hz.conj_inner c
    rwa [hc] at h
  set C := centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hCdef
  have hCC : ⁅C, C⁆ ≤ C := commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hRC : R ≤ C := hR ▸ hCC
  refine hx.false_of_quasisimple_relIndex C (fun y => ?_) R hRC (fun a ha s hs => ?_) hRq hZ hidx
  · rw [hCdef, mem_centralizer_singleton_iff, conj_apply_eq_iff]
    exact eq_comm
  · rw [← hR] at hs ⊢
    have h1 := commutator_mem_commutator ha (hCC hs)
    rw [commutatorElement_def] at h1
    convert mul_mem h1 hs using 1
    group

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
