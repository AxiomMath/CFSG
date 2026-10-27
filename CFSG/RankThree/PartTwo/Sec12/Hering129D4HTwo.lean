module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.RankThree.PartTwo.Sec11
open Subgroup


theorem exists_threeA_model_two {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) (hq2 : ℓ ^ f = 2) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      Group.IsSolvable
        (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
    rw [hq2]
    decide
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
  · exact threeSix_solvable_two hℓp hℓ3 hf hq2 K hK σ hσ L Fr hFr g hgG hFg' (tup ζ gT) ha
      hord vT hv x hx

theorem d4ThreeACent_two_solvable (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = 2 ^ 3) (hσ : ∀ c, σ c = c ^ 2)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Group.IsSolvable
      (centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  obtain ⟨ℓ, f, hℓ, hf, hq⟩ := exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq' : ℓ ^ f = 2 := hq.symm
  have hK' : Nat.card K = (ℓ ^ f) ^ 3 := by rw [hq']; exact hK
  have hσ' : ∀ c, σ c = c ^ (ℓ ^ f) := by rw [hq']; exact hσ
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have : (3 : ℕ) ∣ 2 := by
      rw [← hq']
      exact dvd_pow_self 3 (by omega)
    omega
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK', pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK' hσ' c
    simpa [pow_succ] using this
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  obtain ⟨x, k, hk, hxk, hsol⟩ := exists_threeA_model_two hf hℓ3 hK' hσ' hζ hq'
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK' hσ' (isPointIrreducible_gA hζ) hk' hk hzk hxk
  haveI := hsol
  have hmap : (centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
      (MulAut.conj c).toMonoidHom = centralizer ({x} : Set _) := by
    rw [← hc]
    exact (Hering129L.centralizer_conj_eq_map c z).symm
  let e : centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    ((centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).equivMapOfInjective
      _ (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem twoThreeAExcl_holds : TwoThreeAExcl := by
  intro X _ _ σ P
  apply threeAExcl_of_solvable
  intro a haA ha3
  have ha31 : a ^ 3 = 1 := by
    rw [← ha3]
    exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha3
    omega
  exact d4ThreeACent_two_solvable X σ (by simpa using P.card) (fun c => by simpa using P.frob c)
    haA ha31 ha1

theorem gap129HessD4_of_KF (hKF : KF_D4_HESS) : Gap129HessD4 :=
  gap129HessD4_of hKF twoThreeAExcl_holds

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
