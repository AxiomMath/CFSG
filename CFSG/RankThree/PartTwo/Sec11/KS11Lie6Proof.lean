module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofFrob
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjLang
public import CFSG.RankThree.PartOne.KGD.D4Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof


theorem exists_conj_of_triEmb_conj {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [CharP (AlgebraicClosure K) ℓ] {d : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hirr : IsPointIrreducible (AlgebraicClosure K)
      (transportPoints (modGLPoint TwistTag.D4.tag (AlgebraicClosure K))
        (graphCentralizer TwistTag.D4.tag (AlgebraicClosure K) d)))
    {z s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    {x k : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hx : x ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hk : k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hzx : triEmb K σ (AlgebraicClosure K) z = x * d * x⁻¹)
    (hsk : triEmb K σ (AlgebraicClosure K) s = k * d * k⁻¹) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * z * g⁻¹ = s := by
  have hℓp : ℓ.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    change algebraMap K L (σ c) = Fr (algebraMap K L c)
    rw [hσ, hFr, map_pow]
  have hQG : ∀ g ∈ adjointGroup TwistTag.D4.tag L,
      frobTwistGL TwistTag.D4.tag L ℓ f (diagramMap TwistTag.D4 L) g ∈
        adjointGroup TwistTag.D4.tag L :=
    fun g hg => twistHom_mem_adjointGroup TwistTag.D4 L Fr hg
  have hFs : frobTwistGL TwistTag.D4.tag L ℓ f (diagramMap TwistTag.D4 L)
      (triEmb K σ L s) = triEmb K σ L s := triEmb_fixed Fr hcomm s
  have hFz : frobTwistGL TwistTag.D4.tag L ℓ f (diagramMap TwistTag.D4 L)
      (triEmb K σ L z) = triEmb K σ L z := triEmb_fixed Fr hcomm z
  have hxs : k * x⁻¹ * triEmb K σ L z * (k * x⁻¹)⁻¹ = triEmb K σ L s := by
    rw [hzx, hsk]
    group
  obtain ⟨y, hy, hFy, hyz⟩ := exists_fixed_conj_of_lang ℓ hf (diagramMap TwistTag.D4 L) hQG hirr
    hk hsk hFs hFz (mul_mem hk (inv_mem hx)) hxs
  have hyr : y ∈ (triEmb K σ L).range := by
    rw [triEmb_range hℓp hf hK hσ Fr hFr]
    exact Subgroup.mem_inf.2 ⟨hy, hFy⟩
  obtain ⟨g, rfl⟩ := hyr
  refine ⟨g, triEmb_injective (L := L) ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hyz

theorem d4ThreeConj_holds : KS11Lie4Proof.D4ThreeConj := by
  intro K _ _ q σ hK hσ h3 z hz3 hz1
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (dvd_pow_self 3 (by omega))
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hz3' : (z : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
  have hz1' : (z : ModGL TwistTag.D4.tag K) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨ζ, x, hζ, hx, hcase⟩ := exists_conj_dA_or_dB hf hℓ3 hK hσ L (iterateFrobenius L ℓ f)
    (fun c => iterateFrobenius_def ℓ f c) z.2 hz3' hz1'
  rcases hcase with hA | hB
  ·
    obtain ⟨k, hk, hkeq⟩ := exists_conj_d4S0 (algebraMap K L) σ hζ
    obtain ⟨g, hg⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ)
      (z := z) (s := ⟨d4S0 σ, d4S0_mem σ⟩) hx hk hA hkeq
    exact ⟨g, Or.inl (hg ▸ d4S0_mem_short σ)⟩
  ·
    obtain ⟨k, hk, hkeq⟩ := exists_conj_d4T0 (algebraMap K L) σ hζ
    obtain ⟨g, hg⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gB hζ)
      (z := z) (s := ⟨d4T0 σ, d4T0_mem σ⟩) hx hk hB hkeq
    exact ⟨g, Or.inr (hg ▸ d4T0_mem_centralizer σ)⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
