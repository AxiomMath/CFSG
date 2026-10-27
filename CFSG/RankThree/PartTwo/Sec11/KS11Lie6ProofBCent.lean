module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofFix
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.LieType.AlgebraicGroups Subgroup
open scoped MatrixGroups Pointwise


theorem tup_gB_eq_mulSingle {L : Type} [Field L] (ω : Lˣ) : tup ω gB = Pi.mulSingle n2 ω := by
  have h0 : (0 : ZMod 3).val = 0 := rfl
  have h1 : (1 : ZMod 3).val = 1 := rfl
  funext j
  fin_cases j
  · show ω ^ (0 : ZMod 3).val = 1
    rw [h0, pow_zero]
  · show ω ^ (0 : ZMod 3).val = 1
    rw [h0, pow_zero]
  · show ω ^ (1 : ZMod 3).val = ω
    rw [h1, pow_one]
  · show ω ^ (0 : ZMod 3).val = 1
    rw [h0, pow_zero]

theorem torusGroup_le_normalizer_sigmaB (L : Type) [Field L] :
    torusGroup TwistTag.D4.tag L ≤
      normalizer (rootSpan TwistTag.D4.tag L sigmaB : Set (ModGL TwistTag.D4.tag L)) :=
  CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan fun _ hα => isRoot_of_mem_sigmaB hα

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {σ : K ≃+* K}

theorem exists_thetaHom_of_mem_centralizer (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosed L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ Z : SL2 L, thetaHom L Z = triEmb K σ L z := by
  have h := triEmb_mem_thetaPair_of_mem_centralizer hf hℓ3 hK hσ L hFr hzS
  rw [← range_thetaHom] at h
  exact h

theorem threeBCent_commutator (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {x y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : x ∈ centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hy : y ∈ centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    x * y * x⁻¹ * y⁻¹ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨μ, hμ⟩ := exists_units_orderOf_nine L h3L
  have hζ : orderOf (μ ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hμ]; norm_num), hμ]
  obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hzS
  have hZ3 : Z ^ 3 = 1 := thetaHom_injective (by
    rw [map_pow, hZ, ← map_pow, hz3, map_one, map_one])
  have hZ1 : Z ≠ 1 := fun h => hz1 (triEmb_injective (L := L) (by rw [← hZ, h, map_one, map_one]))
  obtain ⟨P, m, hm, hPZ⟩ := exists_conj_HSL_of_pow_three hζ hZ3 hZ1
  have hω : orderOf ((μ ^ 3) ^ m) = 3 := by
    rcases hm with rfl | rfl
    · rw [pow_one, hζ]
    · rw [Nat.Coprime.orderOf_pow (by rw [hζ]; norm_num), hζ]
  set k := thetaHom L P with hk
  set d := rootDiagUnit TwistTag.D4.tag (tup ((μ ^ 3) ^ m) gB) with hd
  have hιz : triEmb K σ L z = k * d * k⁻¹ := by
    rw [← hZ, hPZ, map_mul, map_mul, map_inv, thetaHom_HSL, hd, tup_gB_eq_mulSingle]
  have hcent : ∀ w ∈ centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      k⁻¹ * triEmb K σ L w * k ∈ (torusGroup TwistTag.D4.tag L : Set (ModGL TwistTag.D4.tag L)) *
        (rootSpan TwistTag.D4.tag L sigmaB : Set (ModGL TwistTag.D4.tag L)) := by
    intro w hw
    rw [mem_centralizer_singleton_iff] at hw
    have hmem : k⁻¹ * triEmb K σ L w * k ∈ graphCentralizer TwistTag.D4.tag L d := by
      refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem (thetaHom_mem_adjointGroup P))
        (triEmb_mem_adjointGroup w)) (thetaHom_mem_adjointGroup P), ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hd' : d = k⁻¹ * triEmb K σ L z * k := by rw [hιz]; group
      rw [hd']
      calc k⁻¹ * triEmb K σ L w * k * (k⁻¹ * triEmb K σ L z * k) =
          k⁻¹ * triEmb K σ L (w * z) * k := by rw [map_mul]; group
        _ = k⁻¹ * triEmb K σ L (z * w) * k := by rw [hw]
        _ = k⁻¹ * triEmb K σ L z * k * (k⁻¹ * triEmb K σ L w * k) := by rw [map_mul]; group
    rw [hd, graphCentralizer_gB hω, ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_sigmaB L)] at hmem
    exact hmem
  have hc := commutator_mem_of_mem_mul (torusGroup_le_normalizer_sigmaB L)
    (fun a ha b hb => torusGroup_mul_comm ha hb) (hcent x hx) (hcent y hy)
  obtain ⟨X, hX⟩ := rootSpan_sigmaB_le hc
  have hkX : outerTriple L X * k = k * outerTriple L X := commute_outerTriple_thetaHom X P
  have hιc : triEmb K σ L (x * y * x⁻¹ * y⁻¹) = outerTriple L X := by
    have h1 : triEmb K σ L (x * y * x⁻¹ * y⁻¹) = k * (k⁻¹ * triEmb K σ L x * k *
        (k⁻¹ * triEmb K σ L y * k) * (k⁻¹ * triEmb K σ L x * k)⁻¹ *
          (k⁻¹ * triEmb K σ L y * k)⁻¹) * k⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [h1, ← hX, ← hkX]
    group
  exact mem_short_of_triEmb_eq_outerTriple (q := ℓ ^ f) hK hσ hFr hιc

theorem threeBCent_order (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hb : b ∈ centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hbS : b ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    b ^ ((ℓ ^ f) ^ 2 - 1) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hzS
  obtain ⟨Y, hY⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hbS
  have hZ3 : Z ^ 3 = 1 := thetaHom_injective (by
    rw [map_pow, hZ, ← map_pow, hz3, map_one, map_one])
  have hZ1 : Z ≠ 1 := fun h => hz1 (triEmb_injective (L := L) (by rw [← hZ, h, map_one, map_one]))
  have hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z := thetaHom_injective (by
    rw [← twistHom_thetaHom Fr hfixθ, hZ]
    exact triEmb_fixed Fr (RingHom.ext hcomm) z)
  have hFY : Matrix.SpecialLinearGroup.map Fr Y = Y := thetaHom_injective (by
    rw [← twistHom_thetaHom Fr hfixθ, hY]
    exact triEmb_fixed Fr (RingHom.ext hcomm) b)
  have hYZ : Y * Z = Z * Y := thetaHom_injective (by
    rw [map_mul, map_mul, hY, hZ, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 hb)])
  have hpow := pow_sq_sub_one_eq_one hℓ3 hFr hZ3 hZ1 hFZ hFY hYZ
  apply triEmb_injective (L := L)
  rw [map_pow, ← hY, ← map_pow, hpow, map_one, map_one]

theorem d4ThreeBCent_holds : KS11Lie4Proof.D4ThreeBCent := by
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
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  exact ⟨fun x hx y hy => threeBCent_commutator hf hℓ3 hK hσ L hFr hzS hz3 hz1 hx hy,
    fun b hb hbS => threeBCent_order hf hℓ3 hK hσ L hFr hzS hz3 hz1 hb hbS⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
