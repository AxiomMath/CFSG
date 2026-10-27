module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Main
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Sc
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Cent
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Zs

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Two

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
open scoped MatrixGroups
open CFSG.RankThree.Classical2 (unitarySet)


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] {σ : K ≃+* K}

theorem mem_commutator_centS_of_pow_three (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c ∈ ⁅centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ := by
  have hℓp : ℓ.Prime := hℓ.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓp (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set k := RingHom.eqLocusField (iterateFrobenius L ℓ f) (RingHom.id L) with hk
  have hkcard : Nat.card k = ℓ ^ f := natCard_eqLocusField_frob hℓp hf hFr
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; exact pow_ne_zero _ hℓp.ne_zero)
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_three).1 h')
  have h3k : (3 : k) ≠ 0 := fun h => h3L (by rw [← map_ofNat k.subtype 3, h, map_zero])
  have hmap := Item1118Res3ProofU3Cent.map_triEmb_centS L hf hℓ3 hK hσ
    (iterateFrobenius L ℓ f) hFr
  set φ : SpecialLinearGroup (Fin 2) k →* ModGL TwistTag.D4.tag L :=
    (thetaHom L).comp (Matrix.SpecialLinearGroup.map k.subtype) with hφ
  have hφinj : Function.Injective φ := fun X Y h =>
    sl2Map_injective k.subtype (thetaHom_injective h)
  obtain ⟨Z, hZ⟩ : triEmb K σ L c ∈ φ.range := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hc
  have hZ3 : Z ^ 3 = 1 := hφinj (by rw [map_pow, hZ, ← map_pow, hc3, map_one, map_one])
  have hZ1 : Z ≠ 1 := fun h => hc1 (triEmb_injective (L := L) (by rw [← hZ, h, map_one, map_one]))
  obtain ⟨N, hN⟩ := CFSG.RankThree.PartTwo.Sec4.Res424Seven.exists_conj_eq_inv_sl2 h3k hZ3 hZ1
  obtain ⟨x, hxC, hxN⟩ : φ N ∈ Subgroup.map (triEmb K σ L) (centralizer
      ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rw [hmap]
    exact ⟨N, rfl⟩
  have hZinv : Z⁻¹ = Z ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hZ3])
  have hZ4 : Z⁻¹ * Z⁻¹ = Z := by
    rw [hZinv, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hZ3, one_mul]
  have hφc : φ (N * Z * N⁻¹ * Z⁻¹) = φ Z := by rw [hN, hZ4]
  have hcomm : x * c * x⁻¹ * c⁻¹ = c := by
    apply triEmb_injective (L := L)
    simpa only [map_mul, map_inv, hxN, ← hZ] using hφc
  have h1 := Subgroup.commutator_mem_commutator hxC hc
  rwa [commutatorElement_def, hcomm] at h1


theorem d4PairingTransTwo_of_mod_two
    (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) (hq3 : q % 3 = 2)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hc : c ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (d : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hd : d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, t * d * t⁻¹ = d ∧ t * c * t⁻¹ = c * d := by
  classical
  set S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hS
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.exists_prime_pow_of_card_eq_cube hK
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    rw [h0] at hq3
    exact absurd hq3 (by norm_num)
  have hq1 : ℓ ^ f % 3 = 2 := hq3
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun x => ?_
    have := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ x
    simpa [pow_succ] using this
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f * 3) (by omega) (by rw [hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨c₀, R, hyR, hRC, hcommR, U, hU, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary_two hℓ hf hℓ3 hq1 hK hσ
      hd hd3 hd1
  have hcS := mem_commutator_centS_of_pow_three hf hℓ3 hK hσ hc hc3 hc1
  have hCS : Subgroup.centralizer (S : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
      Subgroup.centralizer ({d} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact Subgroup.mem_centralizer_iff.1 hx d hd
  have hcd := Subgroup.commutator_mono hCS hCS hcS
  have hcR : c₀ * c * c₀⁻¹ ∈ R :=
    Item1118Res3ProofU3Main.conj_mem_of_comm hcommR hcd
  have hy : ∀ x : R, (⟨c₀ * d * c₀⁻¹, hyR⟩ : R) * x = x * ⟨c₀ * d * c₀⁻¹, hyR⟩ := fun x =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 (hRC x.2) (c₀ * d * c₀⁻¹) (Set.mem_singleton _))
  have hyc3 : (c₀ * d * c₀⁻¹) ^ 3 = 1 := by
    rw [Item1118Res3ProofU3Main.conj_pow_eq_conj, hd3, mul_one, mul_inv_cancel]
  have hy3 : (⟨c₀ * d * c₀⁻¹, hyR⟩ : R) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hyc3)
  have hy1 : (⟨c₀ * d * c₀⁻¹, hyR⟩ : R) ≠ 1 := fun h => hd1 (by
    have h' : c₀ * d * c₀⁻¹ = 1 := congrArg Subtype.val h
    calc d = c₀⁻¹ * (c₀ * d * c₀⁻¹) * c₀ := by group
      _ = 1 := by rw [h']; group)
  have hcc3 : (c₀ * c * c₀⁻¹) ^ 3 = 1 := by
    rw [Item1118Res3ProofU3Main.conj_pow_eq_conj, hc3, mul_one, mul_inv_cancel]
  have hcR3 : (⟨c₀ * c * c₀⁻¹, hcR⟩ : R) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hcc3)
  have hcR1 : (⟨c₀ * c * c₀⁻¹, hcR⟩ : R) ≠ 1 := fun h => hc1 (by
    have h' : c₀ * c * c₀⁻¹ = 1 := congrArg Subtype.val h
    calc c = c₀⁻¹ * (c₀ * c * c₀⁻¹) * c₀ := by group
      _ = 1 := by rw [h']; group)
  have hZ : ∀ X : R, X ∈ Subgroup.center R → ∃ μ : AlgebraicClosure K,
      (((e X : U) : GL (Fin 3) (AlgebraicClosure K)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) = Matrix.scalar (Fin 3) μ := by
    intro X hX
    refine scalar_of_commute_unitarySet hℓ3 hq1 (fun Y hY => ?_)
    have hYU : Y ∈ U := by
      have : Y ∈ (U : Set (GL (Fin 3) (AlgebraicClosure K))) := by rw [hU]; exact hY
      exact this
    obtain ⟨Z, hZ⟩ := e.surjective ⟨Y, hYU⟩
    have hXZ := Subgroup.mem_center_iff.1 hX Z
    have h1 := congrArg (fun r : R => (((e r : U) : GL (Fin 3) (AlgebraicClosure K)) :
      Matrix (Fin 3) (Fin 3) (AlgebraicClosure K))) hXZ.symm
    simp only [map_mul, Subgroup.coe_mul, Units.val_mul, hZ] at h1
    exact h1
  have hmain := Item1118Res3ProofU3Main.conj_or_powers_of_model hf hℓ3 hq1 hU e hZ hy hy3 hy1
    hcR3 hcR1
  rcases hmain with ⟨h, h1, h2⟩ | hpow
  · have h1' := congrArg Subtype.val h1
    have h2' := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1' h2'
    refine ⟨c₀⁻¹ * h.1 * c₀, ?_, ?_⟩
    · calc c₀⁻¹ * h.1 * c₀ * d * (c₀⁻¹ * h.1 * c₀)⁻¹
          = c₀⁻¹ * (h.1 * (c₀ * d * c₀⁻¹) * h.1⁻¹) * c₀ := by group
        _ = c₀⁻¹ * (c₀ * d * c₀⁻¹) * c₀ := by rw [h2']
        _ = d := by group
    · calc c₀⁻¹ * h.1 * c₀ * c * (c₀⁻¹ * h.1 * c₀)⁻¹
          = c₀⁻¹ * (h.1 * (c₀ * c * c₀⁻¹) * h.1⁻¹) * c₀ := by group
        _ = c₀⁻¹ * (c₀ * c * c₀⁻¹ * (c₀ * d * c₀⁻¹)) * c₀ := by rw [h1']
        _ = c * d := by group
  · exfalso
    have hcd' : c = d ∨ c = d ^ 2 := by
      rcases hpow with h | h
      · left
        have e1 : c₀ * c * c₀⁻¹ = c₀ * d * c₀⁻¹ := congrArg Subtype.val h
        calc c = c₀⁻¹ * (c₀ * c * c₀⁻¹) * c₀ := by group
          _ = c₀⁻¹ * (c₀ * d * c₀⁻¹) * c₀ := by rw [e1]
          _ = d := by group
      · right
        have e2 : c₀ * c * c₀⁻¹ = (c₀ * d * c₀⁻¹) ^ 2 := by
          have h' := congrArg Subtype.val h
          rw [Subgroup.coe_pow] at h'
          exact h'
        calc c = c₀⁻¹ * (c₀ * c * c₀⁻¹) * c₀ := by group
          _ = c₀⁻¹ * (c₀ * d * c₀⁻¹) ^ 2 * c₀ := by rw [e2]
          _ = d ^ 2 := by rw [Item1118Res3ProofU3Main.conj_pow_eq_conj]; group
    have hcS' : c ∈ S := by
      rcases hcd' with h | h
      · rw [h]; exact hd
      · rw [h]; exact pow_mem hd 2
    exact hc1 (Item1118Res3ProofU3Zs.d4ShortSL2_central_eq_one hσ3 hcS' hc hc3)

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Two

end
