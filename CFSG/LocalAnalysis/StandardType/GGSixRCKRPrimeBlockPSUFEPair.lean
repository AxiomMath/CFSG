module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private lemma rckRPfu_transpose_map_antidiag {F : Type} [Field F] (σ : F →+* F) (n : ℕ) :
    Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) F).map σ) =
      Unitary.antidiag n := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h', map_one]
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h', map_zero]

private lemma rckRPfu_isometry {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {x : GL (Fin n) F}
    (hx : x ∈ Unitary.SU σ n) :
    Matrix.transpose ((x : Matrix (Fin n) (Fin n) F).map σ.toRingHom) * Unitary.antidiag n *
      (x : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n :=
  (Unitary.mem_SU.mp hx).2

theorem rckRP_flaggedModel_PSU_fieldExtPair
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S))
      (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e))
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    RCKRPFlaggedModel
      (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
      none J' := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1)).toRingHom ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
        2 (g + 1)).toRingHom c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hGh := rckRPfu_transpose_map_antidiag
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
    (F := GaloisField 2 (2 * (g + 1))) n
  obtain ⟨he₁, he₂⟩ := Geo.mul_formAdj_eq_zero_of_dualPair _ hσ hG hGh
    (fun s hs => hSU s hs) hS he hpair
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, eW, φ, hcard, hφ, hφc, hact,
      hcomm⟩ := exists_blockAction_dualPair_PSU hc hSU hS hodd hε he hdeg hpair
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 (2 * (g + 1))) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 (2 * (g + 1))) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 (2 * (g + 1))) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ 2 * (g + 1) *
      blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := by
    nlinarith
  refine rckRP_flaggedModel_of_slBlock (B := none) (fun _ b hb => by simp at hb) he.2.2.1 hJe
    hcard hq eW φ hφ hφc hact hcomm ?_
  intro R hRX hRc hfix hinv U₁ U₂ hU hfl
  exact glGeoFlag_none_of_dualPair _ hσ hG hGh he.2.1 he₁ he₂
    (fun x hx => rckRPfu_isometry (hRX x hx)) hRc hfix hinv hU hfl

theorem rckRP_modelBig_PSU_fieldExtPair
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S))
      (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e))
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    RCKRPModelBig J' := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1)).toRingHom ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
        2 (g + 1)).toRingHom c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hGh := rckRPfu_transpose_map_antidiag
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
    (F := GaloisField 2 (2 * (g + 1))) n
  obtain ⟨he₁, he₂⟩ := Geo.mul_formAdj_eq_zero_of_dualPair _ hσ hG hGh
    (fun s hs => hSU s hs) hS he hpair
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, eW, φ, hcard, hφ, hφc, hact,
      hcomm⟩ := exists_blockAction_dualPair_PSU hc hSU hS hodd hε he hdeg hpair
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 (2 * (g + 1))) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 (2 * (g + 1))) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 (2 * (g + 1))) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ 2 * (g + 1) *
      blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := by
    nlinarith
  obtain ⟨k, κ, -, hnorm, hrange, hcent, -⟩ :=
    rckRP_slModel_of_slBlock (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype (B := none)
      (fun _ b hb => by simp at hb) he.2.2.1 hJe hcard hq eW φ hφ hφc hact hcomm
      (fun R hR hRc hfix hinv U₁ U₂ hU hfl =>
        glGeoFlag_none_of_dualPair _ hσ hG hGh he.2.1 he₁ he₂
          (fun x hx => rckRPfu_isometry (by simpa using hR x hx)) hRc hfix hinv hU hfl)
  exact rckRP_modelBig_of_PSL hq κ hnorm hrange hcent

end CFSG.StandardType.RCKRP
