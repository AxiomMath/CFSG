module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockSelfPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSUBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

theorem rckRP_flaggedModel_PSU_fieldExtSelf
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    RCKRPFlaggedModel
      (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
      none J' := by
  let σ₀ := CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)
  let X : Subgroup (GL (Fin n) (GaloisField 2 (2 * (g + 1)))) := Unitary.SU σ₀ n
  have hnt : ⁅glBlockCentralizer X.subtype S e, glBlockCentralizer X.subtype S e⁆ ≠ ⊥ := by
    rintro hbot
    have hsub : Subsingleton ↥J' := ⟨fun a b => Subtype.ext (by
      have ha : a.1 ∈ (⊥ : Subgroup ↥X) := hbot ▸ hJe.1 a.2
      have hb : b.1 ∈ (⊥ : Subgroup ↥X) := hbot ▸ hJe.1 b.2
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb])⟩
    haveI := hsub
    obtain ⟨a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJe.2.2)
    exact hab (Subsingleton.elim a b)
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, σ, β, eW, φ, hcard, hσ2,
      hσ1, hβs, hβn, hφ, hφiso, hφsurj, hact⟩ :=
    exists_blockAction_selfDual_PSU (F := GaloisField 2 (2 * (g + 1))) (f := g + 1) (n := n)
      (card_galoisField_two_mul 2 (g + 1) (by omega)) hSU hS hodd he hadj hdeg hnt
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 (2 * (g + 1))) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 (2 * (g + 1))) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 (2 * (g + 1))) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ (g + 1) * blockDegree
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := by
    calc 2 ≤ blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := hdeg
      _ = 1 * blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := (one_mul _).symm
      _ ≤ (g + 1) * blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e :=
        Nat.mul_le_mul_right _ (by omega : 1 ≤ g + 1)
  exact rckRP_flaggedModel_of_suBlock (X := X) (B := none)
    (S := S) (e := e) (J' := J') (fun _ b hb => by simp at hb) he.2.1 hJe hcard hq hσ2 hσ1 β
    hβs hβn eW φ hφ hφiso hφsurj hact (fun b hb => by simp at hb)

theorem rckRP_modelBig_PSU_fieldExtSelf
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    RCKRPModelBig J' := by
  let σ₀ := CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)
  let X : Subgroup (GL (Fin n) (GaloisField 2 (2 * (g + 1)))) := Unitary.SU σ₀ n
  have hnt : ⁅glBlockCentralizer X.subtype S e, glBlockCentralizer X.subtype S e⁆ ≠ ⊥ := by
    rintro hbot
    have hsub : Subsingleton ↥J' := ⟨fun a b => Subtype.ext (by
      have ha : a.1 ∈ (⊥ : Subgroup ↥X) := hbot ▸ hJe.1 a.2
      have hb : b.1 ∈ (⊥ : Subgroup ↥X) := hbot ▸ hJe.1 b.2
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb])⟩
    haveI := hsub
    obtain ⟨a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJe.2.2)
    exact hab (Subsingleton.elim a b)
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, σ, β, eW, φ, hcard, hσ2,
      hσ1, hβs, hβn, hφ, hφiso, hφsurj, hact⟩ :=
    exists_blockAction_selfDual_PSU (F := GaloisField 2 (2 * (g + 1))) (f := g + 1) (n := n)
      (card_galoisField_two_mul 2 (g + 1) (by omega)) hSU hS hodd he hadj hdeg hnt
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 (2 * (g + 1))) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 (2 * (g + 1))) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 (2 * (g + 1))) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ (g + 1) * blockDegree
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := by
    calc 2 ≤ blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := hdeg
      _ = 1 * blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e := (one_mul _).symm
      _ ≤ (g + 1) * blockDegree
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e :=
        Nat.mul_le_mul_right _ (by omega : 1 ≤ g + 1)
  obtain ⟨t, k, κ, ht, hnorm, hrange, hcent, -, hcardR⟩ :=
    rckRP_exists_model_of_suBlock X.subtype (B := none) (S := S) (e := e) (J' := J')
      (fun _ b hb => by simp at hb) he.2.1 hJe hcard hq hσ2 hσ1 β hβs hβn eW φ hφ hφiso hφsurj
      hact (fun b hb => by simp at hb)
  refine ⟨t, k, _, κ, hnorm, by rcases ht with rfl | rfl <;> simp, hrange, hcent,
    fun γ hγ hlong => ?_⟩
  rw [hcardR γ hγ hlong]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ _ := Nat.pow_le_pow_right (by norm_num) hq

end CFSG.StandardType.RCKRP
