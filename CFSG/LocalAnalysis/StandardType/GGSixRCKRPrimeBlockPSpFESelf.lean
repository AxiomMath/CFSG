module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockSelfPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSUBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

theorem rckRP_flaggedModel_PSp_fieldExtSelf
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K, hKf, hKa, hKfin, l, W, hWac, hWF, hWK, hTower, hWfd, σ, β, eW, φ,
    hdeg', hK, hσ2, hσ1, hfixF, hβs, hβn, hφinj, hφiso, hφsurj, hact, htrace, horth⟩ :=
    exists_blockAction_selfDual_PSp (F := GaloisField 2 f) hc hSU hS hodd he hadj hdeg
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 f) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 f) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hl : 2 ≤ l := by omega
  have hq : 2 ≤ l * f := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ l * f := Nat.mul_le_mul hl hf
  refine rckRP_flaggedModel_of_suBlock (X := CFSG.Open.StatedSp n (GaloisField 2 f))
    (B := spForm n (GaloisField 2 f))
    (fun y b hb m m' =>
      spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2
        b hb m m') he.2.1 hJe hK hq hσ2 hσ1 β hβs hβn eW φ hφinj hφiso
    (fun g hg _ => hφsurj g hg) hact ?_
  intro b hb
  simp only [spForm, Option.mem_def, Option.some.injEq] at hb
  subst b
  exact ⟨fun m₁ m₂ m => by simpa only [add_dotProduct], horth, htrace, hfixF⟩

theorem rckRP_modelBig_PSp_fieldExtSelf
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    RCKRPModelBig J' := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K, hKf, hKa, hKfin, l, W, hWac, hWF, hWK, hTower, hWfd, σ, β, eW, φ,
    hdeg', hK, hσ2, hσ1, hfixF, hβs, hβn, hφinj, hφiso, hφsurj, hact, htrace, horth⟩ :=
    exists_blockAction_selfDual_PSp (F := GaloisField 2 f) hc hSU hS hodd he hadj hdeg
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 f) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 f) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hl : 2 ≤ l := by omega
  have hq : 2 ≤ l * f := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ l * f := Nat.mul_le_mul hl hf
  obtain ⟨t, k, κ, ht, hnorm, hrange, hcent, -, hcard⟩ :=
    rckRP_exists_model_of_suBlock (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (B := spForm n (GaloisField 2 f))
      (fun y b hb m m' =>
        spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2
          b hb m m') he.2.1 hJe hK hq hσ2 hσ1 β hβs hβn eW φ hφinj hφiso
      (fun g hg _ => hφsurj g hg) hact (by
        intro b hb
        simp only [spForm, Option.mem_def, Option.some.injEq] at hb
        subst b
        exact ⟨fun m₁ m₂ m => by simpa only [add_dotProduct], horth, htrace, hfixF⟩)
  refine ⟨t, k, l * f, κ, hnorm, by rcases ht with rfl | rfl <;> simp, hrange, hcent,
    fun γ hγ hlong => ?_⟩
  rw [hcard γ hγ hlong]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hq

end CFSG.StandardType.RCKRP
