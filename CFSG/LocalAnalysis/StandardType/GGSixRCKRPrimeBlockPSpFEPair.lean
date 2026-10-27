module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open scoped Matrix

private lemma rckRPfe_J_transpose {n f : ℕ} :
    Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private lemma rckRPfe_J_eq_matJ {n f : ℕ} :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      Matrix.J (Fin n) (GaloisField 2 f) := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) = 1 := by
    ext i j
    simp [CharTwo.neg_eq]
  rw [Matrix.J, Matrix.fromBlocks_inj]
  exact ⟨rfl, hneg.symm, hneg, rfl⟩

private lemma rckRPfe_J_isUnit_det {n f : ℕ} :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det := by
  rw [rckRPfe_J_eq_matJ]
  exact Matrix.isUnit_det_J (Fin n) (GaloisField 2 f)

private lemma rckRPfe_mem_statedSp_transpose {n f : ℕ}
    {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hs : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) :
    Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) *
        (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
  have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hs
  simpa [show (⇑(RingHom.id (GaloisField 2 f)) :
      GaloisField 2 f → GaloisField 2 f) = id from rfl, Matrix.map_id] using h

private lemma rckRPfe_dualPair_orth {n f : ℕ}
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠ e) :
    e * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e = 0 ∧
    formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e * e = 0 := by
  have hGh : Matrix.transpose (((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))).map
      (RingHom.id (GaloisField 2 f))) = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [show (⇑(RingHom.id (GaloisField 2 f)) :
      GaloisField 2 f → GaloisField 2 f) = id from rfl, Matrix.map_id]
    exact rckRPfe_J_transpose
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    fun s hs => rckRPfe_mem_statedSp_transpose (hSU s hs)
  exact CFSG.StandardType.ClassicalPosition.Geo.mul_formAdj_eq_zero_of_dualPair
    (RingHom.id (GaloisField 2 f)) (fun _ => rfl) rckRPfe_J_isUnit_det hGh hSU' hS he hpair

theorem rckRP_flaggedModel_PSp_fieldExtPair
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e) (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
      (e + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
        (e + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e)⁆) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, eW, φ, hcard, hact, hcomm⟩ :=
    exists_blockAction_dualPair_PSp (F := GaloisField 2 f) hc hSU hS hodd he hpair
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 f) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 f) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * f := by
    nlinarith
  have horth := rckRPfe_dualPair_orth hSU hS he hpair
  refine rckRP_flaggedModel_of_slBlock
    (fun y => spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2)
    he.2.2.1 hJe hcard hq eW φ.toMonoidHom φ.injective ?_ hact hcomm
    (fun R hRSp hRc hfix hinv U₁ U₂ hU hfl =>
      glGeoFlag_spForm_of_dualPair he.2.1 horth.1 horth.2 hRSp hRc hfix hinv hU hfl)
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ φ.surjective]

theorem rckRP_modelBig_PSp_fieldExtPair
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e) (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
      (e + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
        (e + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e)⁆) :
    RCKRPModelBig J' := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, eW, φ, hcard, hact, hcomm⟩ :=
    exists_blockAction_dualPair_PSp (F := GaloisField 2 f) hc hSU hS hodd he hpair
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWac
  letI : Module (GaloisField 2 f) W := hWF
  letI : Module K W := hWK
  letI : IsScalarTower (GaloisField 2 f) K W := hTower
  letI : FiniteDimensional K W := hWfd
  have hq : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * f := by
    nlinarith
  have horth := rckRPfe_dualPair_orth hSU hS he hpair
  obtain ⟨k, κ, -, hnorm, hrange, hcent, -⟩ :=
    rckRP_slModel_of_slBlock (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (fun y => spForm_isometry n (GaloisField 2 f)
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2)
      he.2.2.1 hJe hcard hq eW φ.toMonoidHom φ.injective (by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ φ.surjective]) hact hcomm
      (fun R hR hRc hfix hinv U₁ U₂ hU hfl =>
        glGeoFlag_spForm_of_dualPair he.2.1 horth.1 horth.2 (fun x hx => by simpa using hR x hx)
          hRc hfix hinv hU hfl)
  exact rckRP_modelBig_of_PSL hq κ hnorm hrange hcent

end CFSG.StandardType.RCKRP
