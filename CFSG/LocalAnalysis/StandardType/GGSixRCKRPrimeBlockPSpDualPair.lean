module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRootSubGeo

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private theorem rckRPb3_J_transpose {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).transpose =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.transpose, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem rckRPb3_J_mul_self {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type,
      CharTwo.neg_eq]

private theorem rckRPb3_J_isUnit_det {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det :=
  Matrix.isUnit_det_of_right_inverse (rckRPb3_J_mul_self n)

private theorem rckRPb3_J_mulVec_inl {F : Type} [Field F] (n : ℕ)
    (x : Fin n ⊕ Fin n → F) (i : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x
      (Sum.inl i) = x (Sum.inr i) := by
  simp [Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem rckRPb3_J_mulVec_inr {F : Type} [Field F] (n : ℕ)
    (x : Fin n ⊕ Fin n → F) (i : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x
      (Sum.inr i) = -x (Sum.inl i) := by
  simp [Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem rckRPb3_J_alt {F : Type} [Field F] (n : ℕ)
    (x : Fin n ⊕ Fin n → F) :
    x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x = 0 := by
  have h1 := rckRPb3_J_mulVec_inl n x
  have h2 := rckRPb3_J_mulVec_inr n x
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (x (Sum.inl i)) (x (Sum.inr i)))]
  simp

private theorem rckRPb3_J_linearIndependent {F : Type} [Field F] (n : ℕ)
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F}
    (h1 : a₁ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₁ = 1)
    (h2 : a₂ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₂ = 1)
    (h3 : a₁ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₂ = 0)
    (h4 : a₂ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₁ = 0) :
    LinearIndependent F ![a₁, a₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have := congrArg (fun z => z ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₁) hst
    simpa [smul_eq_mul, h1, h4] using this
  · have := congrArg (fun z => z ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec b₂) hst
    simpa [smul_eq_mul, h2, h3] using this

theorem rckRP_flaggedModel_PSp_dualPair
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
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
  obtain ⟨k, ι, β₀, -, hlong, hcenter, hrange, a₁, a₂, b₁, b₂, h1, h2, h34, hflag, -⟩ :=
    exists_blockModel_dualPair_PSp_explicit n f S hSU hS he hpair hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hnorm : RCKNormalizedModel .PSL (k + 1) f :=
    ⟨by simp [GGPosTag], rckRP_admissible_PSL_of_quasisimple_range hf ι hq⟩
  refine ⟨.PSL, k + 1, f, ι, hnorm, hrange, hcenter, ?_⟩
  refine rckRP_rootFlags_of_long
    (j := (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)
    (B := spForm n (GaloisField 2 f)) ?_ hnorm (by simp) ι ?_ hlong ?_
  · intro y b hb m m'
    exact spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2
      b hb m m'
  · exact ggLongRoot_mem_roots hlong
  · rw [hflag]
    exact glGeoFlag_altSiegelGroup (rckRPb3_J_isUnit_det n) (rckRPb3_J_transpose n)
      (rckRPb3_J_alt n) (rckRPb3_J_linearIndependent n h1 h2 h34.2.2.1 h34.2.2.2) h34.1

theorem rckRP_modelII_PSp_dualPair
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
      (e + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S
        (e + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e)⁆) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  obtain ⟨k, ι, β₀, -, hlong, hcenter, hrange, a₁, a₂, b₁, b₂, h1, h2, h34, hflag, -⟩ :=
    exists_blockModel_dualPair_PSp_explicit n f S hSU hS he hpair hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hnorm : RCKNormalizedModel .PSL (k + 1) f :=
    ⟨by simp [GGPosTag], rckRP_admissible_PSL_of_quasisimple_range hf ι hq⟩
  refine rckRP_modelII_of_long (t := .PSL) (k := k + 1) (g := f) hnorm (by simp) ι hrange
    hcenter ?_ hlong ?_
  · intro R' y hR'
    exact rckRPRootSubOf_map_conj hR' (ι y)
  · exact rckRPRootSubOf_PSp_of_altSiegel h1 h2 h34 hflag

end CFSG.StandardType.RCKRP
