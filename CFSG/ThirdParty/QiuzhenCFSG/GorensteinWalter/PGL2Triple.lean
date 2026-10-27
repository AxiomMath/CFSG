module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2AffineCoordinates
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3

namespace CFSG
end CFSG
open CFSG

/-!
# Three-point normalization on the projective line

The natural `PGL₂` action on the projective line is sharply
three-transitive.  This file exposes that fact for the repository's standard
points `∞`, `0`, and `1`, and packages the normalization of an arbitrary
projective-line permutation.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped LinearAlgebra.Projectivization MatrixGroups Pointwise

universe u

/-- The affine projective point with coordinate `1`. -/
@[expose]
public def psl2ProjectiveOne
    (K : Type u) [Field K] : PSL2ProjectiveLine K :=
  psl2AffinePoint K 1

public theorem psl2ProjectiveInfinity_ne_zero
    (K : Type u) [Field K] :
    psl2ProjectiveInfinity K ≠ psl2ProjectiveZero K := by
  intro h
  exact psl2AffinePoint_ne_infinity (K := K) 0
    ((psl2AffinePoint_zero (K := K)).trans h.symm)

public theorem psl2ProjectiveInfinity_ne_one
    (K : Type u) [Field K] :
    psl2ProjectiveInfinity K ≠ psl2ProjectiveOne K := by
  exact (psl2AffinePoint_ne_infinity (K := K) 1).symm

public theorem psl2ProjectiveZero_ne_one
    (K : Type u) [Field K] :
    psl2ProjectiveZero K ≠ psl2ProjectiveOne K := by
  intro h
  have h01 : (0 : K) = 1 := by
    apply psl2AffinePoint_injective
    simpa [psl2ProjectiveOne] using
      (psl2AffinePoint_zero (K := K)).trans h
  exact zero_ne_one h01

/-- The canonical inclusion `PSL₂ → PGL₂` preserves the natural projective
action. -/
public theorem psl2ToPGL_smul
    {K : Type u} [Field K]
    (h : PSL2 K) (x : PSL2ProjectiveLine K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL h • x = h • x := by
  induction h using QuotientGroup.induction_on with
  | _ A => rfl

/-- The natural `PGL₂(K)` action is sharply three-transitive on the
projective line. -/
public theorem pgl2_sharply_three_transitive
    (K : Type u) [Field K] [Finite K]
    (a b c a' b' c' : PSL2ProjectiveLine K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha'b' : a' ≠ b') (ha'c' : a' ≠ c') (hb'c' : b' ≠ c') :
    ∃! g : PGL2 K,
      g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  obtain ⟨_, rho, _iota, _hrho, _hiota, _hiotaApply,
      hrhoApply, _hNormal, _hIndex, hsharp, _hLarge, _hTwo, _hThree⟩ :=
    BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a K
  have hrhoNatural (g : PGL2 K) (x : PSL2ProjectiveLine K) :
      rho g x = g • x := by
    rcases Matrix.ProjGenLinGroup.mk_surjective g with ⟨A, rfl⟩
    exact hrhoApply _ _ A rfl
  simpa only [hrhoNatural] using
    hsharp a b c a' b' c' hab hac hbc ha'b' ha'c' hb'c'

/-- Every projective-line permutation can be normalized at `∞`, `0`, and `1`
by a unique projective-linear transformation. -/
public theorem existsUnique_pgl2_normalizes_projective_triple
    (K : Type u) [Field K] [Finite K]
    (tau : Equiv.Perm (PSL2ProjectiveLine K)) :
    ∃! g : PGL2 K,
      g • tau (psl2ProjectiveInfinity K) = psl2ProjectiveInfinity K ∧
      g • tau (psl2ProjectiveZero K) = psl2ProjectiveZero K ∧
      g • tau (psl2ProjectiveOne K) = psl2ProjectiveOne K := by
  apply pgl2_sharply_three_transitive K
  · exact tau.injective.ne (psl2ProjectiveInfinity_ne_zero K)
  · exact tau.injective.ne (psl2ProjectiveInfinity_ne_one K)
  · exact tau.injective.ne (psl2ProjectiveZero_ne_one K)
  · exact psl2ProjectiveInfinity_ne_zero K
  · exact psl2ProjectiveInfinity_ne_one K
  · exact psl2ProjectiveZero_ne_one K

/-- Conjugation by `g ∈ PGL₂` induces the literal projective action of `g` on
the projective line reconstructed from defining-characteristic Sylow
subgroups. -/
@[simp]
public theorem psl2MulAutProjectiveLine_pgl2InnerAut
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (g : PGL2 K) (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard
        (pgl2InnerAutPSL2 K hK hcard g) x =
      g • x := by
  let e := psl2ProjectiveLineEquivSylow K hKcard
  let beta := pgl2InnerAutPSL2 K hK hcard g
  let P : Sylow p (PSL2 K) := e x
  let P' : Sylow p (PSL2 K) := beta • P
  let Q : Sylow p (PSL2 K) := e (g • x)
  let B : Subgroup (PSL2 K) :=
    MulAction.stabilizer (PSL2 K) (g • x)
  have hPfix {h : PSL2 K} (hh : h ∈ (P : Subgroup (PSL2 K))) :
      h • x = x := by
    have hnorm : h ∈ Subgroup.normalizer (P : Subgroup (PSL2 K)) :=
      Subgroup.le_normalizer hh
    have hstab := psl2ProjectiveLineEquivSylow_stabilizer K hKcard x
    have hmem : h ∈ MulAction.stabilizer (PSL2 K) x := by
      rw [hstab]
      exact hnorm
    exact MulAction.mem_stabilizer_iff.mp hmem
  have hP'leB : (P' : Subgroup (PSL2 K)) ≤ B := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    change y ∈ beta • (P : Subgroup (PSL2 K)) at hy
    change y ∈ Subgroup.map beta.toMonoidHom (P : Subgroup (PSL2 K)) at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    have hhfix := hPfix hh
    calc
      beta h • (g • x) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL (beta h) • (g • x) :=
        (psl2ToPGL_smul (beta h) (g • x)).symm
      _ = (g * Matrix.ProjectiveSpecialLinearGroup.toPGL h * g⁻¹) •
          (g • x) := by
        rw [toPGL_pgl2InnerAutPSL2_apply]
      _ = g • (h • x) := by
        simp only [mul_smul, inv_smul_smul]
        rw [psl2ToPGL_smul]
      _ = g • x := by rw [hhfix]
  have hBQ : B = Subgroup.normalizer (Q : Subgroup (PSL2 K)) := by
    exact psl2ProjectiveLineEquivSylow_stabilizer K hKcard (g • x)
  have hQleB : (Q : Subgroup (PSL2 K)) ≤ B := by
    rw [hBQ]
    exact Subgroup.le_normalizer
  have hQnormal :
      (((Q : Subgroup (PSL2 K)).subgroupOf B)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQleB).2
    rw [hBQ]
  let QSyl : Sylow p B := Q.subtype hQleB
  let PSyl : Sylow p B := P'.subtype hP'leB
  have hQSylNormal : (QSyl : Subgroup B).Normal := by
    change (((Q : Subgroup (PSL2 K)).subgroupOf B)).Normal
    exact hQnormal
  let : Unique (Sylow p B) := Sylow.unique_of_normal QSyl hQSylNormal
  have hsub : PSyl = QSyl := Subsingleton.elim _ _
  have hP'eqQ : P' = Q := Sylow.subtype_injective hsub
  apply e.injective
  rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply]
  exact hP'eqQ

/-- The unique projective-linear factor that normalizes the point permutation
induced by `alpha` at `∞`, `0`, and `1`. -/
@[expose]
public noncomputable def psl2MulAutNormalizerPGL
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) : PGL2 K :=
  Classical.choose
    (existsUnique_pgl2_normalizes_projective_triple K
      (psl2MulAutProjectiveLine K hKcard alpha))

public theorem psl2MulAutNormalizerPGL_spec
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) :
    psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha
            (psl2ProjectiveInfinity K) = psl2ProjectiveInfinity K ∧
      psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha
            (psl2ProjectiveZero K) = psl2ProjectiveZero K ∧
      psl2MulAutNormalizerPGL K hKcard alpha •
          psl2MulAutProjectiveLine K hKcard alpha
            (psl2ProjectiveOne K) = psl2ProjectiveOne K :=
  (Classical.choose_spec
    (existsUnique_pgl2_normalizes_projective_triple K
      (psl2MulAutProjectiveLine K hKcard alpha))).1

/-- Compose `alpha` with its projective-linear normalizing factor. -/
@[expose]
public noncomputable def psl2NormalizedMulAut
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) : MulAut (PSL2 K) :=
  pgl2InnerAutPSL2 K hK hcard
      (psl2MulAutNormalizerPGL K hKcard alpha) * alpha

public theorem psl2NormalizedMulAut_projectiveLine
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard
        (psl2NormalizedMulAut K hKcard hK hcard alpha) x =
      psl2MulAutNormalizerPGL K hKcard alpha •
        psl2MulAutProjectiveLine K hKcard alpha x := by
  rw [psl2NormalizedMulAut, map_mul]
  change psl2MulAutProjectiveLine K hKcard
      (pgl2InnerAutPSL2 K hK hcard
        (psl2MulAutNormalizerPGL K hKcard alpha))
      (psl2MulAutProjectiveLine K hKcard alpha x) = _
  rw [psl2MulAutProjectiveLine_pgl2InnerAut]

public theorem psl2NormalizedMulAut_fixes_standard_triple
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) :
    psl2MulAutProjectiveLine K hKcard
          (psl2NormalizedMulAut K hKcard hK hcard alpha)
          (psl2ProjectiveInfinity K) = psl2ProjectiveInfinity K ∧
      psl2MulAutProjectiveLine K hKcard
          (psl2NormalizedMulAut K hKcard hK hcard alpha)
          (psl2ProjectiveZero K) = psl2ProjectiveZero K ∧
      psl2MulAutProjectiveLine K hKcard
          (psl2NormalizedMulAut K hKcard hK hcard alpha)
          (psl2ProjectiveOne K) = psl2ProjectiveOne K := by
  simpa only [psl2NormalizedMulAut_projectiveLine] using
    psl2MulAutNormalizerPGL_spec K hKcard alpha

end CFSG.GorensteinWalter
