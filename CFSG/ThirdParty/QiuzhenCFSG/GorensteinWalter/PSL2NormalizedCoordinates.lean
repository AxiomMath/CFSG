module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Triple
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

namespace CFSG
end CFSG
open CFSG

/-!
# Affine coordinates of a normalized automorphism of `PSL₂`

After composing an arbitrary automorphism of `PSL₂(K)` with its unique
projective-linear normalizing factor, the induced projective-line permutation
fixes `∞`, `0`, and `1`.  This file restricts that permutation to the affine
chart and begins recovering the coefficient-field structure.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups Pointwise

universe u

/-- The permutation of field coordinates induced by the normalized
projective-line action of an abstract automorphism of `PSL₂(K)`. -/
@[expose]
public noncomputable def psl2NormalizedAffinePerm
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) : Equiv.Perm K := by
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard
      (psl2NormalizedMulAut K hKcard hK hcard alpha)
  have hfix : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).1
  let tauAffine :
      {x : PSL2ProjectiveLine K // x ≠ psl2ProjectiveInfinity K} ≃
        {x : PSL2ProjectiveLine K // x ≠ psl2ProjectiveInfinity K} :=
    tau.subtypeEquiv (fun x => by
      constructor
      · intro hx htx
        apply hx
        apply tau.injective
        rw [htx, hfix]
      · intro htx hx
        subst x
        exact htx hfix)
  exact (psl2AffineEquiv K).trans
    (tauAffine.trans (psl2AffineEquiv K).symm)

public theorem psl2NormalizedAffinePerm_point
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (x : K) :
    psl2AffinePoint K
        (psl2NormalizedAffinePerm K hKcard hK hcard alpha x) =
      psl2MulAutProjectiveLine K hKcard
        (psl2NormalizedMulAut K hKcard hK hcard alpha)
        (psl2AffinePoint K x) := by
  simp [psl2NormalizedAffinePerm]
  exact congrArg Subtype.val
    ((psl2AffineEquiv K).apply_symm_apply _)

@[simp]
public theorem psl2NormalizedAffinePerm_zero
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) :
    psl2NormalizedAffinePerm K hKcard hK hcard alpha 0 = 0 := by
  apply psl2AffinePoint_injective
  rw [psl2NormalizedAffinePerm_point, psl2AffinePoint_zero]
  exact (psl2NormalizedMulAut_fixes_standard_triple
    K hKcard hK hcard alpha).2.1

@[simp]
public theorem psl2NormalizedAffinePerm_one
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) :
    psl2NormalizedAffinePerm K hKcard hK hcard alpha 1 = 1 := by
  apply psl2AffinePoint_injective
  rw [psl2NormalizedAffinePerm_point]
  exact (psl2NormalizedMulAut_fixes_standard_triple
    K hKcard hK hcard alpha).2.2

/-- A normalized automorphism carries the upper transvection with parameter
`a` to the upper transvection whose parameter is the induced affine
coordinate of `a`. -/
public theorem psl2NormalizedMulAut_upperUnipotent
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (a : K) :
    psl2NormalizedMulAut K hKcard hK hcard alpha
        (psl2QuotientMap K (sl2UpperUnipotent a)) =
      psl2QuotientMap K
        (sl2UpperUnipotent
          (psl2NormalizedAffinePerm K hKcard hK hcard alpha a)) := by
  let beta : MulAut (PSL2 K) :=
    psl2NormalizedMulAut K hKcard hK hcard alpha
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard beta
  let U : Sylow p (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  have hfixInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).1
  have hfixZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K :=
    (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).2.1
  have hUSylow : beta • U = U := by
    have h := congrArg (psl2ProjectiveLineEquivSylow K hKcard)
      hfixInfinity
    rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply,
      psl2ProjectiveLineEquivSylow_infinity] at h
    simpa [U] using h
  have haU : psl2QuotientMap K (sl2UpperUnipotent a) ∈
      (U : Subgroup (PSL2 K)) := by
    rw [psl2UpperUnipotentSylow_coe]
    exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨a, rfl⟩
  have hbetaU :
      beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        (U : Subgroup (PSL2 K)) := by
    have hmem :
        beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
          (beta • U : Sylow p (PSL2 K)) := by
      change beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        beta • (U : Subgroup (PSL2 K))
      change beta (psl2QuotientMap K (sl2UpperUnipotent a)) ∈
        (U : Subgroup (PSL2 K)).map (beta : PSL2 K →* PSL2 K)
      exact Subgroup.mem_map.mpr ⟨_, haU, rfl⟩
    rwa [hUSylow] at hmem
  rw [psl2UpperUnipotentSylow_coe] at hbetaU
  obtain ⟨b, hb⟩ :=
    (mem_psl2UpperUnipotentSubgroup_iff _).1 hbetaU
  have hsmul := psl2MulAutProjectiveLine_smul K hKcard beta
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K 0)
  rw [psl2UpperUnipotent_smul_affine, zero_add] at hsmul
  rw [psl2AffinePoint_zero, hfixZero, hb] at hsmul
  rw [← psl2AffinePoint_zero,
    psl2UpperUnipotent_smul_affine, zero_add] at hsmul
  have hab :
      psl2NormalizedAffinePerm K hKcard hK hcard alpha a = b := by
    apply psl2AffinePoint_injective
    rw [psl2NormalizedAffinePerm_point]
    exact hsmul
  rw [hb, hab]

/-- The affine-coordinate permutation induced by a normalized automorphism is
additive. -/
public theorem psl2NormalizedAffinePerm_add
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (x a : K) :
    psl2NormalizedAffinePerm K hKcard hK hcard alpha (x + a) =
      psl2NormalizedAffinePerm K hKcard hK hcard alpha x +
        psl2NormalizedAffinePerm K hKcard hK hcard alpha a := by
  let beta : MulAut (PSL2 K) :=
    psl2NormalizedMulAut K hKcard hK hcard alpha
  have hsmul := psl2MulAutProjectiveLine_smul K hKcard beta
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K x)
  rw [psl2UpperUnipotent_smul_affine] at hsmul
  rw [← psl2NormalizedAffinePerm_point K hKcard hK hcard alpha (x + a),
    psl2NormalizedMulAut_upperUnipotent K hKcard hK hcard alpha a,
    ← psl2NormalizedAffinePerm_point K hKcard hK hcard alpha x,
    psl2UpperUnipotent_smul_affine] at hsmul
  exact psl2AffinePoint_injective hsmul

/-- The additive equivalence underlying the normalized affine coordinate
permutation. -/
@[expose]
public noncomputable def psl2NormalizedAffineAddEquiv
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) : K ≃+ K :=
  { psl2NormalizedAffinePerm K hKcard hK hcard alpha with
    map_add' := psl2NormalizedAffinePerm_add K hKcard hK hcard alpha }

/-- The normalized affine permutation commutes with scalar multiplication by
squares. -/
public theorem psl2NormalizedAffinePerm_sq_mul
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (t x : K) :
    psl2NormalizedAffinePerm K hKcard hK hcard alpha (t ^ 2 * x) =
      psl2NormalizedAffinePerm K hKcard hK hcard alpha (t ^ 2) *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha x := by
  by_cases ht : t = 0
  · subst t
    simp
  let beta : MulAut (PSL2 K) :=
    psl2NormalizedMulAut K hKcard hK hcard alpha
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard beta
  let d : PSL2 K := psl2QuotientMap K
    (Matrix.SpecialLinearGroup.diag2 t ht)
  have hfixInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K :=
    (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).1
  have hfixZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K :=
    (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).2.1
  have hdInfinity : d • psl2ProjectiveInfinity K =
      psl2ProjectiveInfinity K := by
    change Matrix.SpecialLinearGroup.diag2 t ht •
      psl2ProjectiveInfinity K = psl2ProjectiveInfinity K
    rw [← MulAction.mem_stabilizer_iff,
      sl2_mem_stabilizer_infinity_iff]
    simp [Matrix.SpecialLinearGroup.diag2_coe']
  have hdZero : d • psl2ProjectiveZero K =
      psl2ProjectiveZero K := by
    change Matrix.SpecialLinearGroup.diag2 t ht •
      psl2ProjectiveZero K = psl2ProjectiveZero K
    rw [← MulAction.mem_stabilizer_iff,
      sl2_mem_stabilizer_zero_iff]
    simp [Matrix.SpecialLinearGroup.diag2_coe']
  have hbetaInfinity : beta d • psl2ProjectiveInfinity K =
      psl2ProjectiveInfinity K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2ProjectiveInfinity K)
    rw [hdInfinity, hfixInfinity] at h
    exact h.symm
  have hbetaZero : beta d • psl2ProjectiveZero K =
      psl2ProjectiveZero K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2ProjectiveZero K)
    rw [hdZero, hfixZero] at h
    exact h.symm
  obtain ⟨c, hc⟩ :=
    exists_psl2_smul_affine_eq_mul_of_fixes_infinity_zero
      (beta d) hbetaInfinity hbetaZero
  have hscale (y : K) :
      psl2NormalizedAffinePerm K hKcard hK hcard alpha (t ^ 2 * y) =
        c * psl2NormalizedAffinePerm K hKcard hK hcard alpha y := by
    have h := psl2MulAutProjectiveLine_smul K hKcard beta d
      (psl2AffinePoint K y)
    rw [psl2Diag2_smul_affine] at h
    rw [← psl2NormalizedAffinePerm_point K hKcard hK hcard alpha
        (t ^ 2 * y),
      ← psl2NormalizedAffinePerm_point K hKcard hK hcard alpha y,
      hc] at h
    exact psl2AffinePoint_injective h
  have hcEq : c =
      psl2NormalizedAffinePerm K hKcard hK hcard alpha (t ^ 2) := by
    have h := hscale 1
    simpa using h.symm
  rw [hscale, hcEq]

/-- The normalized affine permutation preserves multiplication. -/
public theorem psl2NormalizedAffinePerm_mul
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (x y : K) :
    psl2NormalizedAffinePerm K hKcard hK hcard alpha (x * y) =
      psl2NormalizedAffinePerm K hKcard hK hcard alpha x *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha y := by
  let : Fintype K := Fintype.ofFinite K
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨q, n, _hqPrime, hqOdd, _hn, hqcard⟩
    rw [hqcard]
    exact hqOdd.pow
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have heven : Fintype.card K % 2 = 0 :=
      FiniteField.even_card_of_char_two hchar
    have hqOdd' : Odd (Fintype.card K) := by
      simpa [Nat.card_eq_fintype_card] using hqOdd
    rcases hqOdd' with ⟨m, hm⟩
    omega
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  let a : K := (y + 1) / 2
  let b : K := (y - 1) / 2
  have hy : y = a ^ 2 - b ^ 2 := by
    dsimp [a, b]
    field_simp [htwo]
    all_goals ring
  let sigmaAdd : K ≃+ K :=
    psl2NormalizedAffineAddEquiv K hKcard hK hcard alpha
  calc
    psl2NormalizedAffinePerm K hKcard hK hcard alpha (x * y) =
        psl2NormalizedAffinePerm K hKcard hK hcard alpha
          ((a ^ 2 - b ^ 2) * x) := by rw [hy, mul_comm]
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha
          (a ^ 2 * x - b ^ 2 * x) := by
      congr 1
      ring
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha
          (a ^ 2 * x) -
        psl2NormalizedAffinePerm K hKcard hK hcard alpha
          (b ^ 2 * x) := by
      exact map_sub sigmaAdd _ _
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha (a ^ 2) *
          psl2NormalizedAffinePerm K hKcard hK hcard alpha x -
        psl2NormalizedAffinePerm K hKcard hK hcard alpha (b ^ 2) *
          psl2NormalizedAffinePerm K hKcard hK hcard alpha x := by
      rw [psl2NormalizedAffinePerm_sq_mul,
        psl2NormalizedAffinePerm_sq_mul]
    _ = (psl2NormalizedAffinePerm K hKcard hK hcard alpha (a ^ 2) -
          psl2NormalizedAffinePerm K hKcard hK hcard alpha (b ^ 2)) *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha x := by ring
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha
          (a ^ 2 - b ^ 2) *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha x := by
      congr 1
      exact (map_sub sigmaAdd (a ^ 2) (b ^ 2)).symm
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha y *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha x := by rw [← hy]
    _ = psl2NormalizedAffinePerm K hKcard hK hcard alpha x *
        psl2NormalizedAffinePerm K hKcard hK hcard alpha y := mul_comm _ _

/-- The field automorphism recovered from the projective-line action of a
normalized abstract automorphism of `PSL₂(K)`. -/
@[expose]
public noncomputable def psl2NormalizedAffineRingEquiv
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) : K ≃+* K :=
  { psl2NormalizedAffineAddEquiv K hKcard hK hcard alpha with
    map_mul' := psl2NormalizedAffinePerm_mul K hKcard hK hcard alpha }

@[simp]
public theorem psl2NormalizedAffineRingEquiv_apply
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) (x : K) :
    psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha x =
      psl2NormalizedAffinePerm K hKcard hK hcard alpha x := rfl

/-- Entrywise field automorphisms carry upper transvections to the upper
transvections with transformed parameters. -/
public theorem psl2FieldAut_upperUnipotent
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : K) :
    psl2FieldAut K sigma
        (psl2QuotientMap K (sl2UpperUnipotent a)) =
      psl2QuotientMap K (sl2UpperUnipotent (sigma a)) := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center _) (sl2UpperUnipotent a)) = _
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · change sigma 1 = 1
    simp
  · change sigma a = sigma a
    rfl
  · change sigma 0 = 0
    simp
  · change sigma 1 = 1
    simp

/-- Entrywise field automorphisms fix the standard symplectic element. -/
public theorem psl2FieldAut_symplecticElement
    (K : Type u) [Field K] (sigma : K ≃+* K) :
    psl2FieldAut K sigma (psl2SymplecticElement K) =
      psl2SymplecticElement K := by
  rw [psl2FieldAut_apply]
  rw [psl2SymplecticElement_eq_mk]
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · change sigma 0 = 0
    simp
  · change sigma (-1) = -1
    simp
  · change sigma 1 = 1
    simp
  · change sigma 0 = 0
    simp

/-- The standard symplectic element carries infinity to zero. -/
public theorem psl2SymplecticElement_smul_infinity
    (K : Type u) [Field K] :
    psl2SymplecticElement K • psl2ProjectiveInfinity K =
      psl2ProjectiveZero K := by
  let e0 : Fin 2 → K := ![1, 0]
  let e1 : Fin 2 → K := ![0, 1]
  rw [psl2SymplecticElement_eq_mk]
  change sl2SymplecticMatrix K • psl2ProjectiveInfinity K =
    psl2ProjectiveZero K
  rw [psl2ProjectiveInfinity, psl2ProjectiveZero,
    Projectivization.smul_mk]
  change Projectivization.mk K
      ((sl2SymplecticMatrix K).1 *ᵥ e0) _ =
    Projectivization.mk K e1 _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  change (1 : K) • e1 = (sl2SymplecticMatrix K).1 *ᵥ e0
  ext i
  fin_cases i <;>
    simp [sl2SymplecticMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail, e0, e1]

/-- The projective-line permutation induced by a coefficient automorphism is
the corresponding entrywise permutation of affine coordinates. -/
public theorem psl2MulAutProjectiveLine_fieldAut_affine
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) (a : K) :
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
        (psl2AffinePoint K a) =
      psl2AffinePoint K (sigma a) := by
  let phi : MulAut (PSL2 K) := psl2FieldAut K sigma
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard phi
  let U : Sylow p (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  have hUSylow : phi • U = U := by
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def]
    rw [psl2UpperUnipotentSylow_coe]
    ext g
    change g ∈ (psl2UpperUnipotentSubgroup K).map
      (phi : PSL2 K →* PSL2 K) ↔ g ∈ psl2UpperUnipotentSubgroup K
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨b, rfl⟩ :=
        (mem_psl2UpperUnipotentSubgroup_iff h).1 hh
      change phi (psl2QuotientMap K (sl2UpperUnipotent b)) ∈
        psl2UpperUnipotentSubgroup K
      have hmap : phi (psl2QuotientMap K (sl2UpperUnipotent b)) =
          psl2QuotientMap K (sl2UpperUnipotent (sigma b)) := by
        simpa [phi] using psl2FieldAut_upperUnipotent K sigma b
      rw [hmap]
      exact (mem_psl2UpperUnipotentSubgroup_iff _).2
        ⟨sigma b, rfl⟩
    · intro hg
      obtain ⟨b, rfl⟩ :=
        (mem_psl2UpperUnipotentSubgroup_iff g).1 hg
      refine ⟨psl2QuotientMap K
          (sl2UpperUnipotent (sigma.symm b)), ?_, ?_⟩
      · exact (mem_psl2UpperUnipotentSubgroup_iff _).2
          ⟨sigma.symm b, rfl⟩
      · change phi (psl2QuotientMap K
            (sl2UpperUnipotent (sigma.symm b))) =
          psl2QuotientMap K (sl2UpperUnipotent b)
        have hmap := psl2FieldAut_upperUnipotent K sigma (sigma.symm b)
        simpa [phi] using hmap
  have hInfinity : tau (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K := by
    apply (psl2ProjectiveLineEquivSylow K hKcard).injective
    rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply,
      psl2ProjectiveLineEquivSylow_infinity]
    simpa [phi, U] using hUSylow
  have hZero : tau (psl2ProjectiveZero K) =
      psl2ProjectiveZero K := by
    have h := psl2MulAutProjectiveLine_smul K hKcard phi
      (psl2SymplecticElement K) (psl2ProjectiveInfinity K)
    rw [psl2SymplecticElement_smul_infinity,
      psl2FieldAut_symplecticElement, hInfinity,
      psl2SymplecticElement_smul_infinity] at h
    exact h
  have h := psl2MulAutProjectiveLine_smul K hKcard phi
    (psl2QuotientMap K (sl2UpperUnipotent a))
    (psl2AffinePoint K 0)
  rw [psl2UpperUnipotent_smul_affine, zero_add] at h
  rw [psl2AffinePoint_zero, hZero,
    psl2FieldAut_upperUnipotent] at h
  rw [← psl2AffinePoint_zero,
    psl2UpperUnipotent_smul_affine, zero_add] at h
  exact h

/-- A coefficient automorphism fixes the point at infinity in the
reconstructed projective-line action. -/
public theorem psl2MulAutProjectiveLine_fieldAut_infinity
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) :
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
        (psl2ProjectiveInfinity K) =
      psl2ProjectiveInfinity K := by
  let tau : Equiv.Perm (PSL2ProjectiveLine K) :=
    psl2MulAutProjectiveLine K hKcard (psl2FieldAut K sigma)
  by_contra hInfinity
  obtain ⟨b, hb, _⟩ := existsUnique_psl2AffinePoint_eq
    (tau (psl2ProjectiveInfinity K)) hInfinity
  obtain ⟨a, rfl⟩ := sigma.surjective b
  have hAffine := psl2MulAutProjectiveLine_fieldAut_affine
    K hKcard sigma a
  have hEq : tau (psl2AffinePoint K a) =
      tau (psl2ProjectiveInfinity K) := hAffine.trans hb
  exact psl2AffinePoint_ne_infinity a (tau.injective hEq)

/-- The normalized automorphism is exactly the coefficient automorphism
recovered from its affine-coordinate action. -/
public theorem psl2NormalizedMulAut_eq_fieldAut
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (alpha : MulAut (PSL2 K)) :
    psl2NormalizedMulAut K hKcard hK hcard alpha =
      psl2FieldAut K
        (psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha) := by
  apply psl2MulAutProjectiveLine_injective K hKcard
  apply Equiv.ext
  intro z
  by_cases hz : z = psl2ProjectiveInfinity K
  · subst z
    exact (psl2NormalizedMulAut_fixes_standard_triple
      K hKcard hK hcard alpha).1.trans
        (psl2MulAutProjectiveLine_fieldAut_infinity K hKcard
          (psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha)).symm
  · obtain ⟨x, hx, _⟩ := existsUnique_psl2AffinePoint_eq z hz
    calc
      psl2MulAutProjectiveLine K hKcard
          (psl2NormalizedMulAut K hKcard hK hcard alpha) z =
          psl2AffinePoint K
            (psl2NormalizedAffinePerm K hKcard hK hcard alpha x) := by
        rw [← hx]
        exact (psl2NormalizedAffinePerm_point
          K hKcard hK hcard alpha x).symm
      _ = psl2AffinePoint K
          (psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha x) := rfl
      _ = psl2MulAutProjectiveLine K hKcard
          (psl2FieldAut K
            (psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha)) z := by
        rw [← hx]
        exact (psl2MulAutProjectiveLine_fieldAut_affine K hKcard
          (psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha) x).symm

end CFSG.GorensteinWalter
