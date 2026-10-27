module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2InnerSplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The split-half fixed-field divisibility for the semilinear conjugate

This is the split half of the `hU0fixed` transport used by the
equation-(4) PSL₂ branch.  Let `sigma : K ≃+* K` be an odd prime-order
coefficient automorphism, `z : PGL2 K` a projective matrix, and `B` a
subgroup of `Kˣ` whose split-torus image lies in the derived `PSL₂` layer.
Assume that for every `b ∈ B` the semilinear conjugate `z · T(σ(b)) · z⁻¹`
equals `T(b)`, where `T := pGammaL2FullSplitTorus K` and `σ(b)` denotes
`Units.map sigma.toRingHom b`.

Then `|B| ∣ (|Fix σ| − 1)/2`.  The proof splits on whether `σ` fixes `B`
pointwise:

* diagonal case: `B` embeds into the fixed-field units, and
  `pGammaL2_pureField_innerSplitTorus_fixedSubfield` applied to
  `B.map T` gives the half divisibility;
* anti-diagonal case: the projective matrix equation forces `z` to be
  anti-diagonal, so `σ(b) = b⁻¹` on `B`; a prime-order automorphism
  cannot invert a subgroup of order `> 2`, hence `|B| ≤ 2`, and the
  parity of the split half `(q − 1)/2` (with `q = |K| = |Fix σ|^p`,
  `p` odd) gives `2 ∣ (|Fix σ| − 1)/2`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

private lemma two_ne_zero_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h2
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_char : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2
  have hchar2 : ringChar K = 2 := by
    rcases hdvd_char with ⟨c, hc⟩
    cases c with
    | zero => norm_num at hc
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            have hrc_pos : 0 < ringChar K := by
              by_contra h
              have hz : ringChar K = 0 := by omega
              rw [hz] at hc
              norm_num at hc
            have hrc_le : ringChar K ≤ 1 := by nlinarith
            have hrc1 : ringChar K = 1 := by omega
            have hsub : Subsingleton K := (ringChar.ringChar_eq_one (R := K)).mp hrc1
            exact not_subsingleton K hsub
  have hdvd_card : 2 ∣ Fintype.card K :=
    (prime_dvd_char_iff_dvd_card (R := K) (p := 2)).mp (by simpa [hchar2])
  have hprime_dvd : (2 : ℕ) ∣ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hdvd_card
  exact hodd.not_two_dvd_nat hprime_dvd

/-- A pure coefficient automorphism commuting with the split torus: from
`σ(b) = b` (as units) the semilinear element `(1, σ)` commutes with the
projective diagonal class `T(b)`. -/
private lemma pGammaL2_fullSplitTorus_sigma_commute
    (K : Type u) [Field K] (sigma : K ≃+* K) (b : Kˣ)
    (hfix : Units.map sigma.toRingHom b = b) :
    Commute (SemidirectProduct.inr sigma : PGammaL2 K)
      (SemidirectProduct.inl (pGammaL2FullSplitTorus K b)) := by
  change SemidirectProduct.inr sigma *
      SemidirectProduct.inl (pGammaL2FullSplitTorus K b) =
    SemidirectProduct.inl (pGammaL2FullSplitTorus K b) *
      (SemidirectProduct.inr sigma : PGammaL2 K)
  rw [SemidirectProduct.mul_def (SemidirectProduct.inr sigma)
      (SemidirectProduct.inl (pGammaL2FullSplitTorus K b)),
    SemidirectProduct.mul_def (SemidirectProduct.inl (pGammaL2FullSplitTorus K b))
      (SemidirectProduct.inr sigma)]
  apply SemidirectProduct.ext
  · calc
      (1 : PGL2 K) * pgl2FieldAut K sigma (pGammaL2FullSplitTorus K b) =
          pgl2FieldAut K sigma (pGammaL2FullSplitTorus K b) := by simp
      _ = pGammaL2FullSplitTorus K (Units.map sigma.toRingHom b) :=
        pGammaL2FullSplitTorus_map_field K sigma b
      _ = pGammaL2FullSplitTorus K b := by rw [hfix]
      _ = pGammaL2FullSplitTorus K b * (pgl2FieldAut K (1 : K ≃+* K)) 1 := by simp
  · simp

/-- The projective conjugation equation `z · T(c) · z⁻¹ = T(d)` lifts to a
matrix-level scalar equation `M · D(c) = μ • (D(d) · M)`. -/
private lemma mk_conj_diag_scalar_mul (K : Type u) [Field K]
    (M : GL (Fin 2) K) (c d : Kˣ)
    (h : Matrix.ProjGenLinGroup.mk M * pGammaL2FullSplitTorus K c *
          (Matrix.ProjGenLinGroup.mk M)⁻¹ = pGammaL2FullSplitTorus K d) :
    ∃ mu : Kˣ,
      (M : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![((c : Kˣ) : K), 1] =
        (mu : K) • (Matrix.diagonal ![((d : Kˣ) : K), 1] * (M : Matrix (Fin 2) (Fin 2) K)) := by
  change Matrix.ProjGenLinGroup.mk M *
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K c) *
        (Matrix.ProjGenLinGroup.mk M)⁻¹ =
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K d) at h
  have hinv : (Matrix.ProjGenLinGroup.mk M)⁻¹ =
      Matrix.ProjGenLinGroup.mk (M⁻¹) := by
    exact (map_inv Matrix.ProjGenLinGroup.mk M).symm
  rw [hinv, ← map_mul, ← map_mul] at h
  rcases (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mp h with ⟨u, hu⟩
  -- hu : (M * D_c * M⁻¹) * scalar u = D_d  (as GL); multiply by M on the right
  have huM : ((M * (pGammaL2FullSplitTorusGL K c) * M⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) u) * M =
      pGammaL2FullSplitTorusGL K d * M := by
    exact congrArg (fun X : GL (Fin 2) K => X * M) hu
  let Dc : GL (Fin 2) K := pGammaL2FullSplitTorusGL K c
  let Dd : GL (Fin 2) K := pGammaL2FullSplitTorusGL K d
  let S : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) u
  have hstep : (M * Dc) * S = Dd * M := by
    calc
      (M * Dc) * S = (M * Dc) * (M⁻¹ * M) * S := by group
      _ = (M * Dc * M⁻¹) * (M * S) := by group
      _ = (M * Dc * M⁻¹) * (S * M) := by
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [S, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, one_apply,
          mul_comm, mul_left_comm, mul_assoc]
      _ = ((M * Dc * M⁻¹) * S) * M := by group
      _ = Dd * M := huM
  have hSM : (S : Matrix (Fin 2) (Fin 2) K) = (u : K) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, Matrix.GeneralLinearGroup.scalar,
      Matrix.smul_apply, one_apply, smul_eq_mul]
  have huSM : (u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
      Matrix.diagonal ![((c : Kˣ) : K), 1]) =
      Matrix.diagonal ![((d : Kˣ) : K), 1] * (M : Matrix (Fin 2) (Fin 2) K) := by
    have hprod : ((M : Matrix (Fin 2) (Fin 2) K) * (Dc : Matrix (Fin 2) (Fin 2) K) *
        (S : Matrix (Fin 2) (Fin 2) K)) =
        ((Dd : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K)) := by
      have hstep' := congrArg
        (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hstep
      simpa [map_mul, Dc, Dd] using hstep'
    rw [hSM] at hprod
    rw [Matrix.mul_smul, Matrix.mul_one] at hprod
    simpa [Dc, Dd, pGammaL2FullSplitTorusGL, Matrix.diagonal] using hprod
  refine ⟨u⁻¹, ?_⟩
  have hstep' : (u⁻¹ : K) • ((u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
      Matrix.diagonal ![((c : Kˣ) : K), 1])) =
      (u⁻¹ : K) • (Matrix.diagonal ![((d : Kˣ) : K), 1] *
        (M : Matrix (Fin 2) (Fin 2) K)) := by
    exact congrArg (fun X : Matrix (Fin 2) (Fin 2) K => (u⁻¹ : K) • X) huSM
  have hinv1 : (u⁻¹ : K) * (u : K) = 1 := by
    simpa [mul_comm] using (Units.val_inv u)
  simpa [smul_smul, hinv1] using hstep'

/-- A field automorphism preserves multiplicative inverses of nonzero
elements. -/
private lemma ringEquiv_inv_apply (K : Type u) [Field K]
    (sigma : K ≃+* K) (x : K) (hx0 : x ≠ 0) : sigma x⁻¹ = (sigma x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  calc
    sigma x * sigma x⁻¹ = sigma (x * x⁻¹) := by rw [← map_mul]
    _ = sigma 1 := by rw [mul_inv_cancel₀ hx0]
    _ = 1 := map_one sigma

/-- For an odd-prime-order automorphism that inverts `x`, the powers of `σ`
alternate between `x` (even exponent) and `x⁻¹` (odd exponent). -/
private lemma ringEquiv_pow_alternating (K : Type u) [Field K]
    (sigma : K ≃+* K) (x : K) (hx0 : x ≠ 0)
    (hσx : sigma x = x⁻¹) :
    ∀ j : ℕ, (sigma ^ j) x = (if Even j then x else x⁻¹) ∧
      (sigma ^ j) x⁻¹ = (if Even j then x⁻¹ else x) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      constructor
      · rw [pow_succ]
        rw [show (sigma ^ j * sigma) x = (sigma ^ j) (sigma x) by rfl]
        rw [hσx]
        rw [ih.2]
        rcases Nat.even_or_odd j with hjEven | hjOdd
        · have hnot : ¬ Even (j + 1) := by
            rcases hjEven with ⟨m, hm⟩
            intro hsucc
            rcases hsucc with ⟨m', hm'⟩
            omega
          simp [hjEven, hnot]
        · have hnotEven : ¬ Even j := by
            rcases hjOdd with ⟨m, hm⟩
            intro hE
            rcases hE with ⟨m', hm'⟩
            omega
          have hsucc : Even (j + 1) := by
            rcases hjOdd with ⟨m, hm⟩
            refine ⟨m + 1, ?_⟩
            omega
          simp [hnotEven, hsucc]
      · rw [pow_succ]
        rw [show (sigma ^ j * sigma) x⁻¹ = (sigma ^ j) (sigma x⁻¹) by rfl]
        have hσinv : sigma x⁻¹ = x := by
          rw [ringEquiv_inv_apply K sigma x hx0]
          rw [hσx]
          simp
        rw [hσinv]
        rw [ih.1]
        rcases Nat.even_or_odd j with hjEven | hjOdd
        · have hnot : ¬ Even (j + 1) := by
            rcases hjEven with ⟨m, hm⟩
            intro hsucc
            rcases hsucc with ⟨m', hm'⟩
            omega
          simp [hjEven, hnot]
        · have hnotEven : ¬ Even j := by
            rcases hjOdd with ⟨m, hm⟩
            intro hE
            rcases hE with ⟨m', hm'⟩
            omega
          have hsucc : Even (j + 1) := by
            rcases hjOdd with ⟨m, hm⟩
            refine ⟨m + 1, ?_⟩
            omega
          simp [hnotEven, hsucc]

/-- Parity transfer for the split half: for odd `r` and odd `p`, if
`(r^p − 1)/2` is even then `(r − 1)/2` is even. -/
private lemma splitHalf_parity (r p : ℕ) (hr : Odd r) (hpodd : Odd p)
    (h : Even ((r ^ p - 1) / 2)) : Even ((r - 1) / 2) := by
  rcases h with ⟨k, hk⟩
  have h2dvd : 2 ∣ r ^ p - 1 := by
    rcases hr.pow (n := p) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    omega
  have hmul : r ^ p - 1 = 4 * k := by
    calc
      r ^ p - 1 = 2 * ((r ^ p - 1) / 2) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel h2dvd).symm
      _ = 2 * (k + k) := by rw [hk]
      _ = 4 * k := by ring
  have hmod1 : r ^ p % 4 = 1 := by
    have hge : 1 ≤ r ^ p := by
      have hrpos : 0 < r := by
        rcases hr with ⟨m, hm⟩
        omega
      exact Nat.succ_le_of_lt (pow_pos (a := r) (n := p) hrpos)
    have hpow : r ^ p = 4 * k + 1 := by omega
    rw [hpow]
    omega
  have hmod : r ^ p % 4 = r % 4 := by
    have hsq : r ^ 2 % 4 = 1 := by
      rcases hr with ⟨n, hn⟩
      have hcalc : (2 * n + 1) ^ 2 = 4 * (n ^ 2 + n) + 1 := by ring
      rw [hn, hcalc]
      omega
    have hpowm : ∀ m : ℕ, (r ^ 2) ^ m % 4 = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, Nat.mul_mod, ih, hsq]
    rcases hpodd with ⟨m, hm⟩
    calc
      r ^ p % 4 = r ^ (2 * m + 1) % 4 := by rw [hm]
      _ = ((r ^ 2) ^ m * r) % 4 := by
        rw [pow_add, pow_mul, pow_one]
      _ = (((r ^ 2) ^ m) % 4 * (r % 4)) % 4 := by rw [Nat.mul_mod]
      _ = (1 * (r % 4)) % 4 := by rw [hpowm m]
      _ = r % 4 := by omega
  have hr1 : r % 4 = 1 := by
    rwa [hmod] at hmod1
  have hrdecomp : r = 4 * (r / 4) + 1 := by
    have hdiv : r = 4 * (r / 4) + r % 4 := (Nat.div_add_mod r 4).symm
    omega
  refine ⟨r / 4, ?_⟩
  have hnum : r - 1 = 2 * (r / 4 + r / 4) := by
    calc
      r - 1 = 4 * (r / 4) := by omega
      _ = 2 * (r / 4 + r / 4) := by ring
  rw [hnum]
  exact Nat.mul_div_right (r / 4 + r / 4) (by norm_num : 0 < 2)

set_option maxHeartbeats 8000000 in
/-- The split half of the `hU0fixed` transport: a subgroup `B` of `Kˣ`
whose split-torus image is inner and whose elements are semilinearly
conjugated by `(z, σ)` has order dividing `(|Fix σ| − 1)/2`. -/
public theorem pGammaL2_splitTorus_semilinearConjugate_fixedSubfield
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (hq14 : Even ((Nat.card K - 1) / 2))
    (z : PGL2 K)
    (B : Subgroup Kˣ)
    (hBinner : ∀ b : Kˣ, b ∈ B →
      pGammaL2FullSplitTorus K b ∈ commutator (PGL2 K))
    (hconj : ∀ b : Kˣ, b ∈ B →
      z * pGammaL2FullSplitTorus K (Units.map sigma.toRingHom b) * z⁻¹ =
        pGammaL2FullSplitTorus K b) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card B ∣ (Nat.card R - 1) / 2 := by
  classical
  let T := pGammaL2FullSplitTorus K
  have hTinj : Function.Injective T := pGammaL2FullSplitTorus_injective K
  by_cases hdiag : ∀ b : Kˣ, b ∈ B → Units.map sigma.toRingHom b = b
  · -- DIAGONAL CASE: σ fixes B pointwise
    let A : Subgroup (PGL2 K) := B.map T
    have hAtorus : A ≤ T.range := Subgroup.map_le_range T B
    have hAinner : A ≤ commutator (PGL2 K) := by
      rintro x hx
      rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hBinner b hb
    have hcommA : ∀ x : PGL2 K, x ∈ A →
        Commute (SemidirectProduct.inr sigma : PGammaL2 K)
          (SemidirectProduct.inl x) := by
      rintro x ⟨b, hb, rfl⟩
      exact pGammaL2_fullSplitTorus_sigma_commute K sigma b (hdiag b hb)
    have hdvd := pGammaL2_pureField_innerSplitTorus_fixedSubfield
      K hK hcard sigma p hp hpodd hord A hAtorus hAinner hcommA
    have hBcard : Nat.card A = Nat.card B := by
      dsimp [A]
      exact Subgroup.card_map_of_injective (f := T) (K := B) hTinj
    rwa [hBcard] at hdvd
  · -- ANTI-DIAGONAL CASE: some b₀ ∈ B is moved by σ
    have hnot' : ∃ b : Kˣ, b ∈ B ∧ Units.map sigma.toRingHom b ≠ b := by
      by_contra h
      apply hdiag
      intro b hb
      by_contra hne
      apply h
      exact ⟨b, hb, hne⟩
    rcases hnot' with ⟨b₀, hb₀B, hb₀ne⟩
    have hb0ne1 : b₀ ≠ 1 := by
      intro h
      apply hb₀ne
      rw [h]
      simp
    have hcne1 : Units.map sigma.toRingHom b₀ ≠ (1 : Kˣ) := by
      intro hc1
      apply hb0ne1
      apply Units.ext_iff.mpr
      have hval : sigma ((b₀ : K)) = (1 : K) := by
        simpa using congrArg Units.val hc1
      exact sigma.injective (by simpa using hval)
    rcases Matrix.ProjGenLinGroup.mk_surjective z with ⟨M, rfl⟩
    let α : K := (M : Matrix (Fin 2) (Fin 2) K) 0 0
    let β : K := (M : Matrix (Fin 2) (Fin 2) K) 0 1
    let γ : K := (M : Matrix (Fin 2) (Fin 2) K) 1 0
    let δ : K := (M : Matrix (Fin 2) (Fin 2) K) 1 1
    let c : K := sigma (b₀ : K)
    let d : K := (b₀ : K)
    rcases (mk_conj_diag_scalar_mul K M (Units.map sigma.toRingHom b₀) b₀ (by
      simpa using hconj b₀ hb₀B)) with ⟨mu₀, hmu₀Mat⟩
    have h00 : α * c = (mu₀ : K) * (d * α) := by
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) hmu₀Mat
      simpa [α, β, γ, δ, c, d, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two] using h
    have h01 : β = (mu₀ : K) * (d * β) := by
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hmu₀Mat
      simpa [α, β, γ, δ, c, d, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two] using h
    have h10 : γ * c = (mu₀ : K) * γ := by
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hmu₀Mat
      simpa [α, β, γ, δ, c, d, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two] using h
    have h11 : δ = (mu₀ : K) * δ := by
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) hmu₀Mat
      simpa [α, β, γ, δ, c, d, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two] using h
    have hdet : (M : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := M.det_ne_zero
    have hdetval : (M : Matrix (Fin 2) (Fin 2) K).det = α * δ - β * γ := by
      simp [α, β, γ, δ, Matrix.det_fin_two]
    have hcneb : c ≠ d := by
      intro h
      apply hb₀ne
      apply Units.ext_iff.mpr
      simpa [c, d] using h
    have hcne1' : c ≠ 1 := by
      intro hc1
      apply hcne1
      apply Units.ext_iff.mpr
      simpa [c] using hc1
    have hdne1 : d ≠ 1 := by
      intro hd1
      apply hb0ne1
      apply Units.ext_iff.mpr
      simpa [d] using hd1
    -- the matrix entries force z anti-diagonal: α = 0 and δ = 0
    have hα0 : α = 0 := by
      by_contra hαne0
      have hc_eq : c = (mu₀ : K) * d := by
        have h : α * c = α * ((mu₀ : K) * d) := by
          calc
            α * c = (mu₀ : K) * (d * α) := h00
            _ = α * ((mu₀ : K) * d) := by ring
        exact mul_left_cancel₀ hαne0 h
      have hμne1 : (mu₀ : K) ≠ 1 := by
        intro hμ1
        apply hcneb
        rw [hc_eq, hμ1]
        simp
      have hδ0 : δ = 0 := by
        have h : δ * (1 - (mu₀ : K)) = 0 := by
          calc
            δ * (1 - (mu₀ : K)) = δ - (mu₀ : K) * δ := by ring
            _ = 0 := by
              rw [← h11]
              ring
        exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (Ne.symm hμne1))
      have hβne0 : β ≠ 0 := by
        intro hβ0
        apply hdet
        rw [hdetval, hδ0, hβ0]
        simp
      have hγne0 : γ ≠ 0 := by
        intro hγ0
        apply hdet
        rw [hdetval, hδ0, hγ0]
        simp
      have hμd1 : (mu₀ : K) * d = 1 := by
        exact mul_left_cancel₀ hβne0 (by
          calc
            β * ((mu₀ : K) * d) = (mu₀ : K) * (d * β) := by ring
            _ = β := h01.symm
            _ = β * 1 := by simp)
      apply hcne1'
      rw [hc_eq, hμd1]
    have hδ0 : δ = 0 := by
      by_contra hδne0
      have hμ1 : (mu₀ : K) = 1 := by
        exact mul_right_cancel₀ hδne0 (by
          calc
            (mu₀ : K) * δ = δ := h11.symm
            _ = 1 * δ := by simp)
      have hα0' : α = 0 := by
        have h : α * (c - d) = 0 := by
          calc
            α * (c - d) = α * c - α * d := by ring
            _ = (mu₀ : K) * (d * α) - α * d := by rw [h00]
            _ = 0 := by
              rw [hμ1]
              ring
        exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hcneb)
      have hβne0 : β ≠ 0 := by
        intro hβ0
        apply hdet
        rw [hdetval, hα0', hβ0]
        simp
      have hd1 : d = 1 := by
        have h01' : β = d * β := by
          rw [hμ1] at h01
          simpa using h01
        exact mul_left_cancel₀ hβne0 (by
          calc
            β * d = d * β := by ring
            _ = β := h01'.symm
            _ = β * 1 := by simp)
      apply hdne1
      exact hd1
    have hβne0 : β ≠ 0 := by
      intro hβ0
      apply hdet
      rw [hdetval, hα0, hδ0, hβ0]
      simp
    have hγne0 : γ ≠ 0 := by
      intro hγ0
      apply hdet
      rw [hdetval, hα0, hδ0, hγ0]
      simp
    -- σ inverts every element of B
    have hinv : ∀ b : Kˣ, b ∈ B → Units.map sigma.toRingHom b = b⁻¹ := by
      intro b hb
      rcases (mk_conj_diag_scalar_mul K M (Units.map sigma.toRingHom b) b (by
        simpa using hconj b hb)) with ⟨mu, hmuMat⟩
      have h01b : β = (mu : K) * ((b : K) * β) := by
        have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hmuMat
        simpa [β, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two] using h
      have h10b : γ * sigma (b : K) = (mu : K) * γ := by
        have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hmuMat
        simpa [γ, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two] using h
      have hmub1 : (mu : K) * (b : K) = 1 := by
        exact mul_left_cancel₀ hβne0 (by
          calc
            β * ((mu : K) * (b : K)) = (mu : K) * ((b : K) * β) := by ring
            _ = β := h01b.symm
            _ = β * 1 := by simp)
      have hσb : sigma (b : K) = (mu : K) := by
        exact mul_left_cancel₀ hγne0 (by
          calc
            γ * sigma (b : K) = (mu : K) * γ := h10b
            _ = γ * (mu : K) := by ring)
      apply Units.ext
      have hsig : sigma (b : K) = (b : K)⁻¹ := by
        rw [hσb]
        exact eq_inv_of_mul_eq_one_right (by simpa [mul_comm] using hmub1)
      calc
        ((Units.map sigma.toRingHom b).val : K) = sigma.toRingHom (b : K) :=
          Units.coe_map _ _
        _ = sigma (b : K) := by rfl
        _ = (b : K)⁻¹ := hsig
        _ = (b⁻¹).val := (Units.val_inv_eq_inv_val b).symm
    -- every element of B is ±1
    have hBset : ∀ b : Kˣ, b ∈ B → b = 1 ∨ b = -1 := by
      intro b hb
      have hinvb : Units.map sigma.toRingHom b = b⁻¹ := hinv b hb
      let x : K := (b : K)
      have hx0 : x ≠ 0 := by
        exact Units.ne_zero b
      have hσx : sigma x = x⁻¹ := by
        simpa [x] using congrArg Units.val hinvb
      have hnotEven_p : ¬ Even p := by
        rcases hpodd with ⟨k, hk⟩
        intro hEven
        rcases hEven with ⟨m, hm⟩
        omega
      have haltp := (ringEquiv_pow_alternating K sigma x hx0 hσx p).1
      have hσpx_inv : (sigma ^ p) x = x⁻¹ := by
        simpa [hnotEven_p] using haltp
      have hσpx : (sigma ^ p) x = x := by
        have hσp : sigma ^ p = 1 := by
          simpa [hord] using pow_orderOf_eq_one sigma
        rw [hσp]
        simp
      have hxx : x = x⁻¹ := by
        calc
          x = (sigma ^ p) x := hσpx.symm
          _ = x⁻¹ := hσpx_inv
      have hxx2 : x * x = 1 := by
        calc
          x * x = x * x⁻¹ := by rw [← hxx]
          _ = 1 := by exact mul_inv_cancel₀ hx0
      have hx1 : x = 1 ∨ x = -1 := by
        have h : (x - 1) * (x + 1) = 0 := by
          calc
            (x - 1) * (x + 1) = x * x - 1 := by ring
            _ = 1 - 1 := by rw [hxx2]
            _ = 0 := by simp
        rcases mul_eq_zero.mp h with hminus | hplus
        · left
          exact sub_eq_zero.mp hminus
        · right
          exact add_eq_zero_iff_eq_neg.mp hplus
      rcases hx1 with hx1' | hxneg'
      · left
        apply Units.ext_iff.mpr
        simpa [x] using hx1'
      · right
        apply Units.ext_iff.mpr
        simpa [x] using hxneg'
    -- |B| ≤ 2
    have hBle2 : Nat.card B ≤ 2 := by
      have hBlez : B ≤ Subgroup.zpowers (-1 : Kˣ) := by
        intro b hb
        rcases hBset b hb with hb1 | hbneg
        · rw [hb1]
          exact Subgroup.one_mem _
        · rw [hbneg]
          exact Subgroup.mem_zpowers (-1 : Kˣ)
      have hzcard : Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 := by
        have hord' : orderOf (-1 : Kˣ) = 2 := by
          exact orderOf_eq_prime (x := (-1 : Kˣ)) (p := 2)
            (by ext; simp)
            (by
              intro h
              have h2 : (2 : K) = 0 := by
                have hval := congrArg (fun x : Kˣ => (x : K)) h
                have hk : (-1 : K) = (1 : K) := by simpa using hval
                calc
                  (2 : K) = (1 : K) + 1 := by norm_num
                  _ = (-1 : K) + 1 := by rw [hk]
                  _ = 0 := by simp
              have hodd : Odd (Nat.card K) := by
                rcases hK with ⟨q, n, hq, hqodd, hn, hKcard⟩
                rw [hKcard]
                exact hqodd.pow
              exact two_ne_zero_of_odd_card K hodd h2)
        simp [Nat.card_zpowers, hord']
      let e : B → Subgroup.zpowers (-1 : Kˣ) := fun b => ⟨(b : Kˣ), hBlez b.2⟩
      have heinj : Function.Injective e := by
        intro a b hab
        apply Subtype.ext
        simpa [e] using congrArg Subtype.val hab
      have hle : Nat.card B ≤ Nat.card (Subgroup.zpowers (-1 : Kˣ)) :=
        Nat.card_le_card_of_injective e heinj
      rwa [hzcard] at hle
    have hBpos : 0 < Nat.card B := by
      exact Nat.card_pos
    have hBcard : Nat.card B = 1 ∨ Nat.card B = 2 := by omega
    -- parity: r = |Fix σ| is odd, q = r^p, and 2 | (q−1)/2 gives 2 | (r−1)/2
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    let r : ℕ := Nat.card R
    have hfixedData := finiteField_primeOrder_fixedSubfield_data K hK sigma p hp hpodd hord
    have hqpow : Nat.card K = r ^ p := by simpa [r] using hfixedData.2.2
    have hrOdd : Odd r := by
      have hKodd : Odd (Nat.card K) := by
        rcases hK with ⟨q, n, hq, hqodd, hn, hKcard⟩
        rw [hKcard]
        exact hqodd.pow
      by_contra h
      have hrev : Even r := Nat.not_odd_iff_even.mp h
      have hKeven : Even (Nat.card K) := by
        rw [hqpow]
        rcases hrev with ⟨k, hk⟩
        refine ⟨k * r ^ (p - 1), ?_⟩
        have hp2 : 2 ≤ p := hp.two_le
        calc
          r ^ p = r ^ ((p - 1) + 1) := by
            congr 1
            omega
          _ = r ^ (p - 1) * r := by rw [pow_succ]
          _ = r * r ^ (p - 1) := by rw [mul_comm]
          _ = (2 * k) * r ^ (p - 1) := by rw [hk]; ring
          _ = k * r ^ (p - 1) + k * r ^ (p - 1) := by ring
      rcases hKodd with ⟨k, hk⟩
      rcases hKeven with ⟨m, hm⟩
      omega
    have hparity : Even ((r - 1) / 2) := splitHalf_parity r p hrOdd hpodd (by
      simpa [r, hqpow] using hq14)
    rcases hBcard with hB1 | hB2
    · rw [hB1]
      exact one_dvd _
    · rw [hB2]
      simpa [r] using (even_iff_two_dvd.mp hparity)

end CFSG.GorensteinWalter
