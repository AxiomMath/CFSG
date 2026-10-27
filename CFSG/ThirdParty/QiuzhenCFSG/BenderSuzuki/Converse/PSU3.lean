module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace Converse

open PFchapter1section1 PFAppendixIII Matrix MatrixGroups
open scoped LinearAlgebra.Projectivization Matrix

universe u

/-! ### The field `GF(q²)` with its order-two automorphism -/

/-- The field `GF(2^(2k))`, which is `GF(q²)` for `q = 2ᵏ`. -/
public abbrev UField (k : ℕ) : Type := BinaryGaloisField (2 * k)

public theorem card_UField (k : ℕ) (hk : k ≠ 0) :
    Nat.card (UField k) = (2 ^ k) ^ 2 := by
  rw [UField, GaloisField.card 2 (2 * k) (by omega), ← pow_mul]
  ring_nf

/-- The field involution `x ↦ x^q` of `GF(q²)`. -/
public noncomputable def uconj (k : ℕ) : UField k ≃+* UField k :=
  iterateFrobeniusEquiv (UField k) 2 k

public theorem uconj_apply (k : ℕ) (x : UField k) : uconj k x = x ^ (2 ^ k) :=
  iterateFrobeniusEquiv_def (UField k) 2 k x

public theorem uconj_involutive (k : ℕ) (hk : k ≠ 0) :
    Function.Involutive (uconj k) := by
  intro x
  rw [uconj_apply, uconj_apply, ← pow_mul, ← pow_add]
  have hcard : Nat.card (UField k) = 2 ^ (2 * k) := GaloisField.card 2 (2 * k) (by omega)
  haveI : Fintype (UField k) := Fintype.ofFinite _
  have h : Fintype.card (UField k) = 2 ^ (2 * k) := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have := FiniteField.pow_card x
  rw [h] at this
  have hexp : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← pow_add]; ring_nf
  rw [show k + k = 2 * k by ring]
  exact this

/-! ### The fixed field has `q` elements -/

open Polynomial in
public theorem card_fixed_UField (k : ℕ) (hk : k ≠ 0) :
    Nat.card {x : UField k // uconj k x = x} = 2 ^ k := by
  classical
  haveI : Fintype (UField k) := Fintype.ofFinite _
  have hq1 : 1 < 2 ^ k := Nat.one_lt_two_pow hk
  have hcardK : Fintype.card (UField k) = (2 ^ k) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact card_UField k hk
  set f : (UField k)[X] := X ^ (2 ^ k) - X with hfdef
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (UField k) hq1
  have hdeg : f.natDegree = 2 ^ k :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (UField k) hq1
  -- `f` divides `X^|K| - X`, because `f ^ q + f = X ^ (q^2) - X` in characteristic two.
  have hbig : f ^ (2 ^ k) + f = X ^ Fintype.card (UField k) - X := by
    have hpow : f ^ (2 ^ k) = X ^ ((2 ^ k) ^ 2) - X ^ (2 ^ k) := by
      rw [hfdef, sub_pow_char_pow (p := 2) (n := k), ← pow_mul, ← pow_two]
    rw [hpow, hcardK]
    ring
  have hdvd : f ∣ (X ^ Fintype.card (UField k) - X : (UField k)[X]) := by
    rw [← hbig]
    exact dvd_add (dvd_pow_self f (by positivity)) dvd_rfl
  -- hence `f` splits and has exactly `q` distinct roots
  have hbigsplits : (X ^ Fintype.card (UField k) - X : (UField k)[X]).Splits := by
    rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq _ Fintype.one_lt_card]
    simp
  have hsplits : f.Splits :=
    hbigsplits.of_dvd
      (FiniteField.X_pow_card_sub_X_ne_zero (UField k) Fintype.one_lt_card) hdvd
  have hcardroots : Multiset.card f.roots = 2 ^ k := by
    rw [← hdeg]; exact Polynomial.splits_iff_card_roots.1 hsplits
  have hnodup : f.roots.Nodup := Polynomial.nodup_roots (galois_poly_separable 2 (2 ^ k) ⟨2 ^ (k-1), by
    rw [← pow_succ']; congr 1; omega⟩)
  -- identify the fixed points with the roots
  have hmem : ∀ x : UField k, uconj k x = x ↔ x ∈ f.roots := by
    intro x
    rw [Polynomial.mem_roots hf0, uconj_apply, hfdef]
    simp [Polynomial.IsRoot, sub_eq_zero]
  have : {x : UField k // uconj k x = x} ≃ {x : UField k // x ∈ f.roots.toFinset} :=
    Equiv.subtypeEquivRight (by intro x; rw [Multiset.mem_toFinset]; exact hmem x)
  rw [Nat.card_congr this, Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup hnodup, hcardroots]

/-! ### The standard Hermitian form on `GF(q²)³` -/

section Form

variable (k : ℕ) [NeZero k]

public theorem k_ne_zero : k ≠ 0 := NeZero.ne k

/-- The standard nondegenerate Hermitian form with Gram matrix the antidiagonal. -/
@[expose] public noncomputable def uform : HermitianForm 3 (UField k) where
  conj := uconj k
  conj_involutive := uconj_involutive k (k_ne_zero k)
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by
    simp [Matrix.det_fin_three]

@[simp] public theorem uform_conj : (uform k).conj = uconj k := rfl

@[simp] public theorem uform_form :
    (uform k).form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

/-- `PSU₃(q)` for `q = 2ᵏ`. -/
public noncomputable abbrev PSU3 := ProjectiveSpecialUnitaryMatrixGroup (uform k)

end Form

/-! ### The general setting: an arbitrary Hermitian form of the standard shape -/

section General

variable {K : Type u} [Field K] [Finite K]

/-- A finite field of order a power of two has characteristic two. -/
public theorem charP_two_of_card {n : ℕ} (_hn : n ≠ 0) (hcard : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite _
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hprime : Nat.Prime p := CharP.char_is_prime K p
  haveI : Fact (Nat.Prime p) := ⟨hprime⟩
  obtain ⟨m, -, hcardp⟩ := FiniteField.card K p
  have hcard' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hpd : p ∣ 2 ^ n := by
    rw [← hcard', hcardp]
    exact dvd_pow_self p m.2.ne'
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 (hprime.dvd_of_dvd_pow hpd)
  subst hp2
  exact hp

variable (J : HermitianForm 3 K)

public instance finite_projGenLin : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
  Quotient.finite _

/-- The projective plane. -/
public abbrev psuP (K : Type u) [Field K] := ℙ K (Fin 3 → K)

/-- The isotropic points of the Hermitian form `J`. -/
public abbrev psuA : Set (psuP K) :=
  {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

/-- The isotropic points of `J`, as a type: the set on which `PSU₃` acts doubly
transitively. -/
public abbrev psuOmega := {x : psuP K // x ∈ psuA J}

/-! #### A Klein four subgroup inside the root group -/

section Roots

variable [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- Root-group coordinates of a central root element. -/
public noncomputable def psuRootCoord (c : K) (hc : J.conj c = c) :
    External.hermitianUnipotentCoord J :=
  ⟨(0, c), by
    show c + J.conj c + 0 * J.conj 0 = 0
    rw [hc, zero_mul, add_zero, CharTwo.add_self_eq_zero]⟩

/-- The central root element with parameter `c` in the fixed field. -/
public noncomputable def psuRoot (c : K) (hc : J.conj c = c) :
    ProjectiveSpecialUnitaryMatrixGroup J :=
  External.hermitianUnipotentPSU J hJ (psuRootCoord J c hc)

omit [Finite K] [CharP K 2] in
public theorem coord_mul_val (z w : External.hermitianUnipotentCoord J) :
    (z * w : External.hermitianUnipotentCoord J).1 =
      (z.1.1 + w.1.1, z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1) := rfl

omit [Finite K] [CharP K 2] in
public theorem coord_one_val :
    (1 : External.hermitianUnipotentCoord J).1 = (0, 0) := rfl

omit [Finite K] in
public theorem psuRootCoord_mul (c d : K) (hc : J.conj c = c) (hd : J.conj d = d) :
    psuRootCoord J c hc * psuRootCoord J d hd =
      psuRootCoord J (c + d) (by rw [map_add, hc, hd]) := by
  apply Subtype.ext
  rw [coord_mul_val]
  simp [psuRootCoord]

omit [Finite K] in
public theorem psuRootCoord_one : psuRootCoord J 0 (map_zero _) = 1 := by
  apply Subtype.ext
  rw [coord_one_val]
  rfl

omit [Finite K] in
public theorem psuRoot_mul (c d : K) (hc : J.conj c = c) (hd : J.conj d = d) :
    psuRoot J hJ c hc * psuRoot J hJ d hd =
      psuRoot J hJ (c + d) (by rw [map_add, hc, hd]) := by
  rw [psuRoot, psuRoot, psuRoot, ← map_mul, psuRootCoord_mul]

omit [Finite K] in
public theorem psuRoot_zero : psuRoot J hJ 0 (map_zero _) = 1 := by
  rw [psuRoot, psuRootCoord_one, map_one]

omit [Finite K] in
public theorem psuRoot_congr (c d : K) (hc : J.conj c = c) (hd : J.conj d = d)
    (h : c = d) : psuRoot J hJ c hc = psuRoot J hJ d hd := by
  subst h; rfl

omit [Finite K] in
public theorem psuRoot_sq (c : K) (hc : J.conj c = c) :
    psuRoot J hJ c hc * psuRoot J hJ c hc = 1 := by
  rw [psuRoot_mul]
  exact (psuRoot_congr J hJ _ 0 _ (map_zero _) (CharTwo.add_self_eq_zero c)).trans
    (psuRoot_zero J hJ)

omit [Finite K] [CharP K 2] in
/-- The projective root homomorphism is injective. -/
public theorem hUPSU_injective :
    Function.Injective (External.hermitianUnipotentPSU J hJ) := by
  intro z w h
  have hmk : Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z) =
      Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J w) := by
    rw [← External.hermitianUnipotentPSU_val J hJ,
      ← External.hermitianUnipotentPSU_val J hJ, h]
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hmk
  obtain ⟨u, hu⟩ := hmk
  have hent : ∀ i j, (External.hermitianUnipotentGL J z :
      Matrix (Fin 3) (Fin 3) K) i j * (u : K) =
      (External.hermitianUnipotentGL J w :
        Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    have := congrFun (congrFun (congrArg (fun M : GL (Fin 3) K =>
      (M : Matrix (Fin 3) (Fin 3) K)) hu) i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar,
      Matrix.diagonal, Matrix.one_apply] using this
  have h00 := hent 0 0
  have h01 := hent 0 1
  have h02 := hent 0 2
  simp [External.hermitianUnipotentGL, External.hermitianUnipotentMatrix] at h00 h01 h02
  rw [h00] at h01 h02
  apply Subtype.ext
  apply Prod.ext
  · simpa using h01
  · simpa using h02

omit [Finite K] in
public theorem psuRoot_injective (c d : K) (hc : J.conj c = c)
    (hd : J.conj d = d) (h : psuRoot J hJ c hc = psuRoot J hJ d hd) : c = d := by
  have h1 := hUPSU_injective J hJ h
  have h2 := congrArg (fun z : External.hermitianUnipotentCoord J => z.1.2) h1
  simpa [psuRootCoord] using h2

/-- The fixed field, as a subtype. -/
public abbrev psuFix := {c : K // J.conj c = c}

/-- The root element attached to a fixed-field parameter. -/
public noncomputable def psuRootF (z : psuFix J) :
    ProjectiveSpecialUnitaryMatrixGroup J := psuRoot J hJ z.1 z.2

omit [Finite K] in
public theorem psuRootF_injective : Function.Injective (psuRootF J hJ) := by
  intro z w h
  exact Subtype.ext (psuRoot_injective J hJ z.1 w.1 z.2 w.2 h)

/-- The Klein four subgroup of `PSU₃(q)` spanned by two central root elements. -/
public noncomputable def psuKlein (a b : K) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) where
  carrier := psuRootF J hJ '' {z : psuFix J | (z : K) ∈ kleinCarrier a b}
  mul_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨⟨(z : K) + w, by rw [map_add, z.2, w.2]⟩,
      kleinCarrier_add hz hw, (psuRoot_mul J hJ z.1 w.1 z.2 w.2).symm⟩
  one_mem' :=
    ⟨⟨0, map_zero _⟩, by simp [kleinCarrier], (psuRoot_zero J hJ)⟩
  inv_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [eq_comm, inv_eq_iff_mul_eq_one]
    exact psuRoot_sq J hJ z.1 z.2

omit [Finite K] in
public theorem psuKlein_card (a b : K) (ha : J.conj a = a) (hb : J.conj b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    Nat.card (psuKlein J hJ a b) = 4 := by
  show (psuRootF J hJ '' {z : psuFix J | (z : K) ∈ kleinCarrier a b}).ncard = 4
  rw [Set.ncard_image_of_injective _ (psuRootF_injective J hJ)]
  have himg : Subtype.val '' {z : psuFix J | (z : K) ∈ kleinCarrier a b} =
      kleinCarrier a b := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hc
      have hfix : J.conj c = c := by
        simp only [kleinCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact map_zero _
        · exact ha
        · exact hb
        · rw [map_add, ha, hb]
      exact ⟨⟨c, hfix⟩, hc, rfl⟩
  have h := congrArg Set.ncard himg
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at h
  rw [h, kleinCarrier_ncard ha0 hb0 hab]

omit [Finite K] in
public theorem psuKlein_sq (a b : K) (g : psuKlein J hJ a b) :
    (g : psuKlein J hJ a b) ^ 2 = 1 := by
  obtain ⟨_, z, _, rfl⟩ := g
  apply Subtype.ext
  rw [Subgroup.coe_pow, sq]
  exact psuRoot_sq J hJ z.1 z.2

omit [CharP K 2] in
public theorem exists_fixed_ne_zero_one (h4 : 4 ≤ Nat.card (psuFix J)) :
    ∃ b : K, J.conj b = b ∧ b ≠ 0 ∧ b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : {x : K | J.conj x = x} ⊆ ({0, 1} : Set K) := by
    intro x hx
    rcases eq_or_ne x 0 with h | h
    · exact Or.inl h
    · exact Or.inr (hcon x hx h)
  have hle : Nat.card (psuFix J) ≤ 2 := by
    have h1 : ({x : K | J.conj x = x}).ncard ≤ ({0, 1} : Set K).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({0, 1} : Set K).ncard ≤ 2 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      simp
    exact le_trans h1 h2
  omega

include hJ in
/-- `PSU₃(q)` has 2-rank at least two as soon as the fixed field has at least four
elements. -/
public theorem twoRank_psu3 (h4 : 4 ≤ Nat.card (psuFix J)) :
    TwoRankAtLeastTwo (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨b, hbfix, hb0, hb1⟩ := exists_fixed_ne_zero_one J h4
  exact ⟨psuKlein J hJ 1 b,
    psuKlein_card J hJ 1 b (map_one _) hbfix one_ne_zero hb0 (Ne.symm hb1),
    psuKlein_sq J hJ 1 b⟩

end Roots

/-! #### Hypothesis (A) for `PSU₃(q)` -/

open scoped Pointwise in
/-- **Converse to the Suzuki theorem, general `PSU₃` case.**  Let `J` be a Hermitian
form of the standard shape over a finite field with `q²` elements whose fixed field
has `q > 2` elements, `q` a power of two, and let `rho` be a permutation
representation of `PSU₃(J)` on the isotropic points implementing the linear action.
Then `PSU₃(J)` satisfies Hypothesis (A) for that action, with `|Q| = q³`. -/
public theorem hypothesisA_psu3_general
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q)
    (hq : 2 < q) (hq2 : ∃ n : ℕ, q = 2 ^ n)
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (psuOmega J))
    (hrho : ∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (z : psuOmega J)
        (M : J.specialSubgroup),
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : psuOmega J) : psuP K) =
            (Matrix.GeneralLinearGroup.toLin
              (M : GL (Fin 3) K)).toLinearEquiv • (z : psuP K)) :
    ∃ (H D Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (t : ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card Q = q ^ 3 ∧
        @HypothesisA _ (psuOmega J) _ _ (MulAction.compHom _ rho) _ H D Q t := by
  classical
  obtain ⟨n, rfl⟩ := hq2
  have hn2 : 2 ≤ n := by
    by_contra hcon
    interval_cases n <;> simp_all
  haveI : CharP K 2 :=
    charP_two_of_card (n := 2 * n) (by omega) (by rw [hKcard, ← pow_mul]; ring_nf)
  have hq4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hcard, rho₀, pinf, hinj, happly, hUcard, ⟨R, H₀, hRle, hH₀le, hUnorm, hRinf,
    hRsup, -, hRcard, -, -, -, hreg, -⟩, htwo, -⟩ :=
    External.huppert_II_10_12 J (2 ^ n) hKcard hfix hJ
  -- the given representation is the one produced by Huppert II.10.12
  have hEq : rho = rho₀ := by
    refine MonoidHom.ext (fun g => Equiv.ext (fun z => Subtype.ext ?_))
    obtain ⟨M, hM, hMg⟩ := g.2
    rw [hrho g z ⟨M, hM⟩ hMg]
    exact (happly g z ⟨M, hM⟩ hMg).symm
  subst hEq
  letI act : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (psuOmega J) :=
    MulAction.compHom _ rho
  have hsmul : ∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (x : psuOmega J),
      g • x = rho g x := fun _ _ => rfl
  have hone : ∀ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (y : psuOmega J),
      rho ((1 : S) : ProjectiveSpecialUnitaryMatrixGroup J) y = y := by
    intro S y
    have h1 : ((1 : S) : ProjectiveSpecialUnitaryMatrixGroup J) = 1 := rfl
    rw [h1, map_one]
    rfl
  set U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAction.stabilizer (Equiv.Perm (psuOmega J)) pinf).comap rho with hUdef
  have hmemU : ∀ g, g ∈ U ↔ rho g pinf = pinf := fun _ => Iff.rfl
  have hUstab : U = MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf := rfl
  -- a second point
  have hnontriv : ∃ p : psuOmega J, p ≠ pinf := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card (psuOmega J) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨pinf⟩⟩
    rw [hcard] at h1
    have : (0 : ℕ) < (2 ^ n) ^ 3 := by positivity
    omega
  obtain ⟨p₁, hp₁⟩ := hnontriv
  obtain ⟨g₀, hg₀, -⟩ := htwo pinf p₁ p₁ pinf (Ne.symm hp₁) hp₁
  have hg₀inv : rho g₀⁻¹ pinf ≠ pinf := by
    intro h
    apply hp₁
    have h2 := congrArg (rho g₀) h
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply, hg₀] at h2
    exact h2.symm
  -- an involution in `R`, conjugated out of the stabilizer
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hReven : 2 ∣ Nat.card R := by
    rw [hRcard, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hReven
  set t : ProjectiveSpecialUnitaryMatrixGroup J :=
    g₀ * (s : ProjectiveSpecialUnitaryMatrixGroup J) * g₀⁻¹ with htdef
  have hsne : (s : ProjectiveSpecialUnitaryMatrixGroup J) ≠ 1 := by
    intro h
    rw [show s = 1 from Subtype.ext h, orderOf_one] at hs
    omega
  have hssq : (s : ProjectiveSpecialUnitaryMatrixGroup J) ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs] at this
    exact congrArg Subtype.val this
  have htinv : IsInvolution t := by
    constructor
    · intro h
      apply hsne
      have hst : (s : ProjectiveSpecialUnitaryMatrixGroup J) = g₀⁻¹ * t * g₀ := by
        rw [htdef]; group
      rw [hst, h]; group
    · rw [htdef]
      have hsq : (g₀ * (s : ProjectiveSpecialUnitaryMatrixGroup J) * g₀⁻¹) ^ 2 =
          g₀ * (s : ProjectiveSpecialUnitaryMatrixGroup J) ^ 2 * g₀⁻¹ := by
        rw [sq, sq]; group
      rw [hsq, hssq]; group
  have htsq : t * t = 1 := by have := htinv.2; rwa [sq] at this
  have htinv' : t⁻¹ = t := inv_eq_of_mul_eq_one_left htsq
  -- `t` moves `pinf`
  have htnotU : t ∉ U := by
    rw [hmemU]
    intro hfix
    apply hsne
    have hsfix : rho (s : ProjectiveSpecialUnitaryMatrixGroup J) (rho g₀⁻¹ pinf) =
        rho g₀⁻¹ pinf := by
      have hgs : rho g₀ (rho (s : ProjectiveSpecialUnitaryMatrixGroup J)
          (rho g₀⁻¹ pinf)) = pinf := by
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, ← htdef]
        exact hfix
      have hinj' : Function.Injective (rho g₀) := (rho g₀).injective
      apply hinj'
      rw [hgs, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Equiv.Perm.one_apply]
    obtain ⟨w, -, huniq⟩ := hreg (rho g₀⁻¹ pinf) (rho g₀⁻¹ pinf) hg₀inv hg₀inv
    have h1 := huniq s hsfix
    have h2 := huniq 1 (hone R _)
    exact congrArg Subtype.val (h1.trans h2.symm)
  set p₀ : psuOmega J := t • pinf with hp₀def
  have hp₀ne : p₀ ≠ pinf := by
    intro h
    exact htnotU ((hmemU t).2 (by rw [← hsmul]; exact h))
  set D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := U ⊓ rightConjugate U t with hDdef
  have hDeq : D = U ⊓ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) p₀ := by
    rw [hDdef, hUstab, rightConjugate_stabilizer, htinv', hp₀def]
  have hmemD : ∀ g, g ∈ D ↔ (rho g pinf = pinf ∧ rho g p₀ = p₀) := by
    intro g
    rw [hDeq, Subgroup.mem_inf, hmemU, MulAction.mem_stabilizer_iff, hsmul]
  -- the factorisation `U = R · D`
  have hmulapp : ∀ (g h : ProjectiveSpecialUnitaryMatrixGroup J) (x : psuOmega J),
      rho (g * h) x = rho g (rho h x) := by
    intro g h x; rw [map_mul]; rfl
  have hinvapp : ∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (x y : psuOmega J),
      rho g x = y → rho g⁻¹ y = x := by
    intro g x y hxy
    rw [← hxy, ← hmulapp, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  have hDleU : D ≤ U := by rw [hDdef]; exact inf_le_left
  have hUinv : ∀ u, u ∈ U → rho u⁻¹ pinf = pinf := fun u hu =>
    hinvapp u pinf pinf ((hmemU u).1 hu)
  have hfact : ∀ u, u ∈ U → ∃ r ∈ R, ∃ d ∈ D, u = r * d := by
    intro u hu
    have hup₀ : rho u p₀ ≠ pinf := by
      intro h
      apply hp₀ne
      rw [← hinvapp u p₀ pinf h, hUinv u hu]
    obtain ⟨r, hr, -⟩ := hreg p₀ (rho u p₀) hp₀ne hup₀
    refine ⟨(r : ProjectiveSpecialUnitaryMatrixGroup J), r.2,
      (r : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u, ?_, by group⟩
    rw [hmemD]
    refine ⟨?_, ?_⟩
    · rw [hmulapp, (hmemU u).1 hu, hUinv _ (hRle r.2)]
    · rw [hmulapp, ← hr, hinvapp _ p₀ _ rfl]
  have hRsupD : R ⊔ D = U := by
    refine le_antisymm (sup_le hRle hDleU) ?_
    intro u hu
    obtain ⟨r, hr, d, hd, rfl⟩ := hfact u hu
    exact Subgroup.mul_mem_sup hr hd
  have hRdisjD : Disjoint R D := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxD
    rw [hmemD] at hxD
    obtain ⟨w, -, huniq⟩ := hreg p₀ p₀ hp₀ne hp₀ne
    have h1 := huniq ⟨x, hxR⟩ hxD.2
    have h2 := huniq 1 (hone R _)
    exact congrArg Subtype.val (h1.trans h2.symm)
  -- cardinalities
  have hRD : Nat.card R * Nat.card D = Nat.card U := by
    have hdisj' : Disjoint (R.subgroupOf U) (D.subgroupOf U) := by
      rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      rw [Subgroup.mem_subgroupOf] at hx1 hx2
      exact Subtype.ext ((Subgroup.disjoint_def.1 hRdisjD) hx1 hx2)
    have hmul' : (↑(R.subgroupOf U) : Set U) * (↑(D.subgroupOf U) : Set U) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro u
      obtain ⟨r, hr, d, hd, hud⟩ := hfact (u : ProjectiveSpecialUnitaryMatrixGroup J) u.2
      exact ⟨⟨r, hRle hr⟩, hr, ⟨d, hDleU hd⟩, hd, Subtype.ext hud.symm⟩
    have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hmul'
    have hc := hcompl.card_mul
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleU).toEquiv] at hc
  have hgcddvd : Nat.gcd (2 ^ n + 1) 3 ∣ (2 ^ n) ^ 2 - 1 := by
    refine dvd_trans (Nat.gcd_dvd_left _ _) ⟨2 ^ n - 1, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ n = j + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hj]
    have h1 : (j + 1) ^ 2 = j * j + 2 * j + 1 := by ring
    have h2 : (j + 1 + 1) * (j + 1 - 1) = j * j + 2 * j := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [h1, h2, Nat.add_sub_cancel]
  have hUcard' : Nat.card U =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3) := by
    rw [hUcard, Nat.mul_div_assoc _ hgcddvd]
  have hDcard : Nat.card D = ((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3 := by
    have h3 : (0 : ℕ) < (2 ^ n) ^ 3 := by positivity
    have h := hRD
    rw [hRcard, hUcard'] at h
    exact Nat.eq_of_mul_eq_mul_left h3 h
  have hodd21 : Odd ((2 ^ n) ^ 2 - 1) := by
    refine Nat.Even.sub_odd (by nlinarith) ?_ odd_one
    rw [← pow_mul]
    exact (Nat.even_pow' (by omega)).2 even_two
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    obtain ⟨c, hc⟩ : (((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3) ∣ (2 ^ n) ^ 2 - 1 :=
      Nat.div_dvd_of_dvd hgcddvd
    rw [hc, Nat.odd_mul] at hodd21
    exact hodd21.1
  -- assemble
  refine ⟨U, D, R, t, hRcard, ?_⟩
  refine { A1 := ?_, A2 := ?_, A3 := twoRank_psu3 J hJ (by rw [hfix]; exact hq4) }
  · exact
      { two_transitive := by
          rw [MulAction.is_two_pretransitive_iff]
          intro a b c d hab hcd
          obtain ⟨g, h1, h2⟩ := htwo a b c d hab hcd
          exact ⟨g, by rw [hsmul]; exact h1, by rw [hsmul]; exact h2⟩
        point_stabilizer := ⟨pinf, hUstab⟩
        involution_t := htinv
        t_not_mem_H := htnotU
        D_eq := hDdef
        Q_le_H := hRle
        D_le_H := hDleU
        Q_normal_in_H := Subgroup.normal_subgroupOf_of_le_normalizer hUnorm
        Q_disjoint_D := hRdisjD
        Q_sup_D := hRsupD
        Q_even := by
          rw [hRcard, ← pow_mul]
          exact (Nat.even_pow' (by omega)).2 even_two
        D_odd := hDodd }
  · exact ⟨fun {g₁ g₂} h => hinj (Equiv.ext fun x => by
      have := h x
      rwa [hsmul, hsmul] at this)⟩

end General

/-! ### Hypothesis (A) for the concrete groups `PSU₃(2ᵏ)` -/

section Main

variable (k : ℕ) [NeZero k]

/-- The projective plane over `GF(q²)`. -/
public abbrev UP := psuP (UField k)

/-- The isotropic points of the Hermitian form. -/
public abbrev UA : Set (UP k) := psuA (uform k)

/-- The `q³ + 1` isotropic points, on which `PSU₃(q)` acts doubly transitively. -/
public abbrev UOmega := psuOmega (uform k)

/-- **Converse to the Suzuki theorem, `PSU₃` case.**  For every `k ≥ 2` the group
`PSU₃(2ᵏ)`, acting on the isotropic points of the standard Hermitian form over
`GF(2²ᵏ)`, satisfies Hypothesis (A) of Peterfalvi Part II. -/
public theorem hypothesisA_PSU3 (hk : 2 ≤ k) :
    ∃ (act : MulAction (PSU3 k) (UOmega k)) (H D Q : Subgroup (PSU3 k)) (t : PSU3 k),
      @HypothesisA (PSU3 k) (UOmega k) _ _ act _ H D Q t := by
  obtain ⟨-, rho, -, -, happly, -⟩ :=
    External.huppert_II_10_12 (uform k) (2 ^ k)
      (card_UField k (k_ne_zero k)) (card_fixed_UField k (k_ne_zero k)) rfl
  obtain ⟨H, D, Q, t, -, hA⟩ :=
    hypothesisA_psu3_general (uform k) rfl (2 ^ k)
      (card_UField k (k_ne_zero k)) (card_fixed_UField k (k_ne_zero k))
      (by
        calc (2 : ℕ) < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
      ⟨k, rfl⟩ rho happly
  exact ⟨_, H, D, Q, t, hA⟩

end Main

end Converse
end CFSG.BenderSuzuki
