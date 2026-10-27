module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.3.1

The statement follows Volume III, physical pages 190-191.  The matrices are
written in the transposed upper-triangular convention used by
`MatrixGroups.Suzuki`.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open PFAppendixIII
open scoped commutatorElement

private abbrev lowerCentralSeries (H : Type*) [Group H] : ℕ → Subgroup H :=
  (⊤ : Subgroup H).lowerCentralSeries


/-- The square root of Frobenius in the automorphism group of
`GF(2^(2m+1))` is unique. -/
private theorem binaryGaloisField_tits_square_root_unique
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    ∀ sigma : BinaryGaloisField (2 * m + 1) ≃+*
        BinaryGaloisField (2 * m + 1),
      (∀ x, sigma (sigma x) = x ^ 2) → sigma = pi := by
  let K := BinaryGaloisField (2 * m + 1)
  let toAlg : (K ≃+* K) → (K ≃ₐ[ZMod 2] K) := fun e =>
    AlgEquiv.ofRingEquiv (f := e) (fun x => by
      have hcomp : e.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  have hn : 2 * m + 1 ≠ 0 := by omega
  have hcardAut : Nat.card (K ≃ₐ[ZMod 2] K) = 2 * m + 1 := by
    calc
      Nat.card (K ≃ₐ[ZMod 2] K) = Module.finrank (ZMod 2) K :=
        IsGalois.card_aut_eq_finrank (ZMod 2) K
      _ = 2 * m + 1 := by
        simpa [K, BinaryGaloisField] using GaloisField.finrank 2 hn
  have hodd : Odd (Nat.card (K ≃ₐ[ZMod 2] K)) := by
    rw [hcardAut]
    exact ⟨m, by omega⟩
  have hinj : Function.Injective (fun e : K ≃ₐ[ZMod 2] K => e ^ 2) :=
    hodd.coprime_two_right.pow_left_bijective.injective
  intro sigma hsigma_sq
  have hAlg : toAlg sigma = toAlg pi := by
    apply hinj
    ext x
    change sigma (sigma x) = pi (pi x)
    rw [hsigma_sq, hpi_sq]
  apply RingEquiv.ext
  intro x
  exact DFunLike.congr_fun hAlg x

/-- The unique square root of Frobenius on `GF(2^(2m+1))` is the
`(m+1)`-fold Frobenius. -/
private theorem binaryGaloisField_tits_automorphism_apply
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    ∀ x, pi x = x ^ (2 ^ (m + 1)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let sigma : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hsigma_formula : ∀ x : K, sigma x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hsigma_sq : ∀ x : K, sigma (sigma x) = x ^ 2 := by
    intro x
    let _ : Fintype K := Fintype.ofFinite K
    calc
      sigma (sigma x) = (sigma x) ^ (2 ^ (m + 1)) :=
        hsigma_formula (sigma x)
      _ = (x ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) := by
        rw [hsigma_formula]
      _ = x ^ (2 ^ (m + 1 + (m + 1))) := by
        rw [← pow_mul, ← pow_add]
      _ = x ^ (2 ^ ((2 * m + 1) + 1)) := by
        congr 2
        omega
      _ = (x ^ (2 ^ (2 * m + 1))) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ = x ^ 2 := by
        have hx_card : x ^ Nat.card K = x := by
          rw [← Fintype.card_eq_nat_card]
          exact FiniteField.pow_card x
        rw [← hK_card, hx_card]
  have hsigma_eq : sigma = pi :=
    binaryGaloisField_tits_square_root_unique m hm pi hpi_sq sigma hsigma_sq
  intro x
  rw [← hsigma_eq]
  exact hsigma_formula x

/-- The zero Suzuki root coordinates give the identity matrix. -/
public theorem suzukiRootGL_zero_zero (m : ℕ) :
    SuzukiRootGL m 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix]

/-- Suzuki root coordinates are determined by their matrix. -/
private theorem suzukiRootGL_injective
    (m : ℕ) (a b a' b' : BinaryGaloisField (2 * m + 1))
    (h : SuzukiRootGL m a b = SuzukiRootGL m a' b') :
    a = a' ∧ b = b' := by
  constructor
  · have h01 := congrArg
      (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
        ((A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)))
          0 1)) h
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h01
  · have h02 := congrArg
      (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
        ((A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)))
          0 2)) h
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h02

/-- The multiplication formula for the Suzuki root matrices. -/
private theorem suzukiRootGL_mul
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b a' b' : BinaryGaloisField (2 * m + 1)) :
    SuzukiRootGL m a b * SuzukiRootGL m a' b' =
      SuzukiRootGL m (a + a') (b + b' + a * pi a') := by
  have hpow (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (2 ^ (m + 1)) = pi x := (hpi_formula x).symm
  have hpow_one (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (1 + 2 ^ (m + 1)) = x * pi x := by
    rw [pow_add, hpow, pow_one]
  have hpow_two (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (2 + 2 ^ (m + 1)) = x ^ 2 * pi x := by
    rw [pow_add, hpow]
  have htwo : (2 : BinaryGaloisField (2 * m + 1)) = 0 :=
    CharP.cast_eq_zero _ 2
  have hthree : (3 : BinaryGaloisField (2 * m + 1)) = 1 := by
    calc
      (3 : BinaryGaloisField (2 * m + 1)) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, CharTwo.add_self_eq_zero]
  all_goals (try rw [hpow a'])
  all_goals (try rw [hpow a])
  all_goals (try rw [hpow (a + a')])
  all_goals (try rw [hpow b'])
  all_goals (try rw [hpow b])
  all_goals (try rw [hpow (b + b' + a * pi a')])
  all_goals (try rw [hpow_one a'])
  all_goals (try rw [hpow_one a])
  all_goals (try rw [hpow_one (a + a')])
  all_goals (try rw [hpow_two a'])
  all_goals (try rw [hpow_two a])
  all_goals (try rw [hpow_two (a + a')])
  all_goals (try simp only [map_add, map_mul, hpi_sq])
  all_goals ring_nf
  all_goals simp [htwo, hthree]

/-- The inverse of a Suzuki root matrix in root coordinates. -/
public theorem suzukiRootGL_inv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    (SuzukiRootGL m a b)⁻¹ =
      SuzukiRootGL m a (b + a * pi a) := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [suzukiRootGL_mul m pi hpi_sq hpi_formula]
  have hcoord :
      b + (b + a * pi a) + a * pi a = 0 := by
    calc
      b + (b + a * pi a) + a * pi a =
          (b + b) + (a * pi a + a * pi a) := by abel
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  rw [CharTwo.add_self_eq_zero, hcoord]
  exact suzukiRootGL_zero_zero m

/-- The closure generated by Suzuki root matrices is exactly their
two-coordinate range. -/
public theorem suzukiRootGL_mem_closure_iff
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    A ∈ Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} ↔
      ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b := by
  constructor
  · intro hA
    exact Subgroup.closure_induction
      (p := fun A _ => ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b)
      (fun _ h => h)
      ⟨0, 0, (suzukiRootGL_zero_zero m).symm⟩
      (fun _ _ _ _ hx hy => by
        rcases hx with ⟨a, b, rfl⟩
        rcases hy with ⟨a', b', rfl⟩
        exact ⟨a + a', b + b' + a * pi a',
          suzukiRootGL_mul m pi hpi_sq hpi_formula a b a' b'⟩)
      (fun _ _ hx => by
        rcases hx with ⟨a, b, rfl⟩
        exact ⟨a, b + a * pi a,
          suzukiRootGL_inv m pi hpi_sq hpi_formula a b⟩)
      hA
  · rintro ⟨a, b, rfl⟩
    exact Subgroup.subset_closure ⟨a, b, rfl⟩

/-- Root coordinates give a bijection from two copies of the defining field
onto the root subgroup. -/
private noncomputable def suzukiRootCoordinatesEquiv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    (BinaryGaloisField (2 * m + 1) ×
      BinaryGaloisField (2 * m + 1)) ≃ F := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let toF :
      BinaryGaloisField (2 * m + 1) ×
        BinaryGaloisField (2 * m + 1) → F :=
    fun z => ⟨SuzukiRootGL m z.1 z.2,
      Subgroup.subset_closure ⟨z.1, z.2, rfl⟩⟩
  exact Equiv.ofBijective toF
    ⟨by
      intro z w hzw
      have hroot := suzukiRootGL_injective m z.1 z.2 w.1 w.2
        (congrArg Subtype.val hzw)
      exact Prod.ext hroot.1 hroot.2,
    by
      intro x
      rcases (suzukiRootGL_mem_closure_iff
        m pi hpi_sq hpi_formula (x : GL (Fin 4)
          (BinaryGaloisField (2 * m + 1)))).mp x.property with
        ⟨a, b, hx⟩
      refine ⟨(a, b), ?_⟩
      exact Subtype.ext hx.symm⟩

/-- Cardinality of the Suzuki root subgroup from its two field coordinates. -/
private theorem suzukiRootClosure_card
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    Nat.card
        (Subgroup.closure
          {A | ∃ a b : BinaryGaloisField (2 * m + 1),
            A = SuzukiRootGL m a b} :
          Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) =
      (2 ^ (2 * m + 1)) ^ 2 := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let e := suzukiRootCoordinatesEquiv m pi hpi_sq hpi_formula
  have hK_card :
      Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    simpa [BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  change Nat.card F = (2 ^ (2 * m + 1)) ^ 2
  calc
    Nat.card F =
        Nat.card (BinaryGaloisField (2 * m + 1) ×
          BinaryGaloisField (2 * m + 1)) :=
      Nat.card_congr e.symm
    _ = Nat.card (BinaryGaloisField (2 * m + 1)) *
        Nat.card (BinaryGaloisField (2 * m + 1)) := Nat.card_prod _ _
    _ = (2 ^ (2 * m + 1)) ^ 2 := by rw [hK_card, pow_two]

/-- The Suzuki root subgroup is a 2-group. -/
private theorem suzukiRootClosure_isPGroup
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    IsPGroup 2
      (Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} :
        Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) := by
  apply IsPGroup.of_card
    (n := (2 * m + 1) + (2 * m + 1))
  rw [suzukiRootClosure_card m pi hpi_sq hpi_formula, pow_two, ← pow_add]

/-- Squaring a Suzuki root element leaves only its central coordinate. -/
private theorem suzukiRootGL_sq
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    (SuzukiRootGL m a b) ^ 2 =
      SuzukiRootGL m 0 (a * pi a) := by
  rw [pow_two, suzukiRootGL_mul m pi hpi_sq hpi_formula]
  congr 1
  · exact CharTwo.add_self_eq_zero a
  · rw [CharTwo.add_self_eq_zero, zero_add]

/-- Every Suzuki root element has fourth power one. -/
private theorem suzukiRootGL_pow_four
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    (SuzukiRootGL m a b) ^ 4 = 1 := by
  calc
    (SuzukiRootGL m a b) ^ 4 =
        ((SuzukiRootGL m a b) ^ 2) ^ 2 := by group
    _ = (SuzukiRootGL m 0 (a * pi a)) ^ 2 := by
      rw [suzukiRootGL_sq m pi hpi_sq hpi_formula]
    _ = SuzukiRootGL m 0 0 := by
      simpa using
        suzukiRootGL_sq m pi hpi_sq hpi_formula 0 (a * pi a)
    _ = 1 := suzukiRootGL_zero_zero m

/-- The Suzuki root subgroup has exponent dividing four. -/
private theorem suzukiRootClosure_pow_four
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    ∀ x :
      (Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} :
        Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))),
      x ^ 4 = 1 := by
  intro x
  apply Subtype.ext
  change (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) ^ 4 = 1
  rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
    (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).mp x.property with
    ⟨a, b, hx⟩
  rw [hx]
  exact suzukiRootGL_pow_four m pi hpi_sq hpi_formula a b

/-- The root element with first coordinate one has order four. -/
private theorem suzukiRootClosure_exists_order_four
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    ∃ x :
      (Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} :
        Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))),
      orderOf x = 4 := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let x : F := ⟨SuzukiRootGL m 1 0,
    Subgroup.subset_closure ⟨1, 0, rfl⟩⟩
  have hx_ne : x ≠ 1 := by
    intro hx
    have hroot : SuzukiRootGL m 1 0 = SuzukiRootGL m 0 0 := by
      calc
        SuzukiRootGL m 1 0 = 1 := congrArg Subtype.val hx
        _ = SuzukiRootGL m 0 0 := (suzukiRootGL_zero_zero m).symm
    exact one_ne_zero (suzukiRootGL_injective m 1 0 0 0 hroot).1
  have hx_sq_ne : x ^ 2 ≠ 1 := by
    intro hx
    have hxval := congrArg Subtype.val hx
    have hroot_sq :
        SuzukiRootGL m 0 1 = SuzukiRootGL m 0 0 := by
      calc
        SuzukiRootGL m 0 1 =
            (SuzukiRootGL m 1 0) ^ 2 := by
          simpa using
            (suzukiRootGL_sq m pi hpi_sq hpi_formula 1 0).symm
        _ = 1 := by simpa [x] using hxval
        _ = SuzukiRootGL m 0 0 := (suzukiRootGL_zero_zero m).symm
    exact one_ne_zero (suzukiRootGL_injective m 0 1 0 0 hroot_sq).2
  refine ⟨x, (orderOf_eq_iff (by norm_num : 0 < 4)).2 ⟨
    suzukiRootClosure_pow_four m pi hpi_sq hpi_formula x, ?_⟩⟩
  intro n hn hnpos
  interval_cases n
  · simpa using hx_ne
  · simpa using hx_sq_ne
  · intro hx_three
    apply hx_ne
    calc
      x = x * 1 := by simp
      _ = x * x ^ 3 := by rw [hx_three]
      _ = x ^ 4 := by group
      _ = 1 := suzukiRootClosure_pow_four m pi hpi_sq hpi_formula x

/-- The Tits automorphism has the required odd iterate order. -/
private theorem binaryGaloisField_tits_iterate
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    ∀ x : BinaryGaloisField (2 * m + 1),
      pi^[2 * m + 1] x = x := by
  let K := BinaryGaloisField (2 * m + 1)
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hfun : (pi : K → K) = fun x => x ^ (2 ^ (m + 1)) :=
    funext hpi_formula
  have hexp :
      (2 ^ (m + 1)) ^ (2 * m + 1) =
        (2 ^ (2 * m + 1)) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  let _ : Fintype K := Fintype.ofFinite K
  have hK_fintype_card : Fintype.card K = 2 ^ (2 * m + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK_card
  intro x
  rw [hfun, pow_iterate, hexp, ← hK_fintype_card]
  exact FiniteField.pow_card_pow (m + 1) x

/-- For positive m, the Tits automorphism is nontrivial. -/
private theorem binaryGaloisField_tits_nontrivial
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    ∃ x : BinaryGaloisField (2 * m + 1), pi x ≠ x := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let _ : Fintype K := Fintype.ofFinite K
  have hK_card : Fintype.card K = 2 ^ (2 * m + 1) := by
    rw [Fintype.card_eq_nat_card]
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hcard_gt : 2 < Fintype.card K := by
    rw [hK_card]
    have hpow_lt := Nat.pow_lt_pow_right (a := 2) (by norm_num)
      (show 1 < 2 * m + 1 by omega)
    simpa using hpow_lt
  have hexists : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push Not at h
    have huniv : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [h x hx0]
    have hle : Fintype.card K ≤ 2 := by
      rw [← Finset.card_univ]
      calc
        Finset.univ.card ≤ ({0, 1} : Finset K).card :=
          Finset.card_le_card huniv
        _ = 2 := by simp
    omega
  rcases hexists with ⟨x, hx0, hx1⟩
  refine ⟨x, ?_⟩
  intro hpix
  have hsq : x ^ 2 = x := by
    calc
      x ^ 2 = pi (pi x) := (hpi_sq x).symm
      _ = x := by rw [hpix, hpix]
  have hprod : x * (x - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, hsq, sub_self]
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact hx0 hzero
  · exact hx1 (sub_eq_zero.mp hone)

/-- The explicit root coordinates satisfy the Peterfalvi Type-A axioms. -/
private theorem suzukiRootClosure_typeA
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    IsSuzukiTwoTypeA
      (Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} :
        Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) := by
  refine ⟨2 * m + 1, by omega, pi, SuzukiRootGL m,
    (fun a b => a * pi b), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨2 * m + 1, ⟨m, by omega⟩, by omega,
      binaryGaloisField_tits_iterate m hm pi hpi_formula⟩
  · exact binaryGaloisField_tits_nontrivial m hm pi hpi_sq
  · intro a b c
    dsimp
    rw [add_mul]
  · intro a b c
    dsimp
    rw [map_add, mul_add]
  · intro a
    rfl
  · intro a b
    exact Subgroup.subset_closure ⟨a, b, rfl⟩
  · exact suzukiRootGL_zero_zero m
  · intro x hx
    exact (suzukiRootGL_mem_closure_iff
      m pi hpi_sq hpi_formula x).mp hx
  · intro a b a' b' h
    exact suzukiRootGL_injective m a b a' b' h
  · exact suzukiRootGL_mul m pi hpi_sq hpi_formula

/-- Two Suzuki root elements commute exactly when their first coordinates satisfy the twisted bilinear relation. -/
private theorem suzukiRootGL_commute_iff
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b c d : BinaryGaloisField (2 * m + 1)) :
    SuzukiRootGL m a b * SuzukiRootGL m c d =
        SuzukiRootGL m c d * SuzukiRootGL m a b ↔
      a * pi c = c * pi a := by
  rw [suzukiRootGL_mul m pi hpi_sq hpi_formula,
    suzukiRootGL_mul m pi hpi_sq hpi_formula]
  constructor
  · intro h
    have hcoord := (suzukiRootGL_injective m
      (a + c) (b + d + a * pi c)
      (c + a) (d + b + c * pi a) h).2
    linear_combination hcoord
  · intro hcoord
    congr 1
    · exact add_comm a c
    · linear_combination hcoord

/-- The center of the Suzuki root subgroup consists exactly of the root elements with first coordinate zero. -/
private theorem suzukiRootClosure_mem_center_iff
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    ∀ x : F, x ∈ Subgroup.center F ↔
      ∃ b : BinaryGaloisField (2 * m + 1),
        (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m 0 b := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  change ∀ x : F, x ∈ Subgroup.center F ↔
    ∃ b : BinaryGaloisField (2 * m + 1),
      (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
        SuzukiRootGL m 0 b
  intro x
  constructor
  · intro hxcenter
    rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
      (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).mp x.property with
      ⟨a, b, hx⟩
    have hcomm (c d : BinaryGaloisField (2 * m + 1)) :
        SuzukiRootGL m a b * SuzukiRootGL m c d =
          SuzukiRootGL m c d * SuzukiRootGL m a b := by
      let y : F := ⟨SuzukiRootGL m c d,
        Subgroup.subset_closure ⟨c, d, rfl⟩⟩
      have hyx := Subgroup.mem_center_iff.mp hxcenter y
      have hyxval := congrArg Subtype.val hyx
      change SuzukiRootGL m c d * (x : GL (Fin 4)
          (BinaryGaloisField (2 * m + 1))) =
        (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) *
          SuzukiRootGL m c d at hyxval
      rw [hx] at hyxval
      exact hyxval.symm
    have ha_fixed : pi a = a := by
      have ha := (suzukiRootGL_commute_iff
        m pi hpi_sq hpi_formula a b 1 0).mp (hcomm 1 0)
      simpa using ha.symm
    rcases binaryGaloisField_tits_nontrivial m hm pi hpi_sq with ⟨c, hc⟩
    have ha_zero : a = 0 := by
      by_contra ha0
      apply hc
      apply mul_left_cancel₀ ha0
      calc
        a * pi c = c * pi a :=
          (suzukiRootGL_commute_iff
            m pi hpi_sq hpi_formula a b c 0).mp (hcomm c 0)
        _ = c * a := by rw [ha_fixed]
        _ = a * c := mul_comm c a
    exact ⟨b, by simpa [ha_zero] using hx⟩
  · rintro ⟨b, hxb⟩
    rw [Subgroup.mem_center_iff]
    intro y
    rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
      (y : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).mp y.property with
      ⟨c, d, hy⟩
    apply Subtype.ext
    change (y : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) *
        (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
      (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) *
        (y : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))
    rw [hy, hxb]
    exact ((suzukiRootGL_commute_iff
      m pi hpi_sq hpi_formula 0 b c d).2 (by simp)).symm

/-- The commutator of two Suzuki root elements has only a central coordinate. -/
private theorem suzukiRootGL_commutator
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b c d : BinaryGaloisField (2 * m + 1)) :
    ⁅SuzukiRootGL m a b, SuzukiRootGL m c d⁆ =
      SuzukiRootGL m 0 (a * pi c + c * pi a) := by
  rw [commutatorElement_def,
    suzukiRootGL_inv m pi hpi_sq hpi_formula,
    suzukiRootGL_inv m pi hpi_sq hpi_formula,
    suzukiRootGL_mul m pi hpi_sq hpi_formula,
    suzukiRootGL_mul m pi hpi_sq hpi_formula,
    suzukiRootGL_mul m pi hpi_sq hpi_formula]
  have htwo : (2 : BinaryGaloisField (2 * m + 1)) = 0 :=
    CharP.cast_eq_zero _ 2
  have hthree : (3 : BinaryGaloisField (2 * m + 1)) = 1 := by
    calc
      (3 : BinaryGaloisField (2 * m + 1)) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add 1
  congr 1
  · ring_nf
    simp [htwo]
  · ring_nf
    simp [htwo, hthree]

/-- The commutator subgroup of the Suzuki root subgroup lies in its center. -/
private theorem suzukiRootClosure_commutator_le_center
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    commutator F ≤ Subgroup.center F := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  change commutator F ≤ Subgroup.center F
  change ⁅(⊤ : Subgroup F), ⊤⁆ ≤ Subgroup.center F
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
    (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).mp x.property with
    ⟨a, b, hxab⟩
  rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
    (y : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).mp y.property with
    ⟨c, d, hycd⟩
  apply (suzukiRootClosure_mem_center_iff
    m hm pi hpi_sq hpi_formula ⁅x, y⁆).2
  refine ⟨a * pi c + c * pi a, ?_⟩
  change ⁅(x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))),
      (y : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))⁆ =
    SuzukiRootGL m 0 (a * pi c + c * pi a)
  rw [hxab, hycd]
  exact suzukiRootGL_commutator m pi hpi_sq hpi_formula a b c d

/-- The Suzuki root subgroup has nilpotency class exactly two. -/
private theorem suzukiRootClosure_nilpotencyClass
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    Group.nilpotencyClass
      (Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} :
        Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) = 2 := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  change Group.nilpotencyClass F = 2
  have hcomm_le : commutator F ≤ Subgroup.center F :=
    suzukiRootClosure_commutator_le_center
      m hm pi hpi_sq hpi_formula
  have hlower_two : lowerCentralSeries F 2 = ⊥ := by
    apply Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup F) (n := 1)
    rw [Subgroup.top_lowerCentralSeries_one]
    exact hcomm_le
  have hnil : Group.IsNilpotent F :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := F)).mpr
      ⟨2, hlower_two⟩
  let _ : Group.IsNilpotent F := hnil
  have hclass_le : Group.nilpotencyClass F ≤ 2 :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := F)).mp hlower_two
  have hclass_not_le_one : ¬ Group.nilpotencyClass F ≤ 1 := by
    intro hclass
    have hcenter_top : Subgroup.center F = ⊤ := by
      rw [← Subgroup.upperCentralSeries_one F]
      exact Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hclass
    let z : F := ⟨SuzukiRootGL m 1 0,
      Subgroup.subset_closure ⟨1, 0, rfl⟩⟩
    have hz_center : z ∈ Subgroup.center F := by
      rw [hcenter_top]
      exact Subgroup.mem_top z
    rcases (suzukiRootClosure_mem_center_iff
      m hm pi hpi_sq hpi_formula z).mp hz_center with ⟨b, hb⟩
    exact one_ne_zero (suzukiRootGL_injective m 1 0 0 b hb).1
  omega

/-- The twisted norm `a ↦ a * pi a` permutes the nonzero field elements. -/
private theorem binaryGaloisField_tits_norm_surjective
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    ∀ y : (BinaryGaloisField (2 * m + 1))ˣ,
      ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
        (x : BinaryGaloisField (2 * m + 1)) *
          pi (x : BinaryGaloisField (2 * m + 1)) =
            (y : BinaryGaloisField (2 * m + 1)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let N : Kˣ →* Kˣ :=
    { toFun := fun x => x * Units.map pi.toMonoidHom x
      map_one' := by simp
      map_mul' x y := by
        apply Units.ext
        simp only [Units.val_mul, Units.coe_map, map_mul]
        ring }
  have hN_val (x : Kˣ) :
      (N x : K) = (x : K) * pi (x : K) := rfl
  have hker : N.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxval : (x : K) * pi (x : K) = 1 := by
      rw [← hN_val]
      exact congrArg Units.val hx
    have hpi_norm := congrArg pi hxval
    simp only [map_mul, map_one, hpi_sq] at hpi_norm
    have hpix_ne : pi (x : K) ≠ 0 :=
      (map_ne_zero pi).2 x.ne_zero
    have hsquare : (x : K) ^ 2 = (x : K) := by
      apply mul_left_cancel₀ hpix_ne
      calc
        pi (x : K) * (x : K) ^ 2 = 1 := hpi_norm
        _ = pi (x : K) * (x : K) := by
          simpa [mul_comm] using hxval.symm
    apply Units.ext
    apply mul_left_cancel₀ x.ne_zero
    simpa [pow_two] using hsquare
  have hinj : Function.Injective N :=
    N.ker_eq_bot_iff.mp hker
  let _ : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hsurj : Function.Surjective N :=
    Finite.injective_iff_surjective.mp hinj
  intro y
  rcases hsurj y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [← hN_val]
  exact congrArg Units.val hx

/-- Every central root element belongs to the commutator subgroup. -/
private theorem suzukiRootClosure_center_le_commutator
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    Subgroup.center F ≤ commutator F := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure
      {A | ∃ a b : K, A = SuzukiRootGL m a b}
  change Subgroup.center F ≤ commutator F
  intro z hz
  rcases (suzukiRootClosure_mem_center_iff
    m hm pi hpi_sq hpi_formula z).mp hz with ⟨b, hzb⟩
  by_cases hb : b = 0
  · have hz_one : z = 1 := by
      apply Subtype.ext
      change (z : GL (Fin 4) K) = 1
      rw [hzb, hb, suzukiRootGL_zero_zero]
    rw [hz_one]
    exact Subgroup.one_mem (commutator F)
  · rcases binaryGaloisField_tits_nontrivial m hm pi hpi_sq with ⟨t, ht⟩
    have hdelta : pi t + t ≠ 0 := by
      intro hzero
      exact ht (CharTwo.add_eq_zero.mp hzero)
    let y : Kˣ := Units.mk0 (b / (pi t + t))
      (div_ne_zero hb hdelta)
    rcases binaryGaloisField_tits_norm_surjective
      m pi hpi_sq y with ⟨a, ha⟩
    have ha_norm : (a : K) * pi (a : K) = b / (pi t + t) := by
      simpa [y] using ha
    have hcoord :
        (a : K) * pi ((a : K) * t) +
            ((a : K) * t) * pi (a : K) = b := by
      calc
        (a : K) * pi ((a : K) * t) +
              ((a : K) * t) * pi (a : K) =
            ((a : K) * pi (a : K)) * (pi t + t) := by
          rw [map_mul]
          ring
        _ = (b / (pi t + t)) * (pi t + t) := by rw [ha_norm]
        _ = b := div_mul_cancel₀ b hdelta
    let p : F := ⟨SuzukiRootGL m (a : K) 0,
      Subgroup.subset_closure ⟨(a : K), 0, rfl⟩⟩
    let q : F := ⟨SuzukiRootGL m ((a : K) * t) 0,
      Subgroup.subset_closure ⟨(a : K) * t, 0, rfl⟩⟩
    have hpq_mem : ⁅p, q⁆ ∈ commutator F :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top p) (Subgroup.mem_top q)
    have hpq_val :
        ((⁅p, q⁆ : F) : GL (Fin 4) K) = SuzukiRootGL m 0 b := by
      change ⁅SuzukiRootGL m (a : K) 0,
          SuzukiRootGL m ((a : K) * t) 0⁆ = SuzukiRootGL m 0 b
      calc
        ⁅SuzukiRootGL m (a : K) 0,
            SuzukiRootGL m ((a : K) * t) 0⁆ =
            SuzukiRootGL m 0
              ((a : K) * pi ((a : K) * t) +
                ((a : K) * t) * pi (a : K)) :=
          suzukiRootGL_commutator m pi hpi_sq hpi_formula
            (a : K) 0 ((a : K) * t) 0
        _ = SuzukiRootGL m 0 b := by rw [hcoord]
    have hz_eq : z = ⁅p, q⁆ := by
      apply Subtype.ext
      exact hzb.trans hpq_val.symm
    rw [hz_eq]
    exact hpq_mem

/-- The commutator subgroup and center of the Suzuki root subgroup coincide. -/
private theorem suzukiRootClosure_commutator_eq_center
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    commutator F = Subgroup.center F := by
  apply le_antisymm
  · exact suzukiRootClosure_commutator_le_center
      m hm pi hpi_sq hpi_formula
  · exact suzukiRootClosure_center_le_commutator
      m hm pi hpi_sq hpi_formula

/-- The torus matrix at the unit one is the identity. -/
public theorem suzukiTorusGL_one (m : ℕ) :
    SuzukiTorusGL m 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix]

/-- Multiplication of Suzuki torus matrices follows unit multiplication. -/
public theorem suzukiTorusGL_mul
    (m : ℕ)
    (x y : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiTorusGL m x * SuzukiTorusGL m y = SuzukiTorusGL m (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, mul_pow, mul_comm]

/-- The explicit Suzuki torus matrices as a bundled homomorphism. -/
private noncomputable def suzukiTorusHom (m : ℕ) :
    (BinaryGaloisField (2 * m + 1))ˣ →*
      GL (Fin 4) (BinaryGaloisField (2 * m + 1)) where
  toFun := SuzukiTorusGL m
  map_one' := suzukiTorusGL_one m
  map_mul' x y := (suzukiTorusGL_mul m x y).symm

/-- Inversion of a Suzuki torus matrix follows inversion of its unit
coordinate. -/
public theorem suzukiTorusGL_inv
    (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    (SuzukiTorusGL m x)⁻¹ = SuzukiTorusGL m x⁻¹ :=
  ((suzukiTorusHom m).map_inv x).symm

/-- The explicit torus homomorphism is injective. -/
private theorem suzukiTorusHom_injective (m : ℕ) :
    Function.Injective (suzukiTorusHom m) := by
  intro x y hxy
  apply Units.ext
  let K := BinaryGaloisField (2 * m + 1)
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 m
  apply frob.injective
  have h11 := congrArg
    (fun A : GL (Fin 4) K => ((A : Matrix (Fin 4) (Fin 4) K) 1 1)) hxy
  simpa [frob, iterateFrobeniusEquiv_def, iterateFrobenius_def,
    suzukiTorusHom,
    SuzukiTorusGL, SuzukiTorusMatrix] using h11

/-- The closure generated by torus matrices is exactly their unit-coordinate range. -/
public theorem suzukiTorusGL_mem_closure_iff
    (m : ℕ)
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    A ∈ Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x} ↔
      ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
        A = SuzukiTorusGL m x := by
  constructor
  · intro hA
    exact Subgroup.closure_induction
      (p := fun A _ =>
        ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x)
      (fun _ h => h)
      ⟨1, (suzukiTorusGL_one m).symm⟩
      (fun _ _ _ _ hx hy => by
        rcases hx with ⟨x, rfl⟩
        rcases hy with ⟨y, rfl⟩
        exact ⟨x * y, suzukiTorusGL_mul m x y⟩)
      (fun _ _ hx => by
        rcases hx with ⟨x, rfl⟩
        exact ⟨x⁻¹, ((suzukiTorusHom m).map_inv x).symm⟩)
      hA
  · rintro ⟨x, rfl⟩
    exact Subgroup.subset_closure ⟨x, rfl⟩

/-- Unit coordinates give a multiplicative equivalence onto the torus closure. -/
private theorem suzukiTorusCoordinatesMulEquiv (m : ℕ) :
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    ∃ e : (BinaryGaloisField (2 * m + 1))ˣ ≃* H,
      ∀ x, ((e x : H) : GL (Fin 4)
        (BinaryGaloisField (2 * m + 1))) = SuzukiTorusGL m x := by
  let K := BinaryGaloisField (2 * m + 1)
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure
      {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  let toH : Kˣ →* H := (suzukiTorusHom m).codRestrict H
    (fun x => Subgroup.subset_closure ⟨x, rfl⟩)
  have htoH_inj : Function.Injective toH := by
    intro x y hxy
    apply suzukiTorusHom_injective m
    exact congrArg Subtype.val hxy
  have htoH_surj : Function.Surjective toH := by
    intro h
    rcases (suzukiTorusGL_mem_closure_iff m
      (h : GL (Fin 4) K)).mp h.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let e : Kˣ ≃* H :=
    MulEquiv.ofBijective toH ⟨htoH_inj, htoH_surj⟩
  refine ⟨e, ?_⟩
  intro x
  rfl

set_option maxHeartbeats 800000 in
/-- Conjugation by a torus matrix scales the two root coordinates. -/
public theorem suzukiTorusGL_conj_root
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1))
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
      SuzukiRootGL m
        ((x : BinaryGaloisField (2 * m + 1)) * a)
        ((x : BinaryGaloisField (2 * m + 1)) *
          pi (x : BinaryGaloisField (2 * m + 1)) * b) := by
  rw [show (SuzukiTorusGL m x)⁻¹ = SuzukiTorusGL m x⁻¹ from
    ((suzukiTorusHom m).map_inv x).symm]
  let K := BinaryGaloisField (2 * m + 1)
  have hratio :
      (x : K) ^ (1 + 2 ^ m) * ((x : K) ^ (2 ^ m))⁻¹ = (x : K) := by
    rw [pow_add, pow_one]
    simp [pow_ne_zero _ x.ne_zero]
  have hsigma_sq :
      (x : K) ^ (2 ^ m) * (x : K) ^ (2 ^ m) =
        (x : K) ^ (2 ^ (m + 1)) := by
    rw [← pow_two, ← pow_mul, pow_succ]
  have hmiddle :
      (x : K) ^ (2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
        (x : K) * (x : K) ^ (2 ^ (m + 1)) := by
    calc
      (x : K) ^ (2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
          (x : K) ^ (2 ^ m + (1 + 2 ^ m)) := (pow_add _ _ _).symm
      _ = (x : K) ^ (1 + 2 ^ (m + 1)) := by
        congr 1
        rw [pow_succ]
        omega
      _ = (x : K) * (x : K) ^ (2 ^ (m + 1)) := by
        rw [pow_add, pow_one]
  have houter_sq :
      (x : K) ^ (1 + 2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
        (x : K) ^ (2 + 2 ^ (m + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ]
    omega
  have hsigma_inv :
      (x : K) ^ (2 ^ m) * ((x : K)⁻¹) ^ (2 ^ m) = 1 := by
    rw [← mul_pow]
    simp [x.ne_zero]
  have hpi_iter :
      ((x : K) ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) = (x : K) ^ 2 := by
    calc
      ((x : K) ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) =
          pi (pi (x : K)) := by
        rw [hpi_formula, hpi_formula]
      _ = (x : K) ^ 2 := hpi_sq (x : K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, mul_pow, hpi_formula,
      hratio, hsigma_sq, hmiddle, houter_sq, hpi_iter, inv_pow,
      mul_comm, mul_left_comm] <;> ring_nf
  all_goals rw [mul_assoc, hsigma_inv, mul_one]

/-- The twisted norm of a unit is one exactly at the unit one. -/
public theorem binaryGaloisField_tits_norm_eq_one_iff
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    (x : BinaryGaloisField (2 * m + 1)) *
        pi (x : BinaryGaloisField (2 * m + 1)) = 1 ↔
      x = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  constructor
  · intro hx
    have hpi_norm := congrArg pi hx
    simp only [map_mul, map_one, hpi_sq] at hpi_norm
    have hpix_ne : pi (x : K) ≠ 0 :=
      (map_ne_zero pi).2 x.ne_zero
    have hsquare : (x : K) ^ 2 = (x : K) := by
      apply mul_left_cancel₀ hpix_ne
      calc
        pi (x : K) * (x : K) ^ 2 = 1 := hpi_norm
        _ = pi (x : K) * (x : K) := by
          simpa [mul_comm] using hx.symm
    apply Units.ext
    apply mul_left_cancel₀ x.ne_zero
    simpa [pow_two] using hsquare
  · rintro rfl
    simp

/-- The root closure and torus closure intersect trivially. -/
private theorem suzukiRootClosure_disjoint_torusClosure
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    Disjoint F H := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  change Disjoint F H
  rw [Subgroup.disjoint_def]
  intro A hAF hAH
  rcases (suzukiRootGL_mem_closure_iff
    m pi hpi_sq hpi_formula A).mp hAF with ⟨a, b, hroot⟩
  rcases (suzukiTorusGL_mem_closure_iff m A).mp hAH with ⟨x, htorus⟩
  have heq : SuzukiRootGL m a b = SuzukiTorusGL m x :=
    hroot.symm.trans htorus
  have ha_entry := congrArg
    (fun M : GL (Fin 4) K => ((M : Matrix (Fin 4) (Fin 4) K) 0 1)) heq
  have hb_entry := congrArg
    (fun M : GL (Fin 4) K => ((M : Matrix (Fin 4) (Fin 4) K) 0 2)) heq
  have ha : a = 0 := by
    simpa [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix] using ha_entry
  have hb : b = 0 := by
    simpa [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix] using hb_entry
  calc
    A = SuzukiRootGL m a b := hroot
    _ = SuzukiRootGL m 0 0 := by rw [ha, hb]
    _ = 1 := suzukiRootGL_zero_zero m

/-- Nonidentity torus elements act fixed-point-freely on the root closure. -/
private theorem suzukiTorusClosure_fixedPointFree
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    ∀ h : GL (Fin 4) (BinaryGaloisField (2 * m + 1)),
      h ∈ H → h ≠ 1 →
      ∀ f : GL (Fin 4) (BinaryGaloisField (2 * m + 1)),
        f ∈ F → h⁻¹ * f * h = f → f = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  change ∀ h : GL (Fin 4) K, h ∈ H → h ≠ 1 →
    ∀ f : GL (Fin 4) K, f ∈ F → h⁻¹ * f * h = f → f = 1
  intro h hhH hh_ne f hfF hfix
  rcases (suzukiTorusGL_mem_closure_iff m h).mp hhH with ⟨x, hx⟩
  rcases (suzukiRootGL_mem_closure_iff
    m pi hpi_sq hpi_formula f).mp hfF with ⟨a, b, hf⟩
  have hx_ne : x ≠ 1 := by
    intro hx_one
    apply hh_ne
    rw [hx, hx_one, suzukiTorusGL_one]
  have htorus_inv : (SuzukiTorusGL m x)⁻¹ = SuzukiTorusGL m x⁻¹ :=
    ((suzukiTorusHom m).map_inv x).symm
  have htorus_inv_inv : (SuzukiTorusGL m x⁻¹)⁻¹ = SuzukiTorusGL m x := by
    calc
      (SuzukiTorusGL m x⁻¹)⁻¹ = SuzukiTorusGL m (x⁻¹)⁻¹ :=
        ((suzukiTorusHom m).map_inv x⁻¹).symm
      _ = SuzukiTorusGL m x := by rw [inv_inv]
  have hfix_coords := hfix
  rw [hx, hf, htorus_inv] at hfix_coords
  have hconj := suzukiTorusGL_conj_root
    m pi hpi_sq hpi_formula a b x⁻¹
  rw [htorus_inv_inv] at hconj
  have hscaled :
      SuzukiRootGL m (((x⁻¹ : Kˣ) : K) * a)
        (((x⁻¹ : Kˣ) : K) * pi ((x⁻¹ : Kˣ) : K) * b) =
      SuzukiRootGL m a b := hconj.symm.trans hfix_coords
  have hcoords := suzukiRootGL_injective m
    (((x⁻¹ : Kˣ) : K) * a)
    (((x⁻¹ : Kˣ) : K) * pi ((x⁻¹ : Kˣ) : K) * b)
    a b hscaled
  have ha : a = 0 := by
    by_contra ha0
    have hxinv_val : ((x⁻¹ : Kˣ) : K) = 1 := by
      apply mul_right_cancel₀ ha0
      simpa using hcoords.1
    have hxinv_unit : x⁻¹ = 1 := Units.ext hxinv_val
    apply hx_ne
    exact inv_eq_one.mp hxinv_unit
  have hb : b = 0 := by
    by_contra hb0
    have hnorm :
        ((x⁻¹ : Kˣ) : K) * pi ((x⁻¹ : Kˣ) : K) = 1 := by
      apply mul_right_cancel₀ hb0
      simpa using hcoords.2
    have hxinv_unit : x⁻¹ = 1 :=
      (binaryGaloisField_tits_norm_eq_one_iff
        m pi hpi_sq x⁻¹).mp hnorm
    apply hx_ne
    exact inv_eq_one.mp hxinv_unit
  calc
    f = SuzukiRootGL m a b := hf
    _ = SuzukiRootGL m 0 0 := by rw [ha, hb]
    _ = 1 := suzukiRootGL_zero_zero m

/-- Huppert-Blackburn XI.3.1: the root group and split torus in `Sz(q)`. -/
public theorem huppert_blackburn_XI_3_1
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    (∀ sigma : BinaryGaloisField (2 * m + 1) ≃+*
        BinaryGaloisField (2 * m + 1),
      (∀ x, sigma (sigma x) = x ^ 2) → sigma = pi) ∧
    (∀ x, pi x = x ^ (2 ^ (m + 1))) ∧
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    IsPGroup 2 F ∧
    (∀ x : F, x ^ 4 = 1) ∧
    (∃ x : F, orderOf x = 4) ∧
    Group.nilpotencyClass F = 2 ∧
    Nat.card F = (2 ^ (2 * m + 1)) ^ 2 ∧
    IsSuzukiTwoTypeA F ∧
    (∀ a b a' b' : BinaryGaloisField (2 * m + 1),
      SuzukiRootGL m a b * SuzukiRootGL m a' b' =
        SuzukiRootGL m (a + a') (b + b' + a * pi a')) ∧
    commutator F = Subgroup.center F ∧
    (∀ x : F, x ∈ commutator F ↔
      ∃ b : BinaryGaloisField (2 * m + 1),
        (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m 0 b) ∧
    (∃ e : (BinaryGaloisField (2 * m + 1))ˣ ≃* H,
      ∀ x, ((e x : H) : GL (Fin 4)
        (BinaryGaloisField (2 * m + 1))) = SuzukiTorusGL m x) ∧
    (∀ (a b : BinaryGaloisField (2 * m + 1))
        (x : (BinaryGaloisField (2 * m + 1))ˣ),
      SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
        SuzukiRootGL m ((x : BinaryGaloisField (2 * m + 1)) * a)
          ((x : BinaryGaloisField (2 * m + 1)) *
            pi (x : BinaryGaloisField (2 * m + 1)) * b)) ∧
    Disjoint F H ∧
    (∀ h : GL (Fin 4) (BinaryGaloisField (2 * m + 1)),
      h ∈ H → h ≠ 1 →
      ∀ f : GL (Fin 4) (BinaryGaloisField (2 * m + 1)), f ∈ F →
      h⁻¹ * f * h = f → f = 1) := by
  have h_unique := by
    exact binaryGaloisField_tits_square_root_unique m hm pi hpi_sq
  have h_formula := by
    exact binaryGaloisField_tits_automorphism_apply m hm pi hpi_sq
  refine ⟨h_unique, h_formula, ?_⟩
  dsimp only
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let H : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
        A = SuzukiTorusGL m x}
  have h_pgroup : IsPGroup 2 F := by
    exact suzukiRootClosure_isPGroup m pi hpi_sq h_formula
  have h_pow_four : ∀ x : F, x ^ 4 = 1 := by
    exact suzukiRootClosure_pow_four m pi hpi_sq h_formula
  have h_order_four : ∃ x : F, orderOf x = 4 := by
    exact suzukiRootClosure_exists_order_four m pi hpi_sq h_formula
  have h_nilpotency_class : Group.nilpotencyClass F = 2 := by
    exact suzukiRootClosure_nilpotencyClass m hm pi hpi_sq h_formula
  have h_card : Nat.card F = (2 ^ (2 * m + 1)) ^ 2 := by
    exact suzukiRootClosure_card m pi hpi_sq h_formula
  have h_typeA : IsSuzukiTwoTypeA F := by
    exact suzukiRootClosure_typeA m hm pi hpi_sq h_formula
  have h_root_mul :
      ∀ a b a' b' : BinaryGaloisField (2 * m + 1),
        SuzukiRootGL m a b * SuzukiRootGL m a' b' =
          SuzukiRootGL m (a + a') (b + b' + a * pi a') := by
    exact suzukiRootGL_mul m pi hpi_sq h_formula
  have h_commutator_center : commutator F = Subgroup.center F := by
    exact suzukiRootClosure_commutator_eq_center
      m hm pi hpi_sq h_formula
  have h_commutator_coordinates :
      ∀ x : F, x ∈ commutator F ↔
        ∃ b : BinaryGaloisField (2 * m + 1),
          (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
            SuzukiRootGL m 0 b := by
    intro x
    rw [h_commutator_center]
    exact suzukiRootClosure_mem_center_iff
      m hm pi hpi_sq h_formula x
  have h_torus_equiv :
      ∃ e : (BinaryGaloisField (2 * m + 1))ˣ ≃* H,
        ∀ x, ((e x : H) : GL (Fin 4)
          (BinaryGaloisField (2 * m + 1))) = SuzukiTorusGL m x := by
    exact suzukiTorusCoordinatesMulEquiv m
  have h_torus_conjugation :
      ∀ (a b : BinaryGaloisField (2 * m + 1))
          (x : (BinaryGaloisField (2 * m + 1))ˣ),
        SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
          SuzukiRootGL m
            ((x : BinaryGaloisField (2 * m + 1)) * a)
            ((x : BinaryGaloisField (2 * m + 1)) *
              pi (x : BinaryGaloisField (2 * m + 1)) * b) := by
    exact suzukiTorusGL_conj_root m pi hpi_sq h_formula
  have h_disjoint : Disjoint F H := by
    exact suzukiRootClosure_disjoint_torusClosure
      m pi hpi_sq h_formula
  have h_fixed_point_free :
      ∀ h : GL (Fin 4) (BinaryGaloisField (2 * m + 1)),
        h ∈ H → h ≠ 1 →
        ∀ f : GL (Fin 4) (BinaryGaloisField (2 * m + 1)),
          f ∈ F → h⁻¹ * f * h = f → f = 1 := by
    exact suzukiTorusClosure_fixedPointFree
      m pi hpi_sq h_formula
  exact ⟨h_pgroup, h_pow_four, h_order_four, h_nilpotency_class,
    h_card, h_typeA, h_root_mul, h_commutator_center,
    h_commutator_coordinates, h_torus_equiv, h_torus_conjugation,
    h_disjoint, h_fixed_point_free⟩

end External
end CFSG.BenderSuzuki
