module

public import CFSG.Quasithin.Background.H11Defs
public import CFSG.Quasithin.SteinbergCBTwistedField
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.H11Proof

section MinusField

open Polynomial

variable {F : Type} [Field F]

@[expose] noncomputable def quadPoly (a : F) : F[X] := X ^ 2 + X + C a

theorem quadPoly_natDegree (a : F) : (quadPoly a).natDegree = 2 := by
  unfold quadPoly
  compute_degree!

theorem quadPoly_ne_zero (a : F) : quadPoly a ≠ 0 := by
  intro h
  have h2 := quadPoly_natDegree a
  rw [h, natDegree_zero] at h2
  norm_num at h2

theorem quadPoly_irreducible {a : F} (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) :
    Irreducible (quadPoly a) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadPoly_natDegree]
    simp
  · intro x hx
    apply ha x
    have h0 : (quadPoly a).eval x = 0 := hx
    simpa [quadPoly] using h0

theorem finrank_adjoinRoot_quad (a : F) :
    Module.finrank F (AdjoinRoot (quadPoly a)) = 2 := by
  rw [PowerBasis.finrank, AdjoinRoot.powerBasis_dim (quadPoly_ne_zero a), quadPoly_natDegree]

theorem natCard_adjoinRoot_quad [Finite F] (a : F) {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (AdjoinRoot (quadPoly a)) = 2 ^ (2 * n) := by
  haveI : Module.Finite F (AdjoinRoot (quadPoly a)) :=
    (AdjoinRoot.powerBasis (quadPoly_ne_zero a)).finite
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_adjoinRoot_quad, hF, ← pow_mul, mul_comm]

end MinusField

section MinusK

open Polynomial

variable {F : Type} [Field F]

theorem omega_rel (a : F) :
    (AdjoinRoot.root (quadPoly a)) ^ 2 + AdjoinRoot.root (quadPoly a) +
      algebraMap F (AdjoinRoot (quadPoly a)) a = 0 := by
  have h : Polynomial.aeval (AdjoinRoot.root (quadPoly a)) (quadPoly a) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [quadPoly, map_add, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  exact h

theorem exists_decomp_quad (a : F) [Fact (Irreducible (quadPoly a))]
    (z : AdjoinRoot (quadPoly a)) :
    ∃ u v : F, z = algebraMap F (AdjoinRoot (quadPoly a)) u +
      algebraMap F (AdjoinRoot (quadPoly a)) v * AdjoinRoot.root (quadPoly a) := by
  let pb := AdjoinRoot.powerBasis (quadPoly_ne_zero a)
  obtain ⟨f, hfd, hz⟩ := pb.exists_eq_aeval z
  have hdim : pb.dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim, quadPoly_natDegree]
  rw [hdim] at hfd
  have hnd : f.natDegree ≤ 1 := by omega
  have hfX : f = Polynomial.C (f.coeff 1) * Polynomial.X + Polynomial.C (f.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hnd
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hz]
  conv_lhs => rw [hfX]
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [add_comm]
  rfl

theorem algebraMap_ne_root (a : F) [Fact (Irreducible (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (c : F) :
    algebraMap F (AdjoinRoot (quadPoly a)) c ≠ AdjoinRoot.root (quadPoly a) := by
  intro h
  apply ha c
  have h1 := omega_rel (F := F) a
  rw [← h] at h1
  have h2 : algebraMap F (AdjoinRoot (quadPoly a)) (c ^ 2 + c + a) = 0 := by
    rw [map_add, map_add, map_pow]
    linear_combination h1
  exact (map_eq_zero_iff _ (algebraMap F (AdjoinRoot (quadPoly a))).injective).mp h2


theorem iterate_frob_algebraMap_fix [Finite F] {K : Type} [Field K] [CharP K 2] [Algebra F K]
    {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (c : F) :
    iterateFrobenius K 2 n (algebraMap F K c) = algebraMap F K c := by
  have : Fintype F := Fintype.ofFinite F
  have hc : c ^ 2 ^ n = c := by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hF] at this
  rw [iterateFrobenius_def, ← map_pow, hc]

theorem fixed_mem_range_algebraMap [Finite F] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra F K]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hK : Nat.card K = (2 ^ n) ^ 2) (z : K)
    (hz : iterateFrobenius K 2 n z = z) : ∃ c : F, algebraMap F K c = z := by
  have hinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
  have hsub : Set.range (algebraMap F K) ⊆
      ((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K) : Set K) := by
    rintro _ ⟨c, rfl⟩
    exact SteinbergCB.mem_frobFixed.mpr (iterate_frob_algebraMap_fix hF c)
  have hcard : (((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K) : Set K)).ncard ≤
      (Set.range (algebraMap F K)).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have h1 : Nat.card ((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K)) ≤ 2 ^ n :=
      SteinbergCB.card_frobFixed_le hn (fun x => iterateFrobenius_def 2 n x)
    have h2 : Nat.card (Set.range (algebraMap F K)) = 2 ^ n := by
      rw [Nat.card_congr (Equiv.ofInjective (algebraMap F K) hinj).symm, hF]
    have h3 : Nat.card ((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K)) =
        Nat.card (((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K) : Set K)) := rfl
    rw [h2]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hzmem : z ∈ ((SteinbergCB.frobFixed (iterateFrobenius K 2 n) : Subfield K) : Set K) :=
    SteinbergCB.mem_frobFixed.mpr hz
  rw [← heq] at hzmem
  obtain ⟨c, hc⟩ := hzmem
  exact ⟨c, hc⟩

theorem frob_root_eq [Finite F] [CharP F 2] {a : F} [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) :
    iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n (AdjoinRoot.root (quadPoly a)) =
      AdjoinRoot.root (quadPoly a) + 1 := by
  haveI : Finite (AdjoinRoot (quadPoly a)) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h2 : (2 : AdjoinRoot (quadPoly a)) = 0 := by
    have := CharP.cast_eq_zero (AdjoinRoot (quadPoly a)) 2
    exact_mod_cast this
  set ω := AdjoinRoot.root (quadPoly a) with hωdef
  set σ := iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n with hσdef
  have hω := omega_rel a
  have hσa : σ (algebraMap F (AdjoinRoot (quadPoly a)) a) =
      algebraMap F (AdjoinRoot (quadPoly a)) a := iterate_frob_algebraMap_fix hF a
  have hy : (σ ω) ^ 2 + σ ω + algebraMap F (AdjoinRoot (quadPoly a)) a = 0 := by
    have := congrArg σ hω
    rw [map_zero, map_add, map_add, map_pow, hσa] at this
    exact this
  have hprod : (σ ω - ω) * (σ ω + ω + 1) = 0 := by
    linear_combination hy - hω
  rcases mul_eq_zero.mp hprod with h | h
  · exfalso
    obtain ⟨c, hc⟩ := fixed_mem_range_algebraMap hn hF hK ω (sub_eq_zero.mp h)
    exact algebraMap_ne_root a ha c hc
  · linear_combination h - (ω + 1) * h2


section MinusTheta

open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {n : ℕ} {a : F}
  [Fact (Irreducible (quadPoly a))] [CharP (AdjoinRoot (quadPoly a)) 2]

@[expose] noncomputable def hermOf (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] (x : Fin 4 → F) :
    Matrix (Fin 2) (Fin 2) (AdjoinRoot (quadPoly a)) :=
  !![algebraMap F (AdjoinRoot (quadPoly a)) (x 0),
    algebraMap F (AdjoinRoot (quadPoly a)) (x 2) +
      algebraMap F (AdjoinRoot (quadPoly a)) (x 3) * AdjoinRoot.root (quadPoly a);
    iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (algebraMap F (AdjoinRoot (quadPoly a)) (x 2) +
        algebraMap F (AdjoinRoot (quadPoly a)) (x 3) * AdjoinRoot.root (quadPoly a)),
    algebraMap F (AdjoinRoot (quadPoly a)) (x 1)]

theorem frob_iter_iter [Finite (AdjoinRoot (quadPoly a))]
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (z : AdjoinRoot (quadPoly a)) :
    iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n z) = z :=
  SteinbergCB.frob_frob hK (fun x => iterateFrobenius_def 2 n x) z

theorem hermOf_mem [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (x : Fin 4 → F) :
    (hermOf n a x)ᵀ = (hermOf n a x).map (iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n) := by
  have hfix : ∀ c : F, iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (AdjoinRoot.of (quadPoly a) c) = AdjoinRoot.of (quadPoly a) c :=
    fun c => iterate_frob_algebraMap_fix hF c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, hfix, frob_iter_iter hK]

theorem hermOf_add (x y : Fin 4 → F) : hermOf n a (x + y) = hermOf n a x + hermOf n a y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, map_add, add_mul, map_mul] <;> ring

theorem hermOf_smul [Finite F] [Finite (AdjoinRoot (quadPoly a))] (hF : Nat.card F = 2 ^ n)
    (c : F) (x : Fin 4 → F) :
    hermOf n a (c • x) = algebraMap F (AdjoinRoot (quadPoly a)) c • hermOf n a x := by
  have hfix : ∀ c : F, iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (AdjoinRoot.of (quadPoly a) c) = AdjoinRoot.of (quadPoly a) c :=
    fun c => iterate_frob_algebraMap_fix hF c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, hfix, smul_eq_mul, map_mul] <;> ring

theorem coeffs_eq_zero_of_add_mul_root [Finite F] {ha : ∀ t : F, t ^ 2 + t + a ≠ 0} (u v : F)
    (h : algebraMap F (AdjoinRoot (quadPoly a)) u + algebraMap F (AdjoinRoot (quadPoly a)) v *
      AdjoinRoot.root (quadPoly a) = 0) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨(map_eq_zero_iff _ (algebraMap F (AdjoinRoot (quadPoly a))).injective).mp h, rfl⟩
  · exfalso
    have hv' : algebraMap F (AdjoinRoot (quadPoly a)) v ≠ 0 :=
      fun h0 => hv ((map_eq_zero_iff _ (algebraMap F (AdjoinRoot (quadPoly a))).injective).mp h0)
    apply algebraMap_ne_root a ha (-u / v)
    rw [map_div₀, map_neg]
    field_simp
    linear_combination -h

theorem hermOf_eq_iff [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    {ha : ∀ t : F, t ^ 2 + t + a ≠ 0} (x y : Fin 4 → F) :
    hermOf n a x = hermOf n a y ↔ x = y := by
  constructor
  · intro h
    have hinj := (algebraMap F (AdjoinRoot (quadPoly a))).injective
    have h00 : algebraMap F (AdjoinRoot (quadPoly a)) (x 0) =
        algebraMap F (AdjoinRoot (quadPoly a)) (y 0) := congrFun (congrFun h 0) 0
    have h11 : algebraMap F (AdjoinRoot (quadPoly a)) (x 1) =
        algebraMap F (AdjoinRoot (quadPoly a)) (y 1) := congrFun (congrFun h 1) 1
    have h01 : algebraMap F (AdjoinRoot (quadPoly a)) (x 2) +
        algebraMap F (AdjoinRoot (quadPoly a)) (x 3) * AdjoinRoot.root (quadPoly a) =
        algebraMap F (AdjoinRoot (quadPoly a)) (y 2) +
        algebraMap F (AdjoinRoot (quadPoly a)) (y 3) * AdjoinRoot.root (quadPoly a) :=
      congrFun (congrFun h 0) 1
    have hd := coeffs_eq_zero_of_add_mul_root (a := a) (ha := ha) (x 2 - y 2) (x 3 - y 3)
      (by rw [map_sub, map_sub]; linear_combination h01)
    have e0 : x 0 = y 0 := hinj h00
    have e1 : x 1 = y 1 := hinj h11
    have e2 : x 2 = y 2 := sub_eq_zero.mp hd.1
    have e3 : x 3 = y 3 := sub_eq_zero.mp hd.2
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  · rintro rfl
    rfl

theorem hermOf_surj [Finite F] [Finite (AdjoinRoot (quadPoly a))] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (M : Matrix (Fin 2) (Fin 2) (AdjoinRoot (quadPoly a)))
    (hM : Mᵀ = M.map (iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n)) :
    ∃ x : Fin 4 → F, hermOf n a x = M := by
  have h00 : iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n (M 0 0) = M 0 0 := by
    have := congrFun (congrFun hM 0) 0
    simpa using this.symm
  have h11 : iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n (M 1 1) = M 1 1 := by
    have := congrFun (congrFun hM 1) 1
    simpa using this.symm
  have h10 : M 1 0 = iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n (M 0 1) := by
    have := congrFun (congrFun hM 0) 1
    simpa using this
  obtain ⟨c0, hc0⟩ := fixed_mem_range_algebraMap hn hF hK (M 0 0) h00
  obtain ⟨c1, hc1⟩ := fixed_mem_range_algebraMap hn hF hK (M 1 1) h11
  obtain ⟨u, v, huv⟩ := exists_decomp_quad a (M 0 1)
  have hc0' : AdjoinRoot.of (quadPoly a) c0 = M 0 0 := hc0
  have hc1' : AdjoinRoot.of (quadPoly a) c1 = M 1 1 := hc1
  have huv' : M 0 1 = AdjoinRoot.of (quadPoly a) u +
      AdjoinRoot.of (quadPoly a) v * AdjoinRoot.root (quadPoly a) := huv
  refine ⟨![c0, c1, u, v], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [hermOf, hc0']
  · simp [hermOf, huv']
  · show iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (AdjoinRoot.of (quadPoly a) u + AdjoinRoot.of (quadPoly a) v *
        AdjoinRoot.root (quadPoly a)) = M 1 0
    rw [h10, huv']
  · simp [hermOf, hc1']

theorem hermOf_det [Finite F] [Finite (AdjoinRoot (quadPoly a))] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) (ha : ∀ t : F, t ^ 2 + t + a ≠ 0)
    (x : Fin 4 → F) :
    (hermOf n a x).det = algebraMap F (AdjoinRoot (quadPoly a)) (orthMinus F a x) := by
  have h2 : (2 : AdjoinRoot (quadPoly a)) = 0 := by
    have := CharP.cast_eq_zero (AdjoinRoot (quadPoly a)) 2
    exact_mod_cast this
  have hfix : ∀ c : F, iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (AdjoinRoot.of (quadPoly a) c) = AdjoinRoot.of (quadPoly a) c :=
    fun c => iterate_frob_algebraMap_fix hF c
  have hσz : iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n
      (algebraMap F (AdjoinRoot (quadPoly a)) (x 2) +
        algebraMap F (AdjoinRoot (quadPoly a)) (x 3) * AdjoinRoot.root (quadPoly a)) =
      algebraMap F (AdjoinRoot (quadPoly a)) (x 2) +
        algebraMap F (AdjoinRoot (quadPoly a)) (x 3) *
          (AdjoinRoot.root (quadPoly a) + 1) := by
    rw [map_add, map_mul, iterate_frob_algebraMap_fix hF, iterate_frob_algebraMap_fix hF,
      frob_root_eq hn hF hK ha]
  have hω := omega_rel a
  rw [Matrix.det_fin_two]
  simp only [hermOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [hσz]
  simp only [orthMinus, map_add, map_mul, map_pow]
  linear_combination (-((algebraMap F (AdjoinRoot (quadPoly a)) (x 2)) ^ 2 +
    algebraMap F (AdjoinRoot (quadPoly a)) (x 2) * algebraMap F (AdjoinRoot (quadPoly a)) (x 3) *
      AdjoinRoot.root (quadPoly a) +
    algebraMap F (AdjoinRoot (quadPoly a)) (x 2) * algebraMap F (AdjoinRoot (quadPoly a)) (x 3))) *
      h2 + (-(algebraMap F (AdjoinRoot (quadPoly a)) (x 3)) ^ 2) * hω


end MinusTheta

end MinusK

end CFSG.Quasithin.H11Proof
