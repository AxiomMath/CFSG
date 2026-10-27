module

public import CFSG.RepresentationTheory.SzMartineau.LemmaSix
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

variable {a : ℕ}

private noncomputable def frob (c : ℕ) (v : Fin 4 → F a) : Fin 4 → F a :=
  fun i => iterateFrobenius (F a) 2 c (v i)

private noncomputable def stdBasis (s : Fin 4) : Fin 4 → F a := Pi.single s 1

private lemma frob_mulVec (c : ℕ) (M : Matrix (Fin 4) (Fin 4) (F a)) (v : Fin 4 → F a) :
    frob c (M *ᵥ v) = (M.map (· ^ 2 ^ c)) *ᵥ frob c v := by
  ext i
  simp only [frob, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, iterateFrobenius_def]

private lemma eq_sum_smul_stdBasis (v : Fin 4 → F a) :
    v = ∑ s, v s • stdBasis (a := a) s := by
  ext i
  simp [stdBasis, Finset.sum_apply, Pi.single_apply]

private lemma biadd_sum (β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a))
    (v w : Fin 4 → F a) :
    β v w = ∑ s, ∑ t, β (v s • stdBasis (a := a) s) (w t • stdBasis (a := a) t) := by
  conv_lhs => rw [eq_sum_smul_stdBasis v]
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_lhs => rw [eq_sum_smul_stdBasis w]
  rw [map_sum]

private noncomputable def bilinOfTensor (M : Fin 4 → Fin 4 → Fin 4 → F a) :
    (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) :=
  LinearMap.mk₂ (F a) (fun x y i => ∑ s, ∑ t, M i s t * x s * y t)
    (by
      intro x x' y
      ext i
      simp [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    (by
      intro x y y'
      ext i
      simp [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)

private noncomputable def coordBilin (β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a))
    (i s t : Fin 4) : F a →+ F a →+ F a where
  toFun x :=
    { toFun := fun y => β (x • stdBasis (a := a) s) (y • stdBasis (a := a) t) i
      map_zero' := by
        letI : Fintype (F a) := Fintype.ofFinite _
        simp [stdBasis]
      map_add' := by
        intro y y'
        letI : Fintype (F a) := Fintype.ofFinite _
        simp [add_smul, map_add] }
  map_zero' := by
    ext y
    letI : Fintype (F a) := Fintype.ofFinite _
    simp [stdBasis]
  map_add' := by
    intro x x'
    ext y
    letI : Fintype (F a) := Fintype.ofFinite _
    simp [add_smul, map_add]

private lemma sum_comm_four {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin 4 → Fin 4 → Fin n → Fin n → M) :
    (∑ s, ∑ t, ∑ c, ∑ d, f s t c d) = ∑ c, ∑ d, ∑ s, ∑ t, f s t c d := by
  calc
    (∑ s, ∑ t, ∑ c, ∑ d, f s t c d)
        = ∑ s, ∑ c, ∑ t, ∑ d, f s t c d := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ s, ∑ t, ∑ d, f s t c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ s, ∑ d, ∑ t, f s t c d := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ s, ∑ t, f s t c d := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]

private lemma exists_two_var_decomp (β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a)) :
    ∃ B : Fin (2 * a + 1) → Fin (2 * a + 1) →
        ((Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)),
      ∀ v w, β v w = ∑ c, ∑ d, B c d (frob (c : ℕ) v) (frob (d : ℕ) w) := by
  letI : Fintype (F a) := Fintype.ofFinite _
  have hK : Nat.card (F a) = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  have hmain := (CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    (K := F a) (p := 2) (n := 2 * a + 1) (by norm_num) (by omega) hK).2.1
  choose M hM hMuniq using fun (i s t : Fin 4) => hmain (coordBilin β i s t)
  clear hMuniq
  refine ⟨fun c d => bilinOfTensor (fun i s t => M i s t c d), fun v w => ?_⟩
  ext i
  rw [Finset.sum_apply]
  simp_rw [Finset.sum_apply]
  have h1 : ∀ s t : Fin 4,
      β (v s • stdBasis (a := a) s) (w t • stdBasis (a := a) t) i =
        ∑ c, ∑ d, M i s t c d * ((v s) ^ 2 ^ (c : ℕ) * (w t) ^ 2 ^ (d : ℕ)) :=
    fun s t => hM i s t (v s) (w t)
  calc
    β v w i = ∑ s, ∑ t, β (v s • stdBasis (a := a) s) (w t • stdBasis (a := a) t) i := by
      rw [biadd_sum β v w]
      simp only [Finset.sum_apply]
    _ = ∑ s, ∑ t, ∑ c, ∑ d,
          M i s t c d * ((v s) ^ 2 ^ (c : ℕ) * (w t) ^ 2 ^ (d : ℕ)) := by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => h1 s t
    _ = ∑ c, ∑ d, ∑ s, ∑ t,
          M i s t c d * ((v s) ^ 2 ^ (c : ℕ) * (w t) ^ 2 ^ (d : ℕ)) :=
      sum_comm_four (fun s t c d =>
        M i s t c d * ((v s) ^ 2 ^ (c : ℕ) * (w t) ^ 2 ^ (d : ℕ)))
    _ = ∑ c, ∑ d, (bilinOfTensor (fun i s t => M i s t c d)
          (frob (c : ℕ) v) (frob (d : ℕ) w)) i := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      simp only [bilinOfTensor, LinearMap.mk₂_apply, frob, iterateFrobenius_def]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring

private lemma bilin_apply_eq_sum (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (x y : Fin 4 → F a) (i : Fin 4) :
    B x y i = ∑ s, ∑ t, x s * y t * B (stdBasis (a := a) s) (stdBasis (a := a) t) i := by
  conv_lhs => rw [eq_sum_smul_stdBasis x]
  rw [map_sum]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, LinearMap.smul_apply, Pi.smul_apply]
  conv_lhs => rw [eq_sum_smul_stdBasis y]
  rw [map_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul]
  change x s * (y t * (B (stdBasis (a := a) s)) (stdBasis (a := a) t) i) =
    x s * y t * (B (stdBasis (a := a) s)) (stdBasis (a := a) t) i
  ring

private lemma frob_smul_stdBasis (c : ℕ) (x : F a) (s : Fin 4) :
    frob c (x • (stdBasis (a := a) s)) = (x ^ 2 ^ c) • (stdBasis (a := a) s) := by
  ext i
  by_cases h : i = s
  · simp [frob, stdBasis, h, map_mul, iterateFrobenius_def]
  · simp [frob, stdBasis, h]

private lemma bilin_smul_smul (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (x y : F a) (s t : Fin 4) (i : Fin 4) :
    B (x • stdBasis (a := a) s) (y • stdBasis (a := a) t) i =
      x * y * B (stdBasis (a := a) s) (stdBasis (a := a) t) i := by
  simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma two_var_decomp_unique
    {B B' : Fin (2 * a + 1) → Fin (2 * a + 1) →
      ((Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))}
    {β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a)}
    (hB : ∀ v w, β v w = ∑ c, ∑ d, B c d (frob (c : ℕ) v) (frob (d : ℕ) w))
    (hB' : ∀ v w, β v w = ∑ c, ∑ d, B' c d (frob (c : ℕ) v) (frob (d : ℕ) w)) :
    B' = B := by
  letI : Fintype (F a) := Fintype.ofFinite _
  have hK : Nat.card (F a) = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  have hmain := (CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    (K := F a) (p := 2) (n := 2 * a + 1) (by norm_num) (by omega) hK).2.1
  have hcoef : ∀ (i s t : Fin 4) (c d : Fin (2 * a + 1)),
      B' c d (stdBasis (a := a) s) (stdBasis (a := a) t) i =
        B c d (stdBasis (a := a) s) (stdBasis (a := a) t) i := by
    intro i s t c d
    obtain ⟨A, hA, huniq⟩ := hmain (coordBilin β i s t)
    have h1 : (fun c d => B c d (stdBasis (a := a) s) (stdBasis (a := a) t) i) = A := by
      apply huniq
      intro x y
      have h := hB (x • stdBasis (a := a) s) (y • stdBasis (a := a) t)
      have h2 := congrFun h i
      change β (x • stdBasis (a := a) s) (y • stdBasis (a := a) t) i = _
      rw [h2]
      rw [Finset.sum_apply]
      simp_rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [frob_smul_stdBasis, frob_smul_stdBasis, bilin_smul_smul]
      ring
    have h2 : (fun c d => B' c d (stdBasis (a := a) s) (stdBasis (a := a) t) i) = A := by
      apply huniq
      intro x y
      have h := hB' (x • stdBasis (a := a) s) (y • stdBasis (a := a) t)
      have h3 := congrFun h i
      change β (x • stdBasis (a := a) s) (y • stdBasis (a := a) t) i = _
      rw [h3]
      rw [Finset.sum_apply]
      simp_rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [frob_smul_stdBasis, frob_smul_stdBasis, bilin_smul_smul]
      ring
    have h2' := congrFun (congrFun h2 c) d
    have h1' := congrFun (congrFun h1 c) d
    rw [h2', h1']
  funext c d
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  ext i
  rw [bilin_apply_eq_sum (B' c d) x y i, bilin_apply_eq_sum (B c d) x y i]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [hcoef i s t c d]

private lemma twHom_add (c d : ℕ) (g : ↥(Sz a)) :
    (twHom a c g).map (· ^ 2 ^ d) = twHom a (c + d) g := by
  rw [twHom_apply, twHom_apply, Matrix.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [← pow_mul, ← pow_add]

private noncomputable def precompBilin (f g : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)) :
    (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) :=
  LinearMap.mk₂ (F a) (fun x y => B (f x) (g y))
    (by intro x x' y; simp [map_add])
    (by intro c x y; simp)
    (by intro x y y'; simp [map_add])
    (by intro c x y; simp)

private noncomputable def postcompBilin (f : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)) :
    (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) :=
  LinearMap.mk₂ (F a) (fun x y => f (B x y))
    (by intro x x' y; simp [map_add])
    (by intro c x y; simp)
    (by intro x y y'; simp [map_add])
    (by intro c x y; simp)

private noncomputable def conjBilin (β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a))
    (g : ↥(Sz a)) (c₁ c₂ : ℕ) :
    (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a) where
  toFun v :=
    { toFun := fun w => β (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w)
      map_zero' := by simp
      map_add' := by intro w w'; simp only [Matrix.mulVec_add, map_add] }
  map_zero' := by ext w; simp
  map_add' := by intro v v'; ext w; simp [Matrix.mulVec_add, map_add]

private lemma conjBilin_decomp {B : Fin (2 * a + 1) → Fin (2 * a + 1) →
      ((Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))}
    {β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a)}
    (hB : ∀ v w, β v w = ∑ c, ∑ d, B c d (frob (c : ℕ) v) (frob (d : ℕ) w))
    (g : ↥(Sz a)) (c₁ c₂ : ℕ) :
    ∀ v w, conjBilin β g c₁ c₂ v w =
      ∑ c : Fin (2 * a + 1), ∑ d : Fin (2 * a + 1),
        precompBilin ((twHom a (c₁ + (c : ℕ)) g).mulVecLin)
          ((twHom a (c₂ + (d : ℕ)) g).mulVecLin) (B c d)
          (frob (c : ℕ) v) (frob (d : ℕ) w) := by
  intro v w
  change β (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = _
  rw [hB]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [frob_mulVec, frob_mulVec, twHom_add, twHom_add]
  rfl

private lemma actBilin_decomp {B : Fin (2 * a + 1) → Fin (2 * a + 1) →
      ((Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))}
    {β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a)}
    (hB : ∀ v w, β v w = ∑ c, ∑ d, B c d (frob (c : ℕ) v) (frob (d : ℕ) w))
    (g : ↥(Sz a)) (c₁ c₂ c₃ : ℕ)
    (hβ : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      β (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ β v w) :
    ∀ v w, conjBilin β g c₁ c₂ v w =
      ∑ c : Fin (2 * a + 1), ∑ d : Fin (2 * a + 1),
        postcompBilin ((twHom a c₃ g).mulVecLin) (B c d)
          (frob (c : ℕ) v) (frob (d : ℕ) w) := by
  intro v w
  change β (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = _
  rw [hβ g v w]
  change twHom a c₃ g *ᵥ β v w = _
  rw [hB]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rfl

theorem biadd_eq_zero_of_twisted_equivariant {a : ℕ} (ha : 1 ≤ a) (c₁ c₂ c₃ : ℕ)
    (β : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a))
    (hβ : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      β (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ β v w) :
    β = 0 := by
  obtain ⟨B, hB⟩ := exists_two_var_decomp β
  have hBzero : ∀ c d, B c d = 0 := by
    intro c d
    refine bilin_eq_zero_of_twisted_equivariant ha (c₁ + (c : ℕ)) (c₂ + (d : ℕ)) c₃
      (B c d) ?_
    intro g x y
    ext i
    have h1 := conjBilin_decomp hB g c₁ c₂
    have h2 := actBilin_decomp hB g c₁ c₂ c₃ hβ
    have huniq := two_var_decomp_unique h1 h2
    have hcd := congrFun (congrFun huniq c) d
    have hx := LinearMap.ext_iff.mp hcd x
    have hy := LinearMap.ext_iff.mp hx y
    have hi := congrFun hy i
    exact hi.symm
  refine AddMonoidHom.ext fun v => AddMonoidHom.ext fun w => ?_
  rw [hB v w]
  simp [hBzero]

end CFSG.RepresentationTheory.SzMartineau
