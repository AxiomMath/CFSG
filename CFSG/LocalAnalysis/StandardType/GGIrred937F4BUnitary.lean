module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BDescent
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BSplit
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BFrames
public import CFSG.RankThree.PartOne.KF4.F4ThreeFamily

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KF4

open scoped MatrixGroups

@[expose] noncomputable def a2FixedGroup (L : Type) [Field L] [CharP L 2]
    (f : ℕ) (w₀ : WeylGroup Tag.F4) (α β : Fin Tag.F4.rank → ℤ) :
    Subgroup (ModGL Tag.F4 L) :=
  rootSpan Tag.F4 L (a2Roots α β) ⊓ langFixed L f w₀

theorem a2FixedGroup_finite_quasisimple
    {K : Type} [Field K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f) (hq2 : 2 < Nat.card K)
    (w₀ : WeylGroup Tag.F4) (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    {α β : Fin Tag.F4.rank → ℤ} (h : IsA2Pair α β) :
    Finite ↥(a2FixedGroup (AlgebraicClosure K) f w₀ α β) ∧
      CFSG.IsQuasisimple ↥(a2FixedGroup (AlgebraicClosure K) f w₀ α β) := by
  classical
  obtain ⟨ρ, σ, hfr, h01, h12, hset⟩ := f4_exists_a2Frame h (AlgebraicClosure K)
  have hpi := a2Frame_w₀_compat hfr w₀ hw₀
  have hq2' : 2 < 2 ^ f := hq ▸ hq2
  have hf : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    subst this
    simp at hq2'
  obtain ⟨P, hP, hP1, -⟩ := hfr.family_unitary_ex (ℓ := 2) (f := f) Nat.prime_two hf (k := K) hq
    hq2' (iterateFrobenius (AlgebraicClosure K) 2 f) (fun c => by rw [iterateFrobenius_def])
    (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)
    (canonicalRep_mem_monomialSubgroup _ w₀) (Equiv.refl _) hpi
  have hEq : a2FixedGroup (AlgebraicClosure K) f w₀ α β = P () := by
    rw [hP1, hset]
    rfl
  rw [hEq]
  exact ⟨hP.1 (), hP.2.1 ()⟩

private noncomputable def f4BDiagSL {L : Type} [Field L] (a b : Lˣ) : SL(3, L) :=
  ⟨Matrix.diagonal ![(a : L), (b : L), (((a * b)⁻¹ : Lˣ) : L)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [Units.val_inv_eq_inv_val]
    field_simp⟩

private theorem f4BDiagSL_mul {L : Type} [Field L] (a b a' b' : Lˣ) :
    f4BDiagSL (a * a') (b * b') = f4BDiagSL a b * f4BDiagSL a' b' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal ![(((a * a' : Lˣ)) : L), (((b * b' : Lˣ)) : L),
    (((((a * a') * (b * b'))⁻¹ : Lˣ)) : L)] =
    Matrix.diagonal ![(a : L), (b : L), (((a * b)⁻¹ : Lˣ) : L)] *
      Matrix.diagonal ![(a' : L), (b' : L), (((a' * b')⁻¹ : Lˣ) : L)]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm, mul_assoc, mul_left_comm, Units.val_inv_eq_inv_val, mul_inv_rev]

private theorem f4BDiagSL_one {L : Type} [Field L] : f4BDiagSL (1 : Lˣ) (1 : Lˣ) = (1 : SL(3, L)) := by
  apply Subtype.ext
  change Matrix.diagonal ![((1 : Lˣ) : L), ((1 : Lˣ) : L), ((((1 : Lˣ) * 1)⁻¹ : Lˣ) : L)] = 1
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem f4BDiagSL_offdiag {L : Type} [Field L] (a b : Lˣ) :
    ∀ i j : Fin 3, i ≠ j → ((f4BDiagSL a b : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij

private noncomputable def f4BDiagHom (L : Type) [Field L] : Lˣ × Lˣ →* SL(3, L) where
  toFun p := f4BDiagSL p.1 p.2
  map_one' := f4BDiagSL_one
  map_mul' p q := f4BDiagSL_mul p.1 p.2 q.1 q.2

private theorem f4BDiagHom_injective (L : Type) [Field L] : Function.Injective (f4BDiagHom L) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) 0 0) h
  have h1 := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) 1 1) h
  simp [f4BDiagHom, f4BDiagSL] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem a2FixedGroup_contains_elemAbelian_nine
    {K : Type} [Field K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f)
    (h3q : 3 ∣ Nat.card K + 1) (w₀ : WeylGroup Tag.F4)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    {α β : Fin Tag.F4.rank → ℤ} (h : IsA2Pair α β) :
    ∃ E : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)),
      E ≤ a2FixedGroup (AlgebraicClosure K) f w₀ α β ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  obtain ⟨ρ, σ, hfr, h01, h12, hset⟩ := f4_exists_a2Frame h (AlgebraicClosure K)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (AlgebraicClosure K)).degree = 2 := by
    compute_degree!
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (AlgebraicClosure K))
    (by rw [hdeg]; norm_num)
  have hω' : ω ^ 2 + ω + 1 = 0 := by simpa [Polynomial.IsRoot, Polynomial.eval_add] using hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω'
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    simp at hω3
  have h2 : (2 : AlgebraicClosure K) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure K) 2
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1] at hω'
    have : (1 : AlgebraicClosure K) = 0 := by linear_combination hω' - h2
    exact one_ne_zero this
  set ζ : (AlgebraicClosure K)ˣ := Units.mk0 ω hω0 with hζ
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by simpa [hζ] using hω3)
  have hζ1 : ζ ≠ 1 := fun h1 => hω1 (by simpa [hζ] using congrArg Units.val h1)
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  set D₁ : Subgroup (AlgebraicClosure K)ˣ := Subgroup.zpowers ζ with hD₁
  have hD₁card : Nat.card D₁ = 3 := by rw [hD₁, Nat.card_zpowers, hord]
  let φ₂ : D₁ × D₁ →* ModGL Tag.F4 (AlgebraicClosure K) :=
    (ρ.comp (f4BDiagHom (AlgebraicClosure K))).comp (D₁.subtype.prodMap D₁.subtype)
  have hφ₂inj : Function.Injective φ₂ := by
    intro u v huv
    have h1 := hfr.injective huv
    have h2 := f4BDiagHom_injective (AlgebraicClosure K) h1
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h2)) (Subtype.ext (congrArg Prod.snd h2))
  have hu3 : ∀ u : D₁ × D₁, u ^ 3 = 1 := by
    intro u
    refine Prod.ext ?_ ?_
    · change u.1 ^ 3 = 1
      rw [← hD₁card]; exact pow_card_eq_one'
    · change u.2 ^ 3 = 1
      rw [← hD₁card]; exact pow_card_eq_one'
  refine ⟨φ₂.range, ?_, ?_, ?_⟩
  · rintro x ⟨u, rfl⟩
    have hdiag : φ₂ u ∈ torusGroup Tag.F4 (AlgebraicClosure K) :=
      hfr.diag _ (f4BDiagSL_offdiag _ _)
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdiag
    have hcube : φ₂ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
    have hb3 : ∀ i, b i ^ 3 = 1 := by
      have h1 : rootDiagUnit Tag.F4 (b ^ 3) = rootDiagUnit Tag.F4 (1 : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ) := by
        rw [← rootDiagUnit_pow, ← hb, hcube, rootDiagUnit_one]
      have h2 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
      intro i
      exact congrFun h2 i
    have hpow : ∀ x : (AlgebraicClosure K)ˣ, x ^ 3 = 1 → x ^ 2 ^ f = x⁻¹ := by
      intro x hx
      obtain ⟨k, hk⟩ := h3q
      rw [hq] at hk
      have h1 : x ^ 2 ^ f * x = 1 := by rw [← pow_succ, hk, pow_mul, hx, one_pow]
      exact eq_inv_of_mul_eq_one_left h1
    have hneg : ∀ v : Fin Tag.F4.rank → ℤ, rootChar b (-v) = (rootChar b v)⁻¹ := by
      intro v
      have := rootChar_add b (-v) v
      rw [neg_add_cancel, rootChar_zero] at this
      exact eq_inv_of_mul_eq_one_left this.symm
    have hw : ∀ v, rootChar b (w₀ • v) = rootChar b v ^ 2 ^ f := by
      intro v
      rw [hw₀, hneg, hpow _ (rootChar_pow_eq_one b hb3 v)]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hmem : φ₂ u ∈ ρ.range := ⟨_, rfl⟩
      rw [hfr.range, hset] at hmem
      exact hmem
    · rw [mem_langFixed, hb]
      exact (rootDiagUnit_eq_conj_frob 2 hw).symm
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, hu3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ₂inj).toEquiv, Nat.card_prod, hD₁card]

end Irred937

end CFSG.StandardType

end
