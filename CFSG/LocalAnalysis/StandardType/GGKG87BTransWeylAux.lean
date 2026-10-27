module

public import CFSG.LocalAnalysis.StandardType.GGKG87BTransDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs

public section

namespace CFSG.StandardType.KG87B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

private def vA2 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 0, 0, 0]

private def vB : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 3, 2, 1]

private def vA24 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 0, 0]

private def rhoE6 : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private def uWord : List (Fin Tag.E6.rank) := ([3, 4, 5, 2, 3, 4, 1, 3, 2] : List (Fin 6))

private def thirdWord : List (Fin Tag.E6.rank) :=
  ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3] : List (Fin 6))

private theorem smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

private theorem thirdCox_def :
    thirdCox = rootReflection vA2 * rootReflection vB :=
  rfl

private theorem rootReflection_vA2 :
    rootReflection vA2 = simple Tag.E6 1 := by
  rw [rootReflection_eq_conj (w := 1) (j := 1) (by rw [one_smul]; decide), one_mul, inv_one,
    mul_one]

private theorem rootReflection_vB :
    rootReflection vB = (coxeterSystem Tag.E6).wordProd uWord * simple Tag.E6 0 *
      ((coxeterSystem Tag.E6).wordProd uWord)⁻¹ :=
  rootReflection_eq_conj (by rw [smul_foldr]; decide)

private theorem thirdCox_eq :
    thirdCox = (coxeterSystem Tag.E6).wordProd thirdWord := by
  rw [thirdCox_def, rootReflection_vA2, rootReflection_vB, ← CoxeterSystem.wordProd_reverse]
  have e : thirdWord = [1] ++ uWord ++ [0] ++ uWord.reverse := by decide
  rw [e, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
    CoxeterSystem.wordProd_singleton]
  simp only [mul_assoc]

private theorem thirdCox_smul_single
    {i : Fin Tag.E6.rank} (h1 : i ≠ 1) (h3 : i ≠ 3) :
    thirdCox • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 := by
  rw [thirdCox_eq, smul_foldr]
  revert i
  decide

private theorem smul_eq_sum {τ : Tag} (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (Pi.single i (v i) : Fin τ.rank → ℤ) = v i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e, smul_comm]

private theorem thirdCox_smul_of_eq_zero
    {γ : Fin Tag.E6.rank → ℤ} (h1 : γ ⟨1, by decide⟩ = 0)
    (h3 : γ ⟨3, by decide⟩ = 0) : thirdCox • γ = γ := by
  rw [smul_eq_sum]
  conv_rhs => rw [← Finset.univ_sum_single γ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (Pi.single i (γ i) : Fin Tag.E6.rank → ℤ) = γ i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e]
  by_cases hi1 : i = 1
  · subst hi1
    rw [show γ 1 = 0 from h1, zero_smul, zero_smul]
  by_cases hi3 : i = 3
  · subst hi3
    rw [show γ 3 = 0 from h3, zero_smul, zero_smul]
  rw [thirdCox_smul_single hi1 hi3]

private theorem thirdCox_smul_vA24 :
    thirdCox • vA24 = Pi.single 3 1 := by
  rw [thirdCox_eq, smul_foldr]
  decide

private theorem thirdCox_inv_smul_coord :
    (thirdCox⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) 1 = 1 := by
  rw [inv_smul_eq_iff.2 thirdCox_smul_vA24.symm]
  rfl

private theorem weylTwist_thirdCox :
    weylTwist TwistTag.E6 thirdCox = thirdCox := by
  have h : weylTwist TwistTag.E6 ((coxeterSystem Tag.E6).wordProd thirdWord) =
      (coxeterSystem Tag.E6).wordProd (thirdWord.map rhoE6) :=
    weylTwist_wordProd TwistTag.E6 thirdWord
  rw [thirdCox_eq, h]
  refine ext_single fun i => ?_
  rw [smul_foldr, smul_foldr]
  revert i
  decide

private theorem w0_smul
    (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd e6W0Word • v = -(permLattice rhoE6 v) :=
  e6W0_smul v

private theorem w0_mul_thirdCox :
    (coxeterSystem Tag.E6).wordProd e6W0Word * thirdCox =
      thirdCox * (coxeterSystem Tag.E6).wordProd e6W0Word := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, w0_smul, w0_smul, thirdCox_eq, smul_foldr, smul_foldr]
  revert i
  decide

private theorem w0_inv_smul_single
    (i : Fin Tag.E6.rank) :
    ((coxeterSystem Tag.E6).wordProd e6W0Word)⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      -Pi.single (rhoE6 i) 1 := by
  rw [inv_smul_eq_iff, w0_smul]
  revert i
  decide

section Diag

variable {τ : Tag} {K : Type} [Field K]

private noncomputable def wTuple (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))

private theorem wTuple_apply (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    wTuple w b i = rootChar b (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
  rfl

private theorem rootChar_wTuple (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (wTuple w b) u = rootChar b (w⁻¹ • u) := by
  conv_rhs => rw [pi_eq_sum_univ u]
  rw [Finset.smul_sum, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm, rootChar_zsmul]
  rfl

private theorem conj_rootDiagUnit
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = rootDiagUnit τ (wTuple w b) :=
  ((rootDiagUnit_eq_conj_canonicalRep_iff (wTuple w b) b w).2 fun v => by
    rw [rootChar_wTuple, inv_smul_smul]).symm

private theorem rootChar_single (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar b (Pi.single i 1) = b i := by
  have h := rootChar_nsmul_single b i 1
  rwa [one_nsmul, pow_one] at h

private theorem rootChar_neg_single (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar b (-Pi.single i 1) = (b i)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul, rootChar_single]

private theorem rootChar_mulSingle (j : Fin τ.rank) (x : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle j x) v = x ^ v j := by
  rw [rootChar, Finset.prod_eq_single j
    (fun i _ hi => by rw [Pi.mulSingle_eq_of_ne hi, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

private noncomputable def diagHom : (Fin τ.rank → Kˣ) →* ModGL τ K where
  toFun := rootDiagUnit τ
  map_one' := rootDiagUnit_one
  map_mul' := rootDiagUnit_mul

private theorem rootDiagUnit_zpow (b : Fin τ.rank → Kˣ) (k : ℤ) :
    rootDiagUnit τ b ^ k = rootDiagUnit τ (b ^ k) :=
  (map_zpow (diagHom (τ := τ) (K := K)) b k).symm

private theorem rootDiagUnit_pow (b : Fin τ.rank → Kˣ) (k : ℕ) :
    rootDiagUnit τ b ^ k = rootDiagUnit τ (b ^ k) :=
  (map_pow (diagHom (τ := τ) (K := K)) b k).symm

end Diag

private theorem eq_one_of_shape {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ}
    (h0 : a ⟨0, by decide⟩ = 1) (h2 : a ⟨2, by decide⟩ = 1) (h4 : a ⟨4, by decide⟩ = 1)
    (h5 : a ⟨5, by decide⟩ = 1) {i : Fin Tag.E6.rank} (h1 : i ≠ 1) (h3 : i ≠ 3) : a i = 1 := by
  fin_cases i
  · exact h0
  · exact absurd rfl h1
  · exact h2
  · exact absurd rfl h3
  · exact h4
  · exact h5

private theorem wTuple_w0_of_shape
    {K : Type} [Field K]
    {a : Fin Tag.E6.rank → Kˣ} (h0 : a ⟨0, by decide⟩ = 1) (h2 : a ⟨2, by decide⟩ = 1)
    (h4 : a ⟨4, by decide⟩ = 1) (h5 : a ⟨5, by decide⟩ = 1) :
    wTuple ((coxeterSystem Tag.E6).wordProd e6W0Word) a = a⁻¹ := by
  funext i
  rw [wTuple_apply, w0_inv_smul_single, rootChar_neg_single, Pi.inv_apply]
  congr 1
  by_cases h1 : i = 1
  · rw [h1]
    rfl
  by_cases h3 : i = 3
  · rw [h3]
    rfl
  have hρ : rhoE6 i ≠ 1 ∧ rhoE6 i ≠ 3 := by
    revert i
    decide
  rw [eq_one_of_shape h0 h2 h4 h5 hρ.1 hρ.2, eq_one_of_shape h0 h2 h4 h5 h1 h3]

section CharTwo

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

private theorem weylElt_mul_canonicalRep_two
    (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq (1 : K)), torusElt_one, one_mul]

private theorem canonicalRep_wordProd_mul_two
    (ω : List (Fin τ.rank)) (v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω * v) =
      (ω.map fun i => weylElt τ K i 1).prod * canonicalRep (coxeterSystem τ) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_two, ih,
      List.map_cons, List.prod_cons, mul_assoc]

private theorem canonicalRep_mul_two
    (w v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K (w * v) =
      canonicalRep (coxeterSystem τ) K w * canonicalRep (coxeterSystem τ) K v := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd_mul_two, canonicalRep_wordProd hω]

end CharTwo

end CFSG.StandardType.KG87B

end
