module

import CFSG.LieType.SpecialLinear.SLModel.Models
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderFlip
import CFSG.LieType.SpecialLinear.FieldActor.ScalarIntertwiner
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.SLModel
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
open scoped TensorProduct

private theorem w183_eq_iterateFrobeniusEquiv_of_card_four {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 4) {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) :
    σ = iterateFrobeniusEquiv K 2 1 ∧ σ.trans σ = RingEquiv.refl K := by
  classical
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hK]
    simp [h10]
  obtain ⟨x, -, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
  obtain ⟨hx0, hx1⟩ := hxnot
  have hx1' : x + 1 ≠ 0 := by
    intro h
    have hx : x = 1 := by
      have h' : x + 1 + 1 = 0 + 1 := congrArg (fun t => t + 1) h
      simpa [add_assoc, CharTwo.add_self_eq_zero] using h'
    exact hx1 hx
  have h1x : x + 1 ≠ 1 := by
    intro h
    have h' : x + 1 = 0 + 1 := by rw [zero_add]; exact h
    exact hx0 (add_right_cancel h')
  have hxx : x + 1 ≠ x := by
    intro h
    have h' : x + 1 = x + 0 := by rw [add_zero]; exact h
    have h10' : (1 : K) = 0 := add_left_cancel h'
    exact h10 h10'
  have hcard4 : ({0, 1, x, x + 1} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [h10, hx0, hx1, hx1', h1x, hxx, Ne.symm hx0, Ne.symm hx1,
      Ne.symm hx1', Ne.symm h1x, Ne.symm hxx]
  have huniv : ({0, 1, x, x + 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard4]; exact hK.symm)
  have hx2 : x ^ 2 = x + 1 := by
    have hmem : x ^ 2 ∈ ({0, 1, x, x + 1} : Finset K) := by
      rw [huniv]; exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · have hz : x ^ 2 = 0 := h
      exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).1 hz) hx0
    · have : x = 1 ∨ x = -1 := by
        have h' : x ^ 2 - 1 = 0 := by rw [h]; ring
        exact (sq_eq_one_iff).1 (sub_eq_zero.1 h')
      rcases this with h1 | h1
      · exact absurd h1 hx1
      · rw [CharTwo.neg_eq] at h1; exact absurd h1 hx1
    · have : x * (x - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hx0
      · exact absurd (sub_eq_zero.1 h0) hx1
    · exact h
  have hmemσ : σ x ∈ ({0, 1, x, x + 1} : Finset K) := by
    rw [huniv]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmemσ
  have hσx : σ x = x + 1 := by
    rcases hmemσ with h | h | h | h
    · have : x = 0 := by
        have h' := congrArg σ.symm h
        simpa using h'
      exact absurd this hx0
    · have : x = 1 := by
        have h' := congrArg σ.symm h
        simpa using h'
      exact absurd this hx1
    ·
      exfalso
      apply hσ
      ext y
      have hymem : y ∈ ({0, 1, x, x + 1} : Finset K) := by
        rw [huniv]; exact Finset.mem_univ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
      rcases hymem with hy | hy | hy | hy
      · rw [hy, map_zero, RingEquiv.refl_apply]
      · rw [hy, map_one, RingEquiv.refl_apply]
      · rw [hy, h, RingEquiv.refl_apply]
      · rw [hy, map_add, h, map_one, RingEquiv.refl_apply]
    · exact h
  have hpoint : ∀ y : K, σ y = y ^ 2 := by
    intro y
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]; simp
    by_cases hy1 : y = 1
    · rw [hy1, map_one]; simp
    ·
      have hy1' : y + 1 ≠ 0 := by
        intro hh
        have hy : y = 1 := by
          have h' : y + 1 + 1 = 0 + 1 := congrArg (fun t => t + 1) hh
          simpa [add_assoc, CharTwo.add_self_eq_zero] using h'
        exact hy1 hy
      have h1y : y + 1 ≠ 1 := by
        intro hh
        have h' : y + 1 = 0 + 1 := by rw [zero_add]; exact hh
        exact hy0 (add_right_cancel h')
      have hyy : y + 1 ≠ y := by
        intro hh
        have h' : y + 1 = y + 0 := by rw [add_zero]; exact hh
        exact h10 (add_left_cancel h')
      have hcard4' : ({0, 1, y, y + 1} : Finset K).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        all_goals simp [h10, hy0, hy1, hy1', h1y, hyy, Ne.symm hy0, Ne.symm hy1,
          Ne.symm hy1', Ne.symm h1y, Ne.symm hyy]
      have huniv' : ({0, 1, y, y + 1} : Finset K) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hcard4']; exact hK.symm)
      have hy2 : y ^ 2 = y + 1 := by
        have hmem : y ^ 2 ∈ ({0, 1, y, y + 1} : Finset K) := by
          rw [huniv']; exact Finset.mem_univ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h
        · have hz : y ^ 2 = 0 := h
          exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).1 hz) hy0
        · have : y = 1 ∨ y = -1 := by
            have h' : y ^ 2 - 1 = 0 := by rw [h]; ring
            exact (sq_eq_one_iff).1 (sub_eq_zero.1 h')
          rcases this with h1 | h1
          · exact absurd h1 hy1
          · rw [CharTwo.neg_eq] at h1; exact absurd h1 hy1
        · have : y * (y - 1) = 0 := by linear_combination h
          rcases mul_eq_zero.1 this with h0 | h0
          · exact absurd h0 hy0
          · exact absurd (sub_eq_zero.1 h0) hy1
        · exact h
      have hmemσy : σ y ∈ ({0, 1, y, y + 1} : Finset K) := by
        rw [huniv']; exact Finset.mem_univ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemσy
      rcases hmemσy with h | h | h | h
      · have : y = 0 := by
          have h' := congrArg σ.symm h
          simpa using h'
        exact absurd this hy0
      · have : y = 1 := by
          have h' := congrArg σ.symm h
          simpa using h'
        exact absurd this hy1
      ·
        exfalso
        apply hσ
        ext z
        have hzmem : z ∈ ({0, 1, y, y + 1} : Finset K) := by
          rw [huniv']; exact Finset.mem_univ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
        rcases hzmem with hz | hz | hz | hz
        · rw [hz, map_zero, RingEquiv.refl_apply]
        · rw [hz, map_one, RingEquiv.refl_apply]
        · rw [hz, h, RingEquiv.refl_apply]
        · rw [hz, map_add, h, map_one, RingEquiv.refl_apply]
      · rw [h, hy2]
  constructor
  · ext y; rw [hpoint y, iterateFrobeniusEquiv_def]; norm_num
  · ext y
    rw [RingEquiv.trans_apply]
    rw [show σ (σ y) = σ y ^ 2 from hpoint (σ y), hpoint y]
    have hp : y ^ Fintype.card K = y := FiniteField.pow_card y
    rw [hK] at hp
    rw [RingEquiv.refl_apply]
    calc (y ^ 2) ^ 2 = y ^ 4 := by ring
      _ = y := by simpa using hp

private noncomputable def w183_swapEquiv (P : Type*) [Fintype P] (k : Type*) [Field k] :
    (P × P → k) ≃ₗ[k] (P × P → k) :=
  LinearEquiv.funCongrLeft k k (Equiv.prodComm P P)

private noncomputable def w183_piTensorEquiv (P : Type*) [Fintype P] [DecidableEq P]
    (k : Type*) [Field k] : ((P → k) ⊗[k] (P → k)) ≃ₗ[k] (P × P → k) :=
  (TensorProduct.piScalarRight k k (P → k) P).trans (LinearEquiv.curry k k P P).symm

private theorem w183_piTensorEquiv_comm (P : Type*) [Fintype P] [DecidableEq P]
    (k : Type*) [Field k] (x : (P → k) ⊗[k] (P → k)) :
    w183_piTensorEquiv P k (TensorProduct.comm k (P → k) (P → k) x) =
      w183_swapEquiv P k (w183_piTensorEquiv P k x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    funext p
    simp [w183_piTensorEquiv, w183_swapEquiv, Function.uncurry]
  | tmul a b =>
    funext p
    simp [w183_piTensorEquiv, w183_swapEquiv, TensorProduct.piScalarRight,
      LinearEquiv.curry, TensorProduct.comm_tmul, Function.uncurry, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem w183_finrank_range_swap_sub_one (P : Type) [Fintype P] [DecidableEq P]
    (k : Type*) [Field k] :
    Module.finrank k (LinearMap.range ((w183_swapEquiv P k).toLinearMap - 1)) =
      Fintype.card P * (Fintype.card P - 1) / 2 := by
  classical
  let S := w183_swapEquiv P k
  let φ := w183_piTensorEquiv P k
  let τ : (P → k) ⊗[k] (P → k) →ₗ[k] (P → k) ⊗[k] (P → k) :=
    (TensorProduct.comm k (P → k) (P → k)).toLinearMap - 1
  have hcomm' : ∀ y, φ ((TensorProduct.comm k (P → k) (P → k)).toLinearMap y) = S (φ y) :=
    fun y => w183_piTensorEquiv_comm P k y
  have hconj : S.toLinearMap - 1 = φ.toLinearMap.comp (τ.comp φ.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    set y := φ.symm x with hy
    have hx : φ y = x := by rw [hy, LinearEquiv.apply_symm_apply]
    change S x - x = φ (τ (φ.symm x))
    rw [← hy]
    rw [← hx]
    rw [show τ y = (TensorProduct.comm k (P → k) (P → k)).toLinearMap y - y from rfl]
    rw [map_sub, hcomm' y]
  have hrange : LinearMap.range (S.toLinearMap - 1) =
      (LinearMap.range τ).map φ.toLinearMap := by
    rw [hconj, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr φ.symm.surjective, Submodule.map_top]
  rw [hrange, LinearEquiv.finrank_map_eq]
  have hτ := CFSG.QuasithinUnique.Setup.Offender.finrank_range_flip_sub_id
    (F := k) (U := (P → k))
  have hdim : Module.finrank k (P → k) = Fintype.card P :=
    Module.finrank_fintype_fun_eq_card k
  rw [hdim] at hτ
  exact hτ

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.SLModel
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
open scoped TensorProduct Kronecker

theorem exists_flip_involution_pair {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {k : Type} [Field k] [CharP k 2] [Algebra K k]
    {ε : Fin 2 → Finset (Fin 4)} {j : Fin 4} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 3)
    (h0 : ε 0 = {j}) (h1 : ε 1 = {j}) {σ : K ≃+* K} (hσ1 : σ ≠ RingEquiv.refl K) :
    ∃ T : BModel k ε ≃ₗ[k] BModel k ε, T * T = 1 ∧
      (∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
        T (slModelRep (F := K) (k := k) ε x v) =
          slModelRep (F := K) (k := k) ε (Matrix.SpecialLinearGroup.map σ.toRingHom x) (T v)) ∧
      Module.finrank k (LinearMap.range (T.toLinearMap - 1)) = 6 := by
  classical
  obtain ⟨hσeq, hσ2⟩ := w183_eq_iterateFrobeniusEquiv_of_card_four hK hσ1
  let P := Set.powersetCard (Fin 4) j
  have hrest : ∀ r : Fin 2, r ≠ 0 → r ≠ 1 → ε r = ∅ := by
    intro r hr0 hr1
    fin_cases r <;> simp_all
  obtain ⟨β, hβ⟩ := exists_equiv_pair (F := K) (k := k) (m := 3) (f := 2) ε
    (r₀ := 0) (r₁ := 1) (by decide) h0 h1 hrest
  let R := slModelRep (F := K) (k := k) ε
  let S := w183_swapEquiv P k
  let T : BModel k ε ≃ₗ[k] BModel k ε := β.trans (S.trans β.symm)
  let Mfun : Matrix (Fin 4) (Fin 4) K → Matrix (P × P) (P × P) k := fun g =>
    (((minorMatrix (j : ℕ) g).map (iterateFrobeniusEquiv K 2 0)) ⊗ₖ
      ((minorMatrix (j : ℕ) g).map (iterateFrobeniusEquiv K 2 1))).map (algebraMap K k)
  have hcomp : (σ : K → K) ∘ σ = id := by
    funext y
    have h := congrArg (fun e : K ≃+* K => e y) hσ2
    simpa [RingEquiv.trans_apply] using h
  have hM : ∀ g : Matrix (Fin 4) (Fin 4) K,
      Mfun g = ((minorMatrix (j : ℕ) g) ⊗ₖ
        ((minorMatrix (j : ℕ) g).map σ)).map (algebraMap K k) := by
    intro g
    dsimp only [Mfun]
    have h0' : (⇑(iterateFrobeniusEquiv K 2 0) : K → K) = id := by
      funext y; exact iterateFrobeniusEquiv_zero_apply (R := K) (p := 2) y
    have h1' : (⇑(iterateFrobeniusEquiv K 2 1) : K → K) = ⇑σ := by
      funext y; rw [hσeq]
    rw [h0', h1']
    rfl
  have hMσ : ∀ g : Matrix (Fin 4) (Fin 4) K,
      Mfun (g.map σ.toRingHom) =
        (((minorMatrix (j : ℕ) g).map σ) ⊗ₖ (minorMatrix (j : ℕ) g)).map
          (algebraMap K k) := by
    intro g
    dsimp only [Mfun]
    have h0' : (⇑(iterateFrobeniusEquiv K 2 0) : K → K) = id := by
      funext y; exact iterateFrobeniusEquiv_zero_apply (R := K) (p := 2) y
    have h1' : (⇑(iterateFrobeniusEquiv K 2 1) : K → K) = ⇑σ := by
      funext y; rw [hσeq]
    rw [h0', h1']
    rw [minorMatrix_map]
    simp only [Matrix.map_map, Function.id_comp]
    have hσto : (⇑σ.toRingHom : K → K) = ⇑σ := rfl
    rw [hσto]
    have hcomp' : (⇑σ ∘ ⇑σ) = id := hcomp
    rw [hcomp']
    simp only [Matrix.map_id]
  have hβM : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      β (R x v) = Matrix.mulVec (Mfun (x : Matrix (Fin 4) (Fin 4) K)) (β v) := by
    intro x v
    exact hβ x v
  have hswap : ∀ (B C : Matrix P P K) (f : P × P → k),
      S (Matrix.mulVec (((B ⊗ₖ C).map (algebraMap K k))) f) =
        Matrix.mulVec (((C ⊗ₖ B).map (algebraMap K k))) (S f) := by
    intro B C f
    dsimp only [S]
    ext p
    simp only [w183_swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Equiv.prodComm_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [mul_comm (B p.2 b) (C p.1 a)]
    rfl
  have hinter : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      T (R x v) = R (Matrix.SpecialLinearGroup.map σ.toRingHom x) (T v) := by
    intro x v
    apply β.injective
    change β (β.symm (S (β (R x v)))) =
      β (R (Matrix.SpecialLinearGroup.map σ.toRingHom x) (β.symm (S (β v))))
    rw [LinearEquiv.apply_symm_apply, hβM x v, hβM _ (β.symm (S (β v))),
      LinearEquiv.apply_symm_apply]
    rw [hM (x : Matrix (Fin 4) (Fin 4) K)]
    rw [show ((Matrix.SpecialLinearGroup.map σ.toRingHom x :
        Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (x : Matrix (Fin 4) (Fin 4) K).map σ.toRingHom from rfl]
    rw [hMσ (x : Matrix (Fin 4) (Fin 4) K)]
    exact hswap _ _ _
  have hSS : ∀ g : P × P → k, S (S g) = g := by
    intro g
    ext p
    simp [S, w183_swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  refine ⟨T, ?_, hinter, ?_⟩
  · apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply]
    change T (T v) = v
    dsimp only [T]
    simp only [LinearEquiv.trans_apply]
    rw [LinearEquiv.apply_symm_apply, hSS, LinearEquiv.symm_apply_apply]
  · have hconj : T.toLinearMap - (1 : BModel k ε →ₗ[k] BModel k ε) =
        β.symm.toLinearMap.comp ((S.toLinearMap - (1 : (P × P → k) →ₗ[k] (P × P → k))).comp
          β.toLinearMap) := by
      apply LinearMap.ext
      intro x
      change β.symm (S (β x)) - x = β.symm (S (β x) - β x)
      rw [map_sub, LinearEquiv.symm_apply_apply]
    have hrange : LinearMap.range (T.toLinearMap - (1 : BModel k ε →ₗ[k] BModel k ε)) =
        (LinearMap.range (S.toLinearMap - (1 : (P × P → k) →ₗ[k] (P × P → k)))).map
          β.symm.toLinearMap := by
      rw [hconj, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr β.surjective, Submodule.map_top]
    rw [hrange, LinearEquiv.finrank_map_eq, w183_finrank_range_swap_sub_one P k]
    have hcardP : Fintype.card P = 4 := by
      simp only [P]
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_fin]
      rcases hj with h | h <;> rw [h] <;> norm_num
    rw [hcardP]

theorem eq_of_involution_intertwiners {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {k : Type} [Field k] [CharP k 2] [Algebra K k]
    {ε : Fin 2 → Finset (Fin 4)} {j : Fin 4} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 3)
    (h0 : ε 0 = {j}) (h1 : ε 1 = {j}) {σ : K ≃+* K} (hσ1 : σ ≠ RingEquiv.refl K)
    {T D : BModel k ε ≃ₗ[k] BModel k ε} (hT2 : T * T = 1)
    (hT : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      T (slModelRep (F := K) (k := k) ε x v) =
        slModelRep (F := K) (k := k) ε (Matrix.SpecialLinearGroup.map σ.toRingHom x) (T v))
    (hD2 : D * D = 1)
    (hD : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      D (slModelRep (F := K) (k := k) ε x v) =
        slModelRep (F := K) (k := k) ε (Matrix.SpecialLinearGroup.map σ.toRingHom x) (D v)) :
    D = T := by
  classical
  have hF : Fintype.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hρ : IsSimpleRep (slModelRep (F := K) (k := k) ε) :=
    isSimpleRep_slModelRep (F := K) (k := k) hF ε
  let Dd := (coverId 3 K 2).datum
  haveI : Finite ((CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3)).Group) :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3)
  have ht := isCoverType_slModelRep (F := K) (k := k) (m := 3) (f := 2) hF ε
  have hsplit : SplitOver k (Dd.H.comap (MonoidHom.id (Matrix.SpecialLinearGroup (Fin 4) K))) := by
    have h := splitOver (F := K) 3 2 k
    rwa [Subgroup.comap_id] at h
  obtain ⟨μ, hμ⟩ := IsCoverType.exists_mu (R := rankOne 3 K 2) hρ hsplit ht
  have hfix : Module.finrank k (fixSub (slModelRep (F := K) (k := k) ε) Dd.U) = 1 := by
    have hspan : Dd.fixU (slModelRep (F := K) (k := k) ε) =
        Submodule.span k {bTop (k := k) ε} :=
      Dd.fixU_eq_span hρ hμ
    rw [show fixSub (slModelRep (F := K) (k := k) ε) Dd.U =
        Dd.fixU (slModelRep (F := K) (k := k) ε) from rfl, hspan, finrank_span_singleton]
    exact bTop_ne_zero (k := k) ε
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 4) K) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
      (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
      (MonoidHom.ext fun X => by ext i j; simp)
      (MonoidHom.ext fun X => by ext i j; simp)
  have hα : ∀ x, α x = Matrix.SpecialLinearGroup.map σ.toRingHom x := fun x => rfl
  have hTα : ∀ (g : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      T (slModelRep (F := K) (k := k) ε g v) =
        slModelRep (F := K) (k := k) ε (α g) (T v) := by
    intro g v
    rw [hα g]
    exact hT g v
  have hDα : ∀ (g : Matrix.SpecialLinearGroup (Fin 4) K) (v : BModel k ε),
      D (slModelRep (F := K) (k := k) ε g v) =
        slModelRep (F := K) (k := k) ε (α g) (D v) := by
    intro g v
    rw [hα g]
    exact hD g v
  exact eq_of_mul_self_eq_one (ρ := slModelRep (F := K) (k := k) ε) (U := Dd.U)
    hρ hfix hDα hTα hD2 hT2

theorem exists_modelInvolution_of_fieldAut_involution {K : Type} [Field K] [Fintype K]
    [CharP K 2] {f m : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) = 2)
    {σ : K ≃+* K} {d : W ≃ₗ[ZMod 2] W} (hd2 : d * d = 1)
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (w : W),
      d (ρ x w) = ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x) (d w)) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k 2) (_ : Algebra K k)
      (D : BModel k ε ≃ₗ[k] BModel k ε), D * D = 1 ∧
      (∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (v : BModel k ε),
        D (slModelRep (F := K) (k := k) ε x v) =
          slModelRep (F := K) (k := k) ε (Matrix.SpecialLinearGroup.map σ.toRingHom x) (D v)) ∧
      Module.finrank k (LinearMap.range (D.toLinearMap - 1)) =
        Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1)) := by
  classical
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, y, χ, J, h0', ht, hχ, hJ, β, hβ⟩ := hε
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra (Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) k := hEalg
  letI : Algebra K k := hKalg
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  letI : Field E := CFSG.endField_field ρ
  letI : Finite E := CFSG.endField_finite ρ
  letI : Module E ρ.asModule := CFSG.endFieldModule ρ
  letI : Module.Finite (ZMod 2) ρ.asModule := Representation.instFiniteAsModule ρ
  letI : FiniteDimensional E ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) E ρ.asModule
  have hE2 : ∀ c : E, c = 0 ∨ c = 1 := by
    intro c
    haveI : Fintype E := Fintype.ofFinite E
    have hcard : Fintype.card E = 2 := by rwa [Fintype.card_eq_nat_card]
    have h01 : ({0, 1} : Finset E) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard]
      simp [zero_ne_one]
    have hmem : c ∈ ({0, 1} : Finset E) := by rw [h01]; exact Finset.mem_univ c
    simpa using hmem
  let δ : ρ.asModule →ₗ[ZMod 2] ρ.asModule := transportEnd ρ d.toLinearMap
  have hδE : ∀ (c : E) (x : ρ.asModule), δ (c • x) = c • δ x := by
    intro c x
    rcases hE2 c with h | h
    · rw [h, zero_smul, zero_smul, map_zero]
    · rw [h, one_smul, one_smul]
  let δE : ρ.asModule →ₗ[E] ρ.asModule :=
    { toFun := δ
      map_add' := δ.map_add
      map_smul' := hδE }
  have hdd : ∀ w : W, d (d w) = w := by
    intro w
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) hd2
    simpa [LinearEquiv.mul_apply] using h
  have hδδ : ∀ x : ρ.asModule, δE (δE x) = x := by
    intro x
    change δ (δ x) = x
    simp only [δ, transportEnd_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.apply_symm_apply, hdd, LinearEquiv.symm_apply_apply]
  let δe : ρ.asModule ≃ₗ[E] ρ.asModule := LinearEquiv.ofInvolutive δE hδδ
  have hδe_coe : ∀ x, δe x = δE x := fun x => rfl
  have hδ_int : ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (v : ρ.asModule),
      δE (endFieldRep ρ x v) =
        endFieldRep ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x) (δE v) := by
    intro x v
    have hδapp : ∀ y : ρ.asModule, ρ.asModuleEquiv (δE y) = d (ρ.asModuleEquiv y) := by
      intro y
      simp [δE, δ, transportEnd_apply]
    apply ρ.asModuleEquiv.injective
    rw [hδapp (endFieldRep ρ x v), endFieldRep_apply', endFieldRep_apply']
    rw [hδapp v]
    exact hd x (ρ.asModuleEquiv v)
  let D0 : (k ⊗[E] ρ.asModule) ≃ₗ[k] (k ⊗[E] ρ.asModule) :=
    LinearEquiv.baseChange E k ρ.asModule ρ.asModule δe
  have hD0_int : ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K)
      (w : k ⊗[E] ρ.asModule),
      D0 (Theory.Representation.extendScalars k (endFieldRep ρ) x w) =
        Theory.Representation.extendScalars k (endFieldRep ρ)
          (Matrix.SpecialLinearGroup.map σ.toRingHom x) (D0 w) := by
    intro x w
    induction w using TensorProduct.induction_on with
    | zero => simp [D0]
    | tmul a v =>
      change (LinearEquiv.baseChange E k ρ.asModule ρ.asModule δe)
        ((LinearMap.baseChange k (endFieldRep ρ x)) (a ⊗ₜ[E] v)) =
        (LinearMap.baseChange k (endFieldRep ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x)))
          (a ⊗ₜ[E] δe v)
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
      rw [show δe (endFieldRep ρ x v) =
          endFieldRep ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x) (δe v) from hδ_int x v]
    | add p q hp hq => simp only [map_add, hp, hq]
  let D : BModel k ε ≃ₗ[k] BModel k ε := β.symm.trans (D0.trans β)
  have hD2 : D * D = 1 := by
    have hD0D0 : D0 * D0 = 1 := by
      have hδe2 : δe * δe = 1 := by
        apply LinearEquiv.ext
        intro x
        rw [LinearEquiv.mul_apply, hδe_coe, hδe_coe]
        exact hδδ x
      dsimp only [D0]
      rw [← LinearEquiv.baseChange_mul E k ρ.asModule δe δe, hδe2,
        LinearEquiv.baseChange_one E k ρ.asModule]
    apply LinearEquiv.ext
    intro v
    change D (D v) = v
    simp only [D, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← LinearEquiv.mul_apply, hD0D0]
    simp
  have hD_int : ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (v : BModel k ε),
      D (slModelRep (F := K) (k := k) ε x v) =
        slModelRep (F := K) (k := k) ε (Matrix.SpecialLinearGroup.map σ.toRingHom x) (D v) := by
    intro x v
    have hβinv : ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (w : BModel k ε),
        β.symm (slModelRep (F := K) (k := k) ε x w) =
          Theory.Representation.extendScalars k (endFieldRep ρ) x (β.symm w) := by
      intro x w
      apply β.injective
      rw [LinearEquiv.apply_symm_apply, hβ x (β.symm w), LinearEquiv.apply_symm_apply]
    apply β.symm.injective
    rw [show β.symm (D (slModelRep (F := K) (k := k) ε x v)) =
        D0 (Theory.Representation.extendScalars k (endFieldRep ρ) x (β.symm v)) from by
      simp only [D, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rw [hβinv]]
    rw [hβinv (Matrix.SpecialLinearGroup.map σ.toRingHom x) (D v)]
    rw [show β.symm (D v) = D0 (β.symm v) from by
      simp only [D, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]]
    exact hD0_int x (β.symm v)
  have hDrank : Module.finrank k (LinearMap.range (D.toLinearMap - 1)) =
      Module.finrank k (LinearMap.range (D0.toLinearMap - 1)) := by
    have hconj : D.toLinearMap - (1 : BModel k ε →ₗ[k] BModel k ε) =
        β.toLinearMap.comp ((D0.toLinearMap -
          (1 : (k ⊗[E] ρ.asModule) →ₗ[k] (k ⊗[E] ρ.asModule))).comp β.symm.toLinearMap) := by
      apply LinearMap.ext
      intro v
      change β (D0 (β.symm v)) - v = β (D0 (β.symm v) - β.symm v)
      rw [map_sub, LinearEquiv.apply_symm_apply]
    have hrange : LinearMap.range (D.toLinearMap - 1) =
        (LinearMap.range (D0.toLinearMap -
          (1 : (k ⊗[E] ρ.asModule) →ₗ[k] (k ⊗[E] ρ.asModule)))).map β.toLinearMap := by
      rw [hconj, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr β.symm.surjective, Submodule.map_top]
    rw [hrange, LinearEquiv.finrank_map_eq]
  have hD0sub : D0.toLinearMap - (1 : (k ⊗[E] ρ.asModule) →ₗ[k] (k ⊗[E] ρ.asModule)) =
      (δe.toLinearMap - (1 : ρ.asModule →ₗ[E] ρ.asModule)).baseChange k := by
    rw [show D0.toLinearMap = (δe.toLinearMap).baseChange k from
      LinearEquiv.coe_baseChange E k ρ.asModule ρ.asModule δe]
    rw [← LinearMap.baseChange_one, ← LinearMap.baseChange_sub]
  have hbaseRank : Module.finrank k (LinearMap.range
      ((δe.toLinearMap - (1 : ρ.asModule →ₗ[E] ρ.asModule)).baseChange k)) =
      Module.finrank E (LinearMap.range
        (δe.toLinearMap - (1 : ρ.asModule →ₗ[E] ρ.asModule))) := by
    set f : ρ.asModule →ₗ[E] ρ.asModule := δe.toLinearMap - 1 with hf
    have hker : Module.finrank k (LinearMap.ker (f.baseChange k)) =
        Module.finrank E (LinearMap.ker f) := by
      rw [← (LinearMap.kerBaseChangeEquiv (F := E) (E := k) f).finrank_eq,
        Module.finrank_baseChange]
    have hwhole : Module.finrank k (k ⊗[E] ρ.asModule) = Module.finrank E ρ.asModule :=
      Module.finrank_baseChange
    have h1 := LinearMap.finrank_range_add_finrank_ker (f.baseChange k)
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    omega
  have hErange : Module.finrank E (LinearMap.range
      (δe.toLinearMap - (1 : ρ.asModule →ₗ[E] ρ.asModule))) =
      Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1)) := by
    let S : Submodule E ρ.asModule := LinearMap.range
      (δe.toLinearMap - (1 : ρ.asModule →ₗ[E] ρ.asModule))
    let T : Submodule (ZMod 2) ρ.asModule :=
      (LinearMap.range (d.toLinearMap - 1)).map
        (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap
    have hδ_eq : transportEnd ρ d.toLinearMap - (1 : ρ.asModule →ₗ[ZMod 2] ρ.asModule) =
        (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap.comp
          ((d.toLinearMap - 1).comp
            (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap) := by
      apply LinearMap.ext
      intro x
      change transportEnd ρ d.toLinearMap x - x =
        ρ.asModuleEquiv.symm (d (ρ.asModuleEquiv x) - ρ.asModuleEquiv x)
      rw [transportEnd_apply, map_sub, LinearEquiv.symm_apply_apply]
      rfl
    have hrangeδ : LinearMap.range (transportEnd ρ d.toLinearMap -
        (1 : ρ.asModule →ₗ[ZMod 2] ρ.asModule)) = T := by
      rw [hδ_eq, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr ρ.asModuleEquiv.surjective, Submodule.map_top]
    have hST : (S : Set ρ.asModule) = (T : Set ρ.asModule) := by
      have hcoe : (S : Set ρ.asModule) = (LinearMap.range (transportEnd ρ d.toLinearMap -
          (1 : ρ.asModule →ₗ[ZMod 2] ρ.asModule)) : Set ρ.asModule) := rfl
      rw [hcoe, hrangeδ]
    have hcardEq : Nat.card S = Nat.card T :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        show x ∈ (S : Set ρ.asModule) ↔ x ∈ (T : Set ρ.asModule)
        rw [hST]))
    have hcardS : Nat.card S = 2 ^ Module.finrank E S := by
      have := Module.natCard_eq_pow_finrank (K := E) (V := S)
      rwa [hE] at this
    have hcardT : Nat.card T = 2 ^ Module.finrank (ZMod 2) T := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := T)
      simpa using h
    have hpow : 2 ^ Module.finrank E S = 2 ^ Module.finrank (ZMod 2) T := by
      rw [← hcardS, ← hcardT, hcardEq]
    have hdim : Module.finrank E S = Module.finrank (ZMod 2) T :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    have hTrank : Module.finrank (ZMod 2) T =
        Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1)) := by
      rw [show T = (LinearMap.range (d.toLinearMap - 1)).map
          (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap from rfl]
      rw [LinearEquiv.finrank_map_eq]
    change Module.finrank E S =
      Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1))
    rw [hdim, hTrank]
  refine ⟨k, hfield, hcharp, hKalg, D, hD2, hD_int, ?_⟩
  rw [hDrank, hD0sub, hbaseRank, hErange]

theorem six_le_finrank_range_sub_one_of_fieldAut {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] {ε : Fin 2 → Finset (Fin 4)} (hε : HasTwistedLabel ρ ε)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
      ρ.asModule) = 2)
    {j : Fin 4} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 3) (h0 : ε 0 = {j}) (h1 : ε 1 = {j})
    {σ : K ≃+* K} (hσ1 : σ ≠ RingEquiv.refl K) {d : W ≃ₗ[ZMod 2] W} (hd2 : d * d = 1)
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin 4) K) (w : W),
      d (ρ x w) = ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x) (d w)) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1)) := by
  obtain ⟨k, _, _, _, D, hD2, hD, hrank⟩ :=
    exists_modelInvolution_of_fieldAut_involution ρ hε hE hd2 hd
  obtain ⟨T, hT2, hT, hTrank⟩ := exists_flip_involution_pair hK (k := k) hj h0 h1 hσ1
  have hDT : D = T := eq_of_involution_intertwiners hK hj h0 h1 hσ1 hT2 hT hD2 hD
  have h6 : Module.finrank (ZMod 2) (LinearMap.range (d.toLinearMap - 1)) = 6 := by
    rw [← hrank, hDT, hTrank]
  omega

end CFSG.LocalAnalysis.WeakClosure81
