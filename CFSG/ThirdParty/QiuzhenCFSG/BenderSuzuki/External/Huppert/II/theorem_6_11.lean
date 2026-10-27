module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Independence

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.6.11

The projective special linear group acts doubly transitively on projective
space.  The finite-field degree formula is recorded separately.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped LinearAlgebra.Projectivization

universe u

private instance huppert611SLDistribMulAction
    {K : Type u} [Field K] (n : ℕ) :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin n) K) (Fin n → K) :=
  DistribMulAction.compHom (Fin n → K)
    (Matrix.SpecialLinearGroup.toLin' :
      Matrix.SpecialLinearGroup (Fin n) K →* (Fin n → K) ≃ₗ[K] (Fin n → K))

private instance huppert611SLSMulCommClass
    {K : Type u} [Field K] (n : ℕ) :
    SMulCommClass (Matrix.SpecialLinearGroup (Fin n) K) K (Fin n → K) where
  smul_comm A c v := (Matrix.SpecialLinearGroup.toLin' A).map_smul c v

private theorem huppert611_center_mem_projective_perm_ker
    {K : Type u} [Field K] (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) K)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) :
    A ∈ (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin n) K)
      (ℙ K (Fin n → K))).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
      obtain ⟨r, _hrpow, hscalar⟩ :=
        Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      rw [Equiv.Perm.coe_one, id_eq]
      change A • Projectivization.mk K v hv = Projectivization.mk K v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨r, ?_⟩
      change r • v = (Matrix.SpecialLinearGroup.toLin' A) v
      rw [Matrix.SpecialLinearGroup.toLin'_apply]
      funext i
      rw [← hscalar]
      simp [Matrix.toLin'_apply]

private theorem huppert611_mem_center_of_projective_trivial
    {K : Type u} [Field K] (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) K)
    (hfix : ∀ x : ℙ K (Fin n → K), A • x = x) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hcolinear :
      ∀ v : Fin n → K,
        ¬ LinearIndependent K ![v, (Matrix.SpecialLinearGroup.toLin' A) v] := by
    intro v
    by_cases hv : v = 0
    · subst v
      intro hli
      exact (hli.ne_zero 0) rfl
    · rw [LinearIndependent.pair_iff' hv]
      simp only [not_forall, not_not]
      have hp := hfix (Projectivization.mk K v hv)
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hp
      exact hp
  obtain ⟨c, hc⟩ :=
    LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := (Matrix.SpecialLinearGroup.toLin' A).toLinearMap) hcolinear
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨c, ?_, ?_⟩
  · have hdet :
        LinearMap.det (Matrix.SpecialLinearGroup.toLin' A).toLinearMap = 1 := by
      rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.det_toLin']
      exact A.property
    rw [hc] at hdet
    simpa using hdet
  · have hm := congrArg LinearMap.toMatrix' hc
    have hm' : (A : Matrix (Fin n) (Fin n) K) =
        c • (1 : Matrix (Fin n) (Fin n) K) := by
      simpa [Matrix.SpecialLinearGroup.toLin'_to_linearMap,
        LinearMap.toMatrix_id] using hm
    calc
      Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
        simpa using (Matrix.smul_one_eq_diagonal (m := Fin n) c).symm
      _ = (A : Matrix (Fin n) (Fin n) K) := hm'.symm

@[simp] private theorem huppert611_trans_apply
    {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) (x : α) :
    (Trans.trans e f) x = f (e x) := rfl

@[simp] private theorem huppert611_sumCongr_inl
    {α β γ δ : Type*} (e : α ≃ β) (f : γ ≃ δ) (x : α) :
    Equiv.sumCongr e f (Sum.inl x) = Sum.inl (e x) := rfl

private def huppert611_pairIndex {n : ℕ} (hn : 2 ≤ n) (i : Fin 2) : Fin n :=
  finCongr (Nat.add_sub_of_le hn) (finSumFinEquiv (Sum.inl i))

@[simp] private theorem huppert611_reindexEquiv_pairIndex
    {n : ℕ} (hn : 2 ≤ n) {E : Type*} (eTail : Fin (n - 2) ≃ E) (i : Fin 2) :
    ((finCongr (Nat.add_sub_of_le hn).symm).trans <|
      finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) eTail))
        (huppert611_pairIndex hn i) = Sum.inl i := by
  simp only [huppert611_pairIndex, Equiv.trans_apply]
  have hcast :
      finCongr (Nat.add_sub_of_le hn).symm
          (finCongr (Nat.add_sub_of_le hn) (finSumFinEquiv (Sum.inl i))) =
        finSumFinEquiv (Sum.inl i) := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv.symm_apply_apply]
  rfl

@[simp] private theorem huppert611_sumExtend_apply_inl
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {v : Fin 2 → V} (hv : LinearIndependent K v) (i : Fin 2) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  classical
  unfold Module.Basis.sumExtend
  dsimp only
  rw [Module.Basis.reindex_apply]
  let s := Set.range v
  let e : Fin 2 ≃ s := Equiv.ofInjective v hv.injective
  let b := hv.linearIndepOn_id.extend (Set.subset_univ s)
  change (Module.Basis.extend hv.linearIndepOn_id)
    ((Trans.trans (Equiv.sumCongr e (Equiv.refl {x : V // x ∈ b \ s}))
      (Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)))
        (Sum.inl i)) = v i
  have happ :
      (Trans.trans (Equiv.sumCongr e (Equiv.refl {x : V // x ∈ b \ s}))
        (Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)))
          (Sum.inl i) =
        Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)
          (Sum.inl (e i)) := rfl
  rw [happ, Equiv.Set.sumDiffSubset_apply_inl,
    Module.Basis.extend_apply_self]
  rfl

private noncomputable def huppert611_projectivePairBasis
    {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (a b : ℙ K (Fin n → K)) (hab : a ≠ b) :
    Module.Basis (Fin n) K (Fin n → K) := by
  let v : Fin 2 → (Fin n → K) := Projectivization.rep ∘ ![a, b]
  have hv : LinearIndependent K v := by
    have hp : Projectivization.Independent ![a, b] :=
      (Projectivization.independent_pair_iff_ne a b).2 hab
    exact Projectivization.independent_iff.mp hp
  let bs := Module.Basis.sumExtend hv
  let E := Module.Basis.sumExtendIndex hv
  letI : Fintype (Fin 2 ⊕ E) :=
    bs.fintypeIndexOfRankLtAleph0 (by simp)
  letI : Finite E := Finite.of_injective
    (fun x : E => (Sum.inr x : Fin 2 ⊕ E))
    (fun _ _ h => Sum.inr.inj h)
  letI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = n - 2 := by
    have hdim := Module.finrank_eq_card_basis bs
    have hdim' : n = Nat.card (Fin 2 ⊕ E) := by
      simpa [E, bs, Nat.card_eq_fintype_card] using hdim
    rw [Nat.card_sum, Nat.card_fin] at hdim'
    rw [Nat.card_eq_fintype_card] at hdim'
    omega
  let eTail : Fin (n - 2) ≃ E := Fintype.equivOfCardEq (by simpa using hcardE.symm)
  have hsum : 2 + (n - 2) = n := Nat.add_sub_of_le hn
  let e : Fin n ≃ Fin 2 ⊕ E :=
    (finCongr hsum.symm).trans <|
      (finSumFinEquiv).symm.trans (Equiv.sumCongr (Equiv.refl _) eTail)
  exact bs.reindex e.symm

private theorem huppert611_projectivePairBasis_pairIndex
    {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (a b : ℙ K (Fin n → K)) (hab : a ≠ b) (i : Fin 2) :
    huppert611_projectivePairBasis hn a b hab (huppert611_pairIndex hn i) =
      ![a.rep, b.rep] i := by
  classical
  simp only [huppert611_projectivePairBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  rw [huppert611_reindexEquiv_pairIndex]
  rw [huppert611_sumExtend_apply_inl]
  fin_cases i <;> rfl

/-- Huppert II.6.11: the natural faithful action of `PSL(n,K)` on projective
space is doubly transitive. -/
public theorem huppert_II_6_11_projective_action
    {K : Type u} [Field K] (n : ℕ) (hn : 2 ≤ n) :
    let SL := Matrix.SpecialLinearGroup (Fin n) K
    let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
    let P := ℙ K (Fin n → K)
    ∃ rho : PSL →* Equiv.Perm P,
      Function.Injective rho ∧
      (∀ (A : SL) (z : P),
        rho (QuotientGroup.mk' (Subgroup.center SL) A) z =
          (Matrix.GeneralLinearGroup.toLin
            (A : GL (Fin n) K)).toLinearEquiv • z) ∧
      (∀ a b c d : P, a ≠ b → c ≠ d →
        ∃ g : PSL, rho g a = c ∧ rho g b = d) := by
  classical
  dsimp only
  let SL := Matrix.SpecialLinearGroup (Fin n) K
  let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
  let P := ℙ K (Fin n → K)
  let permHom : SL →* Equiv.Perm P := MulAction.toPermHom SL P
  let hcenter_le_ker : Subgroup.center SL ≤ permHom.ker := by
    intro A hA
    exact huppert611_center_mem_projective_perm_ker n A hA
  let rho : PSL →* Equiv.Perm P :=
    QuotientGroup.lift (Subgroup.center SL) permHom hcenter_le_ker
  have hrho : Function.Injective rho := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    constructor
    · intro hx
      rcases QuotientGroup.mk'_surjective (Subgroup.center SL) x with ⟨A, rfl⟩
      rw [MonoidHom.mem_ker] at hx
      have hperm : permHom A = 1 := by
        change (rho.comp (QuotientGroup.mk' (Subgroup.center SL))) A = 1 at hx
        rw [show rho.comp (QuotientGroup.mk' (Subgroup.center SL)) = permHom by
          exact QuotientGroup.lift_comp_mk' (Subgroup.center SL) permHom hcenter_le_ker] at hx
        exact hx
      have hfix : ∀ z : P, A • z = z := by
        intro z
        have hz := congrArg (fun f : Equiv.Perm P => f z) hperm
        simpa [permHom] using hz
      have hcenter := huppert611_mem_center_of_projective_trivial n A hfix
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff A).mpr hcenter
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  have hrho_apply :
      ∀ (A : SL) (z : P),
        rho (QuotientGroup.mk' (Subgroup.center SL) A) z =
          (Matrix.GeneralLinearGroup.toLin
            (A : GL (Fin n) K)).toLinearEquiv • z := by
    intro A z
    change A • z = _
    rfl
  refine ⟨rho, hrho, hrho_apply, ?_⟩
  intro a b c d hab hcd
  let ba := huppert611_projectivePairBasis hn a b hab
  let bc := huppert611_projectivePairBasis hn c d hcd
  let std := Pi.basisFun K (Fin n)
  let A : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    ba.equiv std (Equiv.refl _)
  let B : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    std.equiv bc (Equiv.refl _)
  let correction : Kˣ := (LinearEquiv.det B * LinearEquiv.det A)⁻¹
  let w : Fin n → Kˣ := fun j =>
    if j = huppert611_pairIndex hn 0 then correction else 1
  let D : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    std.equiv (std.unitsSMul w) (Equiv.refl _)
  let gLin : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    A.trans (D.trans B)
  have hdetD : LinearEquiv.det D = correction := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det (D : (Fin n → K) →ₗ[K] (Fin n → K)) =
      (correction : K)
    rw [Module.Basis.det_basis, Module.Basis.det_unitsSMul_self]
    rw [Finset.prod_eq_single (huppert611_pairIndex hn 0)]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
  have hdetg : LinearEquiv.det gLin = 1 := by
    simp only [gLin, LinearEquiv.det_trans, hdetD]
    simp [correction, mul_comm]
  have hg (i : Fin 2) :
      gLin (![a.rep, b.rep] i) =
        (w (huppert611_pairIndex hn i) : K) • ![c.rep, d.rep] i := by
    rw [← huppert611_projectivePairBasis_pairIndex hn a b hab i]
    change B (D (A (ba (huppert611_pairIndex hn i)))) = _
    rw [show A (ba (huppert611_pairIndex hn i)) =
        std (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := ba) _ std (Equiv.refl _)]
    rw [show D (std (huppert611_pairIndex hn i)) =
        (std.unitsSMul w) (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := std) _ (std.unitsSMul w) (Equiv.refl _)]
    rw [Module.Basis.unitsSMul_apply]
    change B ((w (huppert611_pairIndex hn i) : K) •
      std (huppert611_pairIndex hn i)) = _
    rw [B.map_smul]
    rw [show B (std (huppert611_pairIndex hn i)) =
        bc (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := std) _ bc (Equiv.refl _)]
    rw [huppert611_projectivePairBasis_pairIndex hn c d hcd i]
  let M : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (gLin : (Fin n → K) →ₗ[K] (Fin n → K))
  have hMdet : M.det = 1 := by
    have h := congrArg Units.val hdetg
    simpa [M, LinearEquiv.coe_det] using h
  let S : SL := ⟨M, hMdet⟩
  have hSlin : Matrix.SpecialLinearGroup.toLin' S = gLin := by
    apply (LinearEquiv.toLinearMap_injective.eq_iff).mp
    change Matrix.toLin' (LinearMap.toMatrix'
      (gLin : (Fin n → K) →ₗ[K] (Fin n → K))) =
      (gLin : (Fin n → K) →ₗ[K] (Fin n → K))
    exact Matrix.toLin'_toMatrix' _
  let q : PSL := QuotientGroup.mk' (Subgroup.center SL) S
  refine ⟨q, ?_, ?_⟩
  · change S • a = c
    rw [← Projectivization.mk_rep a, ← Projectivization.mk_rep c,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(w (huppert611_pairIndex hn 0) : K), ?_⟩
    change (w (huppert611_pairIndex hn 0) : K) • c.rep =
      (Matrix.SpecialLinearGroup.toLin' S) a.rep
    rw [hSlin]
    simpa using (hg 0).symm
  · change S • b = d
    rw [← Projectivization.mk_rep b, ← Projectivization.mk_rep d,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(w (huppert611_pairIndex hn 1) : K), ?_⟩
    change (w (huppert611_pairIndex hn 1) : K) • d.rep =
      (Matrix.SpecialLinearGroup.toLin' S) b.rep
    rw [hSlin]
    simpa using (hg 1).symm


end External
end CFSG.BenderSuzuki
