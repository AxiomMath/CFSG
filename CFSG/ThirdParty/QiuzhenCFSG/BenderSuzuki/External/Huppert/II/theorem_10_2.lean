module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.SesquilinearForm.Star

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.10.2

Anisotropic vectors and orthogonal bases for nondegenerate Hermitian spaces.
-/

namespace CFSG.BenderSuzuki
namespace External

open MatrixGroups

universe u v

private theorem hermitian_exists_anisotropic
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [Nontrivial V] (sigma : K ≃+* K)
    (B : V →ₛₗ[(sigma : K →+* K)] V →ₗ[K] K)
    (hB : B.IsSymm) (hsep : B.SeparatingLeft)
    (htrace : ∃ a : K, a + sigma a ≠ 0) :
    ∃ x : V, B x x ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have hnotall : ¬ ∀ w : V, B u w = 0 := fun h => hu (hsep u h)
  push Not at hnotall
  obtain ⟨w, hw⟩ := hnotall
  let z := (B u w)⁻¹ • w
  have huz : B u z = 1 := by simp [z, hw]
  have hzu : B z u = 1 := by rw [← hB.eq, huz, map_one]
  rcases htrace with ⟨a, ha⟩
  by_contra hall
  push Not at hall
  have hu0 := hall u
  have hz0 := hall z
  have hsum := hall (u + a • z)
  simp [map_add, map_smul, map_smulₛₗ, hu0, hz0, huz, hzu] at hsum
  exact ha (by simpa [add_comm] using hsum)

private theorem hermitian_isCompl_span_singleton_orthogonal
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (sigma : K ≃+* K)
    (B : V →ₛₗ[(sigma : K →+* K)] V →ₗ[K] K)
    {x : V} (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B) := by
  refine
    { disjoint := disjoint_iff.2 <|
        LinearMap.span_singleton_inf_orthogonal_eq_bot B x hx
      codisjoint := codisjoint_iff.2 ?_ }
  rw [eq_top_iff]
  intro y _
  have hxx : B x x ≠ 0 := hx
  have hbase : B x (y + (-B x y / B x x) • x) = 0 := by
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hxx, add_neg_cancel]
  have hyorth :
      y + (-B x y / B x x) • x ∈
        (K ∙ x).orthogonalBilin B := by
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [map_smulₛₗ]
    change sigma c * B x (y + (-B x y / B x x) • x) = 0
    rw [hbase, mul_zero]
  have hxspan :
      (B x y / B x x) • x ∈ (K ∙ x) :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have hxspanSup :
      (B x y / B x x) • x ∈
        (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B :=
    (show (K ∙ x) ≤
      (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B from le_sup_left) hxspan
  have hyorthSup :
      y + (-B x y / B x x) • x ∈
        (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B :=
    (show (K ∙ x).orthogonalBilin B ≤
      (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B from le_sup_right) hyorth
  have hadd := Submodule.add_mem _ hxspanSup hyorthSup
  simpa [neg_div, add_comm, add_left_comm, add_assoc] using hadd

private theorem hermitian_orthogonal_restrict_separatingLeft
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (sigma : K ≃+* K)
    (B : V →ₛₗ[(sigma : K →+* K)] V →ₗ[K] K)
    (hB : B.IsSymm) (hsep : B.SeparatingLeft)
    {x : V} (hx : B x x ≠ 0) :
    (B.domRestrict₁₂
      ((K ∙ x).orthogonalBilin B)
      ((K ∙ x).orthogonalBilin B)).SeparatingLeft := by
  let N := (K ∙ x).orthogonalBilin B
  intro z hz
  apply Subtype.ext
  apply hsep z.1
  intro y
  have hxx : B x x ≠ 0 := hx
  have hybase : B x (y + (-B x y / B x x) • x) = 0 := by
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hxx, add_neg_cancel]
  have hyN : y + (-B x y / B x x) • x ∈ N := by
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [map_smulₛₗ]
    change sigma c * B x (y + (-B x y / B x x) • x) = 0
    rw [hybase, mul_zero]
  let y0 : N := ⟨y + (-B x y / B x x) • x, hyN⟩
  have hxz : B x z.1 = 0 :=
    z.2 x (Submodule.mem_span_singleton_self x)
  have hzx : B z.1 x = 0 := hB.isRefl.eq_zero hxz
  have hzy0 : B z.1 y0.1 = 0 := by
    simpa [N, y0, LinearMap.domRestrict₁₂_apply] using hz y0
  have hydecomp : y = (B x y / B x x) • x + y0.1 := by
    simp [y0, neg_div, add_left_comm]
  rw [hydecomp, map_add, map_smul, smul_eq_mul, hzx, hzy0, mul_zero, zero_add]

private theorem hermitian_exists_orthogonal_basis
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (sigma : K ≃+* K)
    (B : V →ₛₗ[(sigma : K →+* K)] V →ₗ[K] K)
    (hB : B.IsSymm) (hsep : B.SeparatingLeft)
    (htrace : ∃ a : K, a + sigma a ≠ 0)
    (d : ℕ) (hd : Module.finrank K V = d) :
    ∃ b : Module.Basis (Fin d) K V, B.IsOrthoᵢ b := by
  induction d generalizing V with
  | zero =>
      exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
      letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hd
      obtain ⟨x, hx⟩ := hermitian_exists_anisotropic sigma B hB hsep htrace
      let N := (K ∙ x).orthogonalBilin B
      have hcompl : IsCompl (K ∙ x) N :=
        hermitian_isCompl_span_singleton_orthogonal sigma B hx
      rw [← Submodule.finrank_add_eq_of_isCompl hcompl.symm,
        finrank_span_singleton (ne_zero_of_map hx)] at hd
      let B' := B.domRestrict₁₂ N N
      have hB' : B'.IsSymm := hB.domRestrict N
      have hsep' : B'.SeparatingLeft :=
        hermitian_orthogonal_restrict_separatingLeft sigma B hB hsep hx
      obtain ⟨b', hb'⟩ := ih B' hB' hsep' (Nat.succ.inj hd)
      let b :=
        Module.Basis.mkFinCons x b'
          (by
            rintro c y hy hc
            rw [add_eq_zero_iff_neg_eq] at hc
            rw [← hc, Submodule.neg_mem_iff] at hy
            have hdisj := hcompl.disjoint
            rw [Submodule.disjoint_def] at hdisj
            have hzero := hdisj (c • x)
              (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
            exact (smul_eq_zero.1 hzero).resolve_right
              (fun h => hx <| h.symm ▸ map_zero _))
          (by
            intro y
            refine ⟨-B x y / B x x, ?_⟩
            intro z hz
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
            have hxx : B x x ≠ 0 := hx
            rw [map_smulₛₗ]
            change sigma c * B x (y + (-B x y / B x x) • x) = 0
            rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hxx,
              add_neg_cancel, mul_zero])
      refine ⟨b, ?_⟩
      rw [Module.Basis.coe_mkFinCons]
      intro j i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
        simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      · exact (hij rfl).elim
      · rw [← hB.eq]
        have hxo : B x (b' j) = 0 :=
          (b' j).prop _ (Submodule.mem_span_singleton_self x)
        rw [hxo, map_zero]
      · exact (b' i).prop _ (Submodule.mem_span_singleton_self x)
      · exact hb' (ne_of_apply_ne _ hij)


/-- Huppert II.10.2(b): a nondegenerate Hermitian space has an orthogonal
basis with nonzero diagonal Gram entries. -/
public theorem huppert_II_10_2_b_orthogonal_basis
    {K : Type u} [Field K] (n : ℕ) (J : HermitianForm n K)
    (htrace_nonzero : ∃ a : K, a + J.conj a ≠ 0) :
    ∃ P : GL (Fin n) K,
      (∀ i j, i ≠ j →
        (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
          (P : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i,
        (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
          (P : Matrix (Fin n) (Fin n) K)) i i ≠ 0 := by
  have horthogonal_basis :
      ∃ P : GL (Fin n) K,
        (∀ i j, i ≠ j →
          (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
            (P : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
        ∀ i,
          (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
            (P : Matrix (Fin n) (Fin n) K)) i i ≠ 0 := by
    classical
    letI : Star K := ⟨J.conj⟩
    letI : InvolutiveStar K := ⟨J.conj_involutive⟩
    letI : StarMul K := ⟨fun r s => by
      change J.conj (r * s) = J.conj s * J.conj r
      rw [map_mul, mul_comm]⟩
    letI : StarRing K := ⟨fun r s => by
      change J.conj (r + s) = J.conj r + J.conj s
      rw [map_add]⟩
    let e := Pi.basisFun K (Fin n)
    let B := Matrix.toLinearMapₛₗ₂ (J.conj : K →+* K) e e J.form
    have hB : B.IsSymm := by
      apply (LinearMap.isSymm_iff_basis e).2
      intro i j
      change J.conj (B (e i) (e j)) = B (e j) (e i)
      rw [Matrix.toLinearMapₛₗ₂_apply_basis,
        Matrix.toLinearMapₛₗ₂_apply_basis]
      exact J.form_hermitian j i
    have hsep : B.SeparatingLeft := by
      intro x hx
      have hmul : J.form.mulVec x = 0 := by
        ext i
        have hBix : B (e i) x = 0 := by
          rw [← hB.eq]
          simp [hx]
        rw [apply_eq_dotProduct_toMatrix₂_mulVec e e B (e i) x] at hBix
        change J.form.mulVec x i = 0
        have hrepr : ((Pi.basisFun K (Fin n)).repr x : Fin n → K) = x := by
          ext j
          simp
        have hrepr_i :
            ((Pi.basisFun K (Fin n)).repr (e i) : Fin n → K) = Pi.single i 1 := by
          ext j
          simp [e]
        rw [hrepr, hrepr_i] at hBix
        have hconj_single :
            ((↑J.conj : K →+* K) ∘ (Pi.single i 1 : Fin n → K)) =
              Pi.single i (J.conj 1) := by
          ext j
          by_cases h : j = i <;> simp [h]
        rw [hconj_single, single_dotProduct] at hBix
        simpa [B, Matrix.toLinearMapₛₗ₂_apply] using hBix
      by_contra hx0
      apply J.form_nondegenerate
      exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hmul⟩
    obtain ⟨b, hb⟩ := hermitian_exists_orthogonal_basis
      J.conj B hB hsep htrace_nonzero n (Module.finrank_fin_fun K)
    let Pmat := e.toMatrix b
    have hPunit : IsUnit Pmat.det := by
      rw [← e.det_apply]
      exact e.isUnit_det b
    have hPdet : Pmat.det ≠ 0 := hPunit.ne_zero
    let P : GL (Fin n) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Pmat hPdet
    refine ⟨P, ?_, ?_⟩
    · intro i j hij
      have hgram :
          (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
              (P : Matrix (Fin n) (Fin n) K)) i j = B (b i) (b j) := by
        change (J.conjTranspose Pmat * J.form * Pmat) i j = B (b i) (b j)
        simp only [HermitianForm.conjTranspose, Matrix.mul_apply, Pmat,
          Module.Basis.toMatrix_apply, B, Matrix.toLinearMapₛₗ₂_apply,
          smul_eq_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ac_rfl
      rw [hgram]
      exact hb hij
    · intro i
      have hgram :
          (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
              (P : Matrix (Fin n) (Fin n) K)) i i = B (b i) (b i) := by
        change (J.conjTranspose Pmat * J.form * Pmat) i i = B (b i) (b i)
        simp only [HermitianForm.conjTranspose, Matrix.mul_apply, Pmat,
          Module.Basis.toMatrix_apply, B, Matrix.toLinearMapₛₗ₂_apply,
          smul_eq_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ac_rfl
      rw [hgram]
      exact hb.not_isOrtho_basis_self_of_separatingLeft hsep i
  exact horthogonal_basis

end External
end CFSG.BenderSuzuki
