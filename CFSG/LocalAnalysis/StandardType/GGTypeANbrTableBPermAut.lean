module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import TauCeti.GroupTheory.Perm.FinThree.Basic
public import CFSG.Mathlib.GroupTheory.Perm.S3Kernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

namespace TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K]

theorem perm_eq_one_of_pairVec_of_coprime (hd : 3 ≤ d) (hcp : Nat.Coprime d p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : Equiv.Perm (Fin d)}
    (h : ∀ k l : Fin d, k ≠ l → ∃ c : K,
      ∀ m, ggPairVec k l ζ (σ m) = c * ggPairVec k l ζ m) : σ = 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  apply Equiv.ext
  intro k
  change σ k = k
  obtain ⟨l, hlk⟩ := exists_ne_of_two hd k k
  obtain ⟨c, hc⟩ := h k l (Ne.symm hlk.1)
  have hprod : c ^ d = 1 := by
    have he := congrArg (fun v : Fin d → K => ∏ m, v m) (funext hc)
    rw [Equiv.prod_comp σ, Finset.prod_mul_distrib,
      prod_ggPairVec ζ hζ0, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_one] at he
    exact he.symm
  have hpow : c ^ p = 1 := by
    have he := congrArg (fun z : K => z ^ p) (hc k)
    rw [TypeA.pow_ggPairVec hζ.pow_eq_one, mul_pow,
      TypeA.pow_ggPairVec hζ.pow_eq_one, mul_one] at he
    exact he.symm
  have hc1 : c = 1 := by
    have ho : orderOf c ∣ Nat.gcd d p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hprod) (orderOf_dvd_of_pow_eq_one hpow)
    rw [hcp.gcd_eq_one] at ho
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one ho)
  have he := hc k
  rw [hc1, one_mul] at he
  have hvk : ggPairVec k l ζ k = ζ := by
    simp [ggPairVec_apply, Ne.symm hlk.1]
  rw [hvk] at he
  by_cases hsk : σ k = k
  · exact hsk
  · by_cases hsl : σ k = l
    · simp [ggPairVec_apply, hsk, hsl, hlk.1] at he
      exact (hζinv he.symm).elim
    · simp [ggPairVec_apply, hsk, hsl] at he
      exact (hζ1 he.symm).elim

private theorem exists_ne_of_three (hd : 4 ≤ d) (a b c : Fin d) :
    ∃ x : Fin d, x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]
        exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2.1, hi.2.2⟩

theorem perm_eq_one_of_pairVec (hd : 4 ≤ d) {ζ : K} (hζ1 : ζ ≠ 1) (hζinv : ζ ≠ ζ⁻¹)
    {σ : Equiv.Perm (Fin d)}
    (h : ∀ k l : Fin d, k ≠ l → ∃ c : K, ∀ m, ggPairVec k l ζ (σ m) = c * ggPairVec k l ζ m) :
    σ = 1 := by
  by_contra hσ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hσ (Equiv.ext fun i => by rw [hcon i, Equiv.Perm.one_apply])
  set j : Fin d := σ i with hj
  have hji : j ≠ i := by rw [hj]; exact hi
  obtain ⟨m₀, hm₀i, hm₀j⟩ := exists_ne_of_two (by omega : 3 ≤ d) i j
  obtain ⟨x, hxi, hxj, hxm₀⟩ := exists_ne_of_three hd i j m₀
  set v : Fin d → K := ggPairVec j m₀ ζ with hv
  obtain ⟨c, hc⟩ := h j m₀ (Ne.symm hm₀j)
  have hvj : v j = ζ := by
    rw [hv, ggPairVec_apply, ite_eq_left rfl, ite_eq_right (Ne.symm hm₀j), mul_one]
  have hvi : v i = 1 := by
    rw [hv, ggPairVec_apply, ite_eq_right (Ne.symm hji), ite_eq_right (Ne.symm hm₀i), mul_one]
  have hvx : v x = 1 := by
    rw [hv, ggPairVec_apply, ite_eq_right hxj, ite_eq_right hxm₀, mul_one]
  have hci : v (σ i) = c * v i := hc i
  have hcζ : c = ζ := by
    rw [hvi, mul_one, ← hj, hvj] at hci
    exact hci.symm
  have hcx : v (σ x) = c * v x := hc x
  have hxζ : v (σ x) = ζ := by
    rw [hvx, mul_one, hcζ] at hcx
    exact hcx
  have hv_eq : ∀ y : Fin d, v y = ζ → y = j := by
    intro y hy
    by_cases hyj : y = j
    · exact hyj
    by_cases hym : y = m₀
    · have hvm : v m₀ = ζ⁻¹ := by
        rw [hv, ggPairVec_apply, ite_eq_right hm₀j, ite_eq_left rfl, one_mul]
      rw [hym, hvm] at hy
      exact absurd hy.symm hζinv
    · have hv1 : v y = 1 := by
        rw [hv, ggPairVec_apply, ite_eq_right hyj, ite_eq_right hym, mul_one]
      rw [hv1] at hy
      exact absurd hy.symm hζ1
  have hσxj : σ x = j := hv_eq (σ x) hxζ
  have hxi_eq : x = i := σ.injective (hσxj.trans hj)
  exact hxi hxi_eq

variable [CharP K 2]

private theorem permConj_conj_mem_of_selfCent {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (σ : Equiv.Perm (Fin d))
    {a : MulAut L'} (ha : a ∈ A) :
    NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹ ∈ A := by
  obtain ⟨t, hat⟩ := hdiag a ha
  have hb : ActsDiag φ' (NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹)
      (t ∘ σ.symm) :=
    hat.conj_perm σ.symm
  have hprod : ∏ k, t (σ.symm k) * (t k)⁻¹ = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ.symm t]
    exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
  let D : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal (fun k => t (σ.symm k) * (t k)⁻¹), by rw [det_diagonal, hprod]⟩
  have hDm : (D : Matrix (Fin d) (Fin d) K) = diagonal (fun k => t (σ.symm k) * (t k)⁻¹) := rfl
  have hDA : MulAut.conj (φ' D) ∈ A :=
    conj_mem_of_selfCent hsc hdiag hDm
      (fun i => hat.ratio_pow hφker (hAp a ha) (σ.symm i) i)
  have hconjD : ActsDiag φ' (MulAut.conj (φ' D)) (fun k => t (σ.symm k) * (t k)⁻¹) :=
    actsDiag_conj hDm
  have hmul : ActsDiag φ' (MulAut.conj (φ' D) * a) (t ∘ σ.symm) := by
    have h := hconjD.mul hat
    have hfun : (fun k => (t (σ.symm k) * (t k)⁻¹) * t k) = t ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, mul_assoc, inv_mul_cancel₀ (hat.ne_zero k), mul_one]
    rw [hfun] at h
    exact h
  have heq : NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹ =
      MulAut.conj (φ' D) * a := hb.unique hφ's hmul
  rw [heq]
  exact A.mul_mem hDA ha

theorem permConj_mem_normalizer_of_selfCent {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (σ : Equiv.Perm (Fin d)) :
    NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact permConj_conj_mem_of_selfCent hφ's hφker hAp hsc hdiag σ hh
  · intro hh
    have h2 := permConj_conj_mem_of_selfCent hφ's hφker hAp hsc hdiag (σ⁻¹) hh
    have hinv : NbrInnerWeylA.permConj φ' σ⁻¹ = (NbrInnerWeylA.permConj φ' σ)⁻¹ :=
      map_inv (NbrInnerWeylA.permConj φ') σ
    rw [hinv] at h2
    have heq : (NbrInnerWeylA.permConj φ' σ)⁻¹ * (NbrInnerWeylA.permConj φ' σ * h *
        (NbrInnerWeylA.permConj φ' σ)⁻¹) * ((NbrInnerWeylA.permConj φ' σ)⁻¹)⁻¹ = h := by
      group
    rwa [heq] at h2

@[expose] noncomputable def permAut {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L')
    (A : Subgroup (MulAut L'))
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    Equiv.Perm (Fin d) →* MulAut ↥A where
  toFun σ := ggConjAut A (hN σ)
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, map_mul]
    group

theorem permAut_apply {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L')
    (A : Subgroup (MulAut L'))
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (σ : Equiv.Perm (Fin d)) : permAut φ' A hN σ = ggConjAut A (hN σ) :=
  rfl

theorem permAut_mem_ggAutomizer {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (σ : Equiv.Perm (Fin d)) :
    permAut φ' A hN σ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  rw [permAut_apply]
  exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
    (g := NbrInnerWeylA.permConj φ' σ)
    (MonoidHom.mem_range.mpr ⟨φ' (permSL σ⁻¹), rfl⟩) (hN σ)

theorem permAut_injective [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) {L' : Type} [Group L'] [Finite L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    Function.Injective (permAut φ' A hN) := by
  refine (injective_iff_map_eq_one (permAut φ' A hN)).mpr fun σ hσ => ?_
  have hcomm : ∀ b ∈ A, NbrInnerWeylA.permConj φ' σ * b * (NbrInnerWeylA.permConj φ' σ)⁻¹ = b := by
    intro b hb
    have h := congrArg (fun f : MulAut ↥A => ((f ⟨b, hb⟩ : ↥A) : MulAut L')) hσ
    rw [permAut_apply, ggConjAut_apply, MulAut.one_apply] at h
    simpa using h
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  refine inv_eq_one.mp (perm_eq_one_of_pairVec hd hζ1 hζinv (σ := σ.symm) fun k l _ => ?_)
  obtain ⟨m₀, hm₀k, hm₀l⟩ := exists_ne_of_two (by omega : 3 ≤ d) k l
  set v : Fin d → K := ggPairVec k l ζ with hv
  have hvm₀ : v m₀ = 1 := by
    rw [hv, ggPairVec_apply, ite_eq_right hm₀k, ite_eq_right hm₀l, mul_one]
  have hv_ne : ∀ y, v y ≠ 0 := by
    intro y
    rw [hv, ggPairVec_apply]
    split_ifs with h1 h2
    · exact mul_ne_zero hζ0 (inv_ne_zero hζ0)
    · simpa using hζ0
    · simpa using inv_ne_zero hζ0
    · simpa using one_ne_zero
  let D : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal v, by rw [det_diagonal, hv, prod_ggPairVec ζ hζ0]⟩
  have hDm : (D : Matrix (Fin d) (Fin d) K) = diagonal v := rfl
  have hDA : MulAut.conj (φ' D) ∈ A :=
    conj_mem_of_selfCent hsc hdiag hDm (fun i => by rw [hv]; exact pow_ggPairVec hζ.pow_eq_one i)
  have hact : ActsDiag φ' (MulAut.conj (φ' D)) v := actsDiag_conj hDm
  have hperm : MulAut.conj (φ' (permSL σ.symm)) = NbrInnerWeylA.permConj φ' σ := rfl
  have hconj : MulAut.conj (φ' (permSL σ.symm)) * MulAut.conj (φ' D) *
      (MulAut.conj (φ' (permSL σ.symm)))⁻¹ = MulAut.conj (φ' D) := by
    rw [hperm]
    exact hcomm (MulAut.conj (φ' D)) hDA
  have hact' : ActsDiag φ' (MulAut.conj (φ' D)) (v ∘ σ.symm) := by
    have h := hact.conj_perm σ.symm
    rw [hconj] at h
    exact h
  refine ⟨v (σ.symm m₀) * (v m₀)⁻¹, fun m => ?_⟩
  by_cases hm : m = m₀
  · rw [hm]
    simp [hvm₀]
  · have hratio := hact'.ratio hφker hact hm
    rw [Function.comp_apply, Function.comp_apply, hvm₀, inv_one, mul_one] at hratio
    rw [hvm₀, inv_one, mul_one]
    calc v (σ.symm m) = v (σ.symm m) * (v (σ.symm m₀))⁻¹ * v (σ.symm m₀) := by
          rw [mul_assoc, inv_mul_cancel₀ (hv_ne (σ.symm m₀)), mul_one]
      _ = v m * v (σ.symm m₀) := by rw [hratio]
      _ = v (σ.symm m₀) * v m := by rw [mul_comm]

private theorem exists_smul_of_ratio_eq_fin3 {K : Type} [Field K] {t u : Fin 3 → K}
    (ht : ∀ i, t i ≠ 0) (hu : ∀ i, u i ≠ 0)
    (h : ∀ i j, i ≠ j → t i * (t j)⁻¹ = u i * (u j)⁻¹) :
    ∃ lam : K, ∀ i, u i = lam * t i := by
  refine ⟨u 0 * (t 0)⁻¹, fun i => ?_⟩
  by_cases hi : i = 0
  · subst i
    field_simp [ht 0]
  · have hh := h i 0 hi
    have h1 : t i = u i * (u 0)⁻¹ * t 0 := by
      calc t i = t i * (t 0)⁻¹ * t 0 := by field_simp [ht 0]
        _ = (u i * (u 0)⁻¹) * t 0 := by rw [hh]
        _ = u i * (u 0)⁻¹ * t 0 := rfl
    have hmul : u i * t 0 = t i * u 0 := by
      rw [h1]
      field_simp [hu 0]
    calc u i = (u i * t 0) * (t 0)⁻¹ := by field_simp [ht 0]
      _ = (t i * u 0) * (t 0)⁻¹ := by rw [hmul]
      _ = (u 0 * (t 0)⁻¹) * t i := by ring

private theorem exists_smul_of_actsDiag_same {K : Type} [Field K] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {a : MulAut L'} {t u : Fin 3 → K}
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ActsDiag φ' a t) (hu : ActsDiag φ' a u) :
    ∃ lam : K, ∀ i, u i = lam * t i := by
  refine exists_smul_of_ratio_eq_fin3 (fun i => ht.ne_zero i) (fun i => hu.ne_zero i) ?_
  intro i j hij
  exact ht.ratio hφker hu hij

private theorem conj_fixes_of_permAut_finRotate_eq_one
    {K : Type} [Field K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hfix : permAut φ' A hN (finRotate 3) = 1) (a : ↥A) :
    MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)) * (a : MulAut L') *
      (MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)))⁻¹ = (a : MulAut L') := by
  have h := congrArg (fun f : MulAut ↥A => ((f a : ↥A) : MulAut L')) hfix
  simpa [permAut_apply, ggConjAut_apply, MulAut.one_apply, NbrInnerWeylA.permConj,
    Equiv.Perm.inv_def] using h

private theorem exists_lam_of_conj_fixes
    {K : Type} [Field K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    {t : ↥A → Fin 3 → K}
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ∀ a : ↥A, ActsDiag φ' (a : MulAut L') (t a)) (a : ↥A)
    (hfixa : MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)) * (a : MulAut L') *
      (MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)))⁻¹ = (a : MulAut L')) :
    ∃ lam : K, ∀ i, t a ((finRotate 3).symm i) = lam * t a i := by
  have hconj : ActsDiag φ' (MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)) *
      (a : MulAut L') * (MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)))⁻¹)
      (t a ∘ (finRotate 3).symm) := (ht a).conj_perm (finRotate 3).symm
  rw [hfixa] at hconj
  obtain ⟨lam, hlam⟩ := exists_smul_of_actsDiag_same hφker (ht a) hconj
  exact ⟨lam, fun i => by simpa [Function.comp_apply] using hlam i⟩

private theorem finRotate_symm_zero : (finRotate 3).symm 0 = 2 := by decide +kernel
private theorem finRotate_symm_one : (finRotate 3).symm 1 = 0 := by decide +kernel
private theorem finRotate_symm_two : (finRotate 3).symm 2 = 1 := by decide +kernel

private theorem lam_pow_three_of_rel {K : Type} [Field K] {t : Fin 3 → K} {lam : K}
    (ht0 : t 0 ≠ 0)
    (h : ∀ i, t ((finRotate 3).symm i) = lam * t i) :
    lam ^ 3 = 1 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [finRotate_symm_zero, finRotate_symm_one, finRotate_symm_two] at h0 h1 h2
  have hchain : t 0 = lam ^ 3 * t 0 := by
    calc t 0 = lam * t 1 := h1
      _ = lam * (lam * t 2) := by rw [h2]
      _ = lam ^ 2 * t 2 := by ring
      _ = lam ^ 2 * (lam * t 0) := by rw [h0]
      _ = lam ^ 3 * t 0 := by ring
  exact mul_right_cancel₀ ht0 (by simpa using hchain.symm)

private theorem lam_injective
    {K : Type} [Field K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    {t : ↥A → Fin 3 → K}
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ∀ a : ↥A, ActsDiag φ' (a : MulAut L') (t a))
    (lam : ↥A → K)
    (hlam : ∀ (a : ↥A) (i : Fin 3),
      t a ((finRotate 3).symm i) = lam a * t a i)
    (hlam3 : ∀ a : ↥A, lam a ^ 3 = 1) :
    Function.Injective (fun a : ↥A =>
      rootsOfUnity.mkOfPowEq (lam a) (hlam3 a)) := by
  intro a b hab
  have hlam0 : ∀ a : ↥A, lam a ≠ 0 := by
    intro a hzero
    have h := hlam3 a
    rw [hzero, zero_pow (by norm_num : 3 ≠ 0)] at h
    exact zero_ne_one h
  have hlam_eq : lam a = lam b := by
    have h := congrArg (fun z : ↥(rootsOfUnity 3 K) => ((z : Kˣ) : K)) hab
    simpa [rootsOfUnity.mkOfPowEq] using h
  let u : Fin 3 → K := fun i => t a i * (t b i)⁻¹
  have hpoint : ∀ i, u ((finRotate 3).symm i) = u i := by
    intro i
    dsimp [u]
    rw [hlam a i, hlam b i, hlam_eq]
    field_simp [hlam0 a, hlam0 b, (ht a).ne_zero i, (ht b).ne_zero i]
  have hu20 : u 2 = u 0 := by
    have h := hpoint 0
    rw [finRotate_symm_zero] at h
    exact h
  have hu01 : u 0 = u 1 := by
    have h := hpoint 1
    rw [finRotate_symm_one] at h
    exact h
  have hu12 : u 1 = u 2 := by
    have h := hpoint 2
    rw [finRotate_symm_two] at h
    exact h
  have hconst : ∀ i j, u i = u j := by
    have h02 : u 0 = u 2 := hu01.trans hu12
    have h10 : u 1 = u 0 := hu01.symm
    have h20 : u 2 = u 0 := hu20
    have h21 : u 2 = u 1 := hu12.symm
    intro i j
    fin_cases i <;> fin_cases j <;> first | rfl | assumption
  have hdiagprod : ActsDiag φ' ((a : MulAut L') * (b : MulAut L')⁻¹)
      (fun i => t a i * (t b i)⁻¹) := (ht a).mul ((ht b).inv)
  have hone : ((a : MulAut L') * (b : MulAut L')⁻¹) = 1 :=
    ActsDiag.eq_one (d := 3) (by norm_num) hφ's hdiagprod (by simpa [u] using hconst)
  exact Subtype.ext (mul_inv_eq_one.mp hone)

theorem card_le_three_of_permAut_finRotate_eq_one
    {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ∀ a : ↥A, ∃ t : Fin 3 → K, ActsDiag φ' (a : MulAut L') t)
    (hfix : permAut φ' A hN (finRotate 3) = 1) :
    Nat.card ↥A ≤ 3 := by
  classical
  let t : ↥A → Fin 3 → K := fun a => Classical.choose (ht a)
  have ht' : ∀ a : ↥A, ActsDiag φ' (a : MulAut L') (t a) := fun a =>
    Classical.choose_spec (ht a)
  have hfixa : ∀ a : ↥A, MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)) *
      (a : MulAut L') * (MulAut.conj (φ' (TypeA.permSL (finRotate 3).symm)))⁻¹ =
      (a : MulAut L') := fun a =>
    conj_fixes_of_permAut_finRotate_eq_one hN hfix a
  have hex : ∀ a : ↥A, ∃ lam : K, ∀ i, t a ((finRotate 3).symm i) = lam * t a i :=
    fun a => exists_lam_of_conj_fixes hφker ht' a (hfixa a)
  let lam : ↥A → K := fun a => Classical.choose (hex a)
  have hlam : ∀ a : ↥A, ∀ i, t a ((finRotate 3).symm i) = lam a * t a i := fun a =>
    Classical.choose_spec (hex a)
  have hlam3 : ∀ a : ↥A, lam a ^ 3 = 1 := fun a =>
    lam_pow_three_of_rel ((ht' a).ne_zero 0) (hlam a)
  have hinj : Function.Injective (fun a : ↥A =>
      rootsOfUnity.mkOfPowEq (lam a) (hlam3 a)) :=
    lam_injective hφ's hφker ht' lam hlam hlam3
  have hle : Nat.card ↥A ≤ Nat.card ↥(rootsOfUnity 3 K) :=
    Nat.card_le_card_of_injective
      (fun a : ↥A => rootsOfUnity.mkOfPowEq (lam a) (hlam3 a)) hinj
  have h3 : Nat.card ↥(rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
  omega

theorem finRotate_not_mem_ker_of_nine_le_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ∀ a : ↥A, ∃ t : Fin 3 → K, ActsDiag φ' (a : MulAut L') t)
    (h9 : 9 ≤ Nat.card ↥A) :
    (finRotate 3 : Equiv.Perm (Fin 3)) ∉ (permAut φ' A hN).ker := by
  intro hc
  have hfix : permAut φ' A hN (finRotate 3) = 1 := hc
  have hle := card_le_three_of_permAut_finRotate_eq_one hN hφ's hφker ht hfix
  omega

theorem permAut_injective_of_nine_le_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin 3) K →* L'} {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars 3 K)
    (ht : ∀ a : ↥A, ∃ t : Fin 3 → K, ActsDiag φ' (a : MulAut L') t)
    (h9 : 9 ≤ Nat.card ↥A) :
    Function.Injective (permAut φ' A hN) :=
  CFSG.injective_of_finRotate_not_mem_ker (permAut φ' A hN)
    (finRotate_not_mem_ker_of_nine_le_card hN hφ's hφker ht h9)

end TypeANbrDvd

end CFSG.StandardType
