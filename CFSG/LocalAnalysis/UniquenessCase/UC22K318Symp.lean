module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Red
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.RankThree.PartTwo CFSG.OddSolvableUnitary
open CFSG.RankThree.SubgroupLists (spForm spGram)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (pRank_le_of_le)
open scoped commutatorElement Matrix

variable {L : Type} [Group L] [Finite L]

@[expose] def SympSection (X : Subgroup L) (q : ℕ) [Fact q.Prime]
    (ψ : L →* GL (Fin 2 ⊕ Fin 2) (ZMod q)) : Prop :=
  ∃ D : Subgroup L, D.Normal ∧ D ≤ X ∧ (∀ x ∈ D, x ^ q = 1) ∧ Nat.card D = q ^ 5 ∧
    ∃ π : D →* Multiplicative (Fin 2 ⊕ Fin 2 → ZMod q), Function.Surjective π ∧
      (∀ x : D, π x = 1 → ∀ g : L, g * x = x * g) ∧
      (∀ (g : L) (x y : D), (y : L) = g * x * g⁻¹ →
        (ψ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ Multiplicative.toAdd (π x) =
          Multiplicative.toAdd (π y)) ∧
      ∀ x y : D, x * y = y * x ↔
        spForm 2 (ZMod q) (Multiplicative.toAdd (π x)) (Multiplicative.toAdd (π y)) = 0

theorem card_eq_of_card_frattini_four {q : ℕ} [Fact q.Prime] {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup q D) (hexp : ∀ x : D, x ^ q = 1) (hclass : commutator D ≤ center D)
    (hrank : CFSG.pRank q D ≤ 3) (hk : Nat.card (D ⧸ frattini D) = q ^ 4) :
    Nat.card D = q ^ 5 ∧ Nat.card (center D) = q ∧ center D = commutator D ∧
      frattini D = commutator D ∧ CFSG.pRank q D = 3 := by
  have hΦ : frattini D = commutator D := frattini_eq_commutator hD hexp
  rw [hΦ] at hk
  have h4 := (quotient_commutator_rank Fact.out hexp hk).2
  obtain ⟨h1, h2, -⟩ := class_two_small_rank_order_bounds hD hexp hclass
  have h3 : CFSG.pRank q D = 3 := by
    by_contra hne
    have := h1 (by omega)
    omega
  obtain ⟨i, hi, -⟩ := h2 h3
  fin_cases i
  · have hi' : IsElementaryAbelian q D ∧ Nat.card D = q ^ 3 ∧
        CFSG.pRank q (D ⧸ commutator D) = 3 := hi
    omega
  · have hi' : Nat.card D = q ^ 5 ∧ Nat.card (center D) = q ∧ commutator D = center D ∧
        CFSG.pRank q (D ⧸ commutator D) = 4 := hi
    exact ⟨hi'.1, hi'.2.1, hi'.2.2.1.symm, hΦ, h3⟩
  · have hi' : Nat.card D = q ^ 4 ∧ Nat.card (center D) = q ^ 2 ∧ Nat.card (commutator D) = q ∧
        CFSG.pRank q (D ⧸ commutator D) = 3 := hi
    omega

theorem commute_of_mem_center [Group.IsPerfect L] {Q : Subgroup L} [Q.Normal] {D : Subgroup Q}
    [D.Characteristic] [IsCyclic (center D)] (g : L) {z : D} (hz : z ∈ center D) :
    g * ((z : Q) : L) = ((z : Q) : L) * g := by
  let act : L →* MulAut (center D) :=
    (MulAut.characteristic (center D)).comp ((MulAut.characteristic D).comp MulAut.conjNormal)
  have hg : act g = 1 := by
    have h := Abelianization.commutator_subset_ker
      ((IsCyclic.mulAutMulEquiv (center D)).toMonoidHom.comp act)
    rw [Group.IsPerfect.commutator_eq_top] at h
    have h2 : IsCyclic.mulAutMulEquiv (center D) (act g) = 1 := MonoidHom.mem_ker.1 (h (mem_top g))
    exact (MulEquiv.map_eq_one_iff _).1 h2
  have h1 : g * ((z : Q) : L) * g⁻¹ = ((z : Q) : L) :=
    congrArg (fun a : MulAut (center D) => ((((a ⟨z, hz⟩ : center D) : D) : Q) : L)) hg
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem exists_sympSection [Group.IsPerfect L] {X : Subgroup L} {q : ℕ} [Fact q.Prime]
    (hrank : CFSG.Open.pRank q X ≤ 3) {φ : L →* GL (Fin 4) (ZMod q)}
    (hcs : CriticalSection X q 4 φ) :
    ∃ τ : GL (Fin 4) (ZMod q) ≃* GL (Fin 2 ⊕ Fin 2) (ZMod q),
      ∃ c : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 2 ⊕ Fin 2 → ZMod q),
        (∀ (M : GL (Fin 4) (ZMod q)) (v : Fin 4 → ZMod q),
          (τ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ c v =
            c ((M : Matrix (Fin 4) (Fin 4) (ZMod q)) *ᵥ v)) ∧
        (∀ g : L, τ (φ g) ∈ CFSG.Open.StatedSp 2 (ZMod q)) ∧
        CFSG.Open.pRank q X = 3 ∧ SympSection X q (τ.toMonoidHom.comp φ) := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨Q, hQn, hQX, hQp, -, D, hDc, -, hDexp, -, -, -, hclass, hDrank, hcard, e, he⟩ := hcs
  haveI := hQn
  haveI := hDc
  have hDq : IsPGroup q D := hQp.to_subgroup D
  have hexp : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDexp x x.2)
  obtain ⟨hD5, hZq, hZ, hΦ, hD3⟩ := card_eq_of_card_frattini_four hDq hexp hclass hDrank hcard
  have hX3 : CFSG.Open.pRank q X = 3 :=
    le_antisymm hrank (hD3 ▸ pRank_le_of_le hq.one_lt hQX D)
  haveI : IsCyclic (center D) := isCyclic_of_prime_card hZq
  obtain ⟨ε⟩ := nonempty_center_mulEquiv hZq
  have : Module (ZMod q) (Additive (Abelianization D)) :=
    AddCommGroup.zmodModule (nsmul_abelianization_eq_zero hexp)
  obtain ⟨B, hBa, hBn, hB⟩ := exists_commForm hZ ε
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod q) (Additive (Abelianization D)) := Module.Finite.of_finite
  obtain ⟨m, bs, hbs⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (K := ZMod q) hBa hBn
  have hab : Nat.card (Abelianization D) = q ^ 4 := by
    change Nat.card (D ⧸ commutator D) = q ^ 4
    rw [← hΦ]
    exact hcard
  have hm : m = 2 := by
    have h1 : Nat.card (Additive (Abelianization D)) = q ^ (2 * m) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod,
        Module.finrank_eq_card_basis bs, Fintype.card_sum, Fintype.card_fin, two_mul]
    change Nat.card (Abelianization D) = _ at h1
    rw [hab] at h1
    have := Nat.pow_right_injective hq.two_le h1
    omega
  subst hm
  have hval : ∀ x y : D, ⁅x, y⁆ = 1 ↔ B (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = 0 := by
    intro x y
    rw [hB, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε,
      ε.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e₁ : Abelianization D ≃* Multiplicative (Fin 4 → ZMod q) :=
    (QuotientGroup.quotientMulEquivOfEq hΦ.symm).trans e
  let ℓ : Additive (Abelianization D) ≃ₗ[ZMod q] (Fin 4 → ZMod q) :=
    (MulEquiv.toAdditiveLeft e₁).toLinearEquiv (R := ZMod q) fun (a : ZMod q) v =>
      ZMod.map_smul (MulEquiv.toAdditiveLeft e₁) a v
  have hℓ : ∀ x : D, ℓ (Additive.ofMul (Abelianization.of x)) =
      Multiplicative.toAdd (e (x : D ⧸ frattini D)) := fun x => rfl
  have hℓs : ∀ v, ∃ x : D, ℓ (Additive.ofMul (Abelianization.of x)) = v := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm (Multiplicative.ofAdd v))
    refine ⟨x, ?_⟩
    rw [hℓ, hx, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  let B' : LinearMap.BilinForm (ZMod q) (Fin 4 → ZMod q) := LinearMap.BilinForm.congr ℓ B
  have hB' : ∀ x y : D, B' (ℓ (Additive.ofMul (Abelianization.of x)))
      (ℓ (Additive.ofMul (Abelianization.of y))) =
        B (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)) := by
    intro x y
    simp only [B', LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply]
  let bs' : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod q) (Fin 4 → ZMod q) := bs.map ℓ
  have hJ : LinearMap.BilinForm.toMatrix bs' B' = Matrix.J (Fin 2) (ZMod q) := by
    rw [← hbs]
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, bs', Module.Basis.map_apply, B',
      LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply]
  let A : Matrix (Fin 4) (Fin 4) (ZMod q) ≃ₐ[ZMod q]
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q) :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv bs')
  let τ : GL (Fin 4) (ZMod q) ≃* GL (Fin 2 ⊕ Fin 2) (ZMod q) :=
    Units.mapEquiv A.toRingEquiv.toMulEquiv
  have hτ : ∀ M : GL (Fin 4) (ZMod q), (τ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) =
      LinearMap.toMatrix bs' bs' (Matrix.toLin' (M : Matrix (Fin 4) (Fin 4) (ZMod q))) :=
    fun M => rfl
  have hτc : ∀ (M : GL (Fin 4) (ZMod q)) (v : Fin 4 → ZMod q),
      (τ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ bs'.equivFun v =
        bs'.equivFun ((M : Matrix (Fin 4) (Fin 4) (ZMod q)) *ᵥ v) := by
    intro M v
    rw [hτ, Module.Basis.equivFun_apply bs' v, LinearMap.toMatrix_mulVec_repr, Matrix.toLin'_apply,
      Module.Basis.equivFun_apply]
  let act : L →* MulAut D := (MulAut.characteristic D).comp MulAut.conjNormal
  have hact : ∀ (g : L) (x : D), (((act g x : D) : Q) : L) = g * ((x : Q) : L) * g⁻¹ :=
    fun g x => rfl
  have hφe : ∀ (g : L) (x : D), (φ g : Matrix (Fin 4) (Fin 4) (ZMod q)) *ᵥ
      Multiplicative.toAdd (e (x : D ⧸ frattini D)) =
        Multiplicative.toAdd (e ((act g x : D) : D ⧸ frattini D)) :=
    fun g x => he g x (act g x) (hact g x)
  have hφℓ : ∀ (g : L) (x : D), Matrix.toLin' (φ g : Matrix (Fin 4) (Fin 4) (ZMod q))
      (ℓ (Additive.ofMul (Abelianization.of x))) =
        ℓ (Additive.ofMul (Abelianization.of (act g x))) := by
    intro g x
    rw [Matrix.toLin'_apply, hℓ, hℓ, hφe]
  have hinv : ∀ g : L, B'.comp (Matrix.toLin' (φ g : Matrix (Fin 4) (Fin 4) (ZMod q)))
      (Matrix.toLin' (φ g : Matrix (Fin 4) (Fin 4) (ZMod q))) = B' := by
    intro g
    refine LinearMap.ext₂ fun u v => ?_
    obtain ⟨x, rfl⟩ := hℓs u
    obtain ⟨y, rfl⟩ := hℓs v
    rw [LinearMap.BilinForm.comp_apply, hφℓ, hφℓ, hB', hB', hB, hB]
    have hc : ⁅x, y⁆ ∈ center D := commutatorElement_mem_center hZ x y
    have hcomm : ⁅act g x, act g y⁆ = ⁅x, y⁆ := by
      rw [← map_commutatorElement]
      apply Subtype.ext
      apply Subtype.ext
      rw [hact, commute_of_mem_center g hc, mul_inv_cancel_right]
    exact congrArg (fun z : center D => Multiplicative.toAdd (ε z)) (Subtype.ext hcomm)
  have hSp : ∀ g : L, τ (φ g) ∈ CFSG.Open.StatedSp 2 (ZMod q) := by
    intro g
    have h1 := LinearMap.BilinForm.toMatrix_comp bs' bs' B'
      (Matrix.toLin' (φ g : Matrix (Fin 4) (Fin 4) (ZMod q)))
      (Matrix.toLin' (φ g : Matrix (Fin 4) (Fin 4) (ZMod q)))
    rw [hinv g, hJ] at h1
    have h2 : (τ (φ g) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) ∈
        Matrix.symplecticGroup (Fin 2) (ZMod q) := by
      rw [SymplecticGroup.mem_iff', hτ]
      exact h1.symm
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.2 h2
  have hBsp : ∀ a b : Fin 4 → ZMod q,
      spForm 2 (ZMod q) (bs'.equivFun a) (bs'.equivFun b) = -B' a b := by
    intro a b
    have hg : spGram 2 (ZMod q) = -Matrix.J (Fin 2) (ZMod q) :=
      CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J
    rw [spForm, Matrix.toBilin'_apply', hg, Matrix.neg_mulVec, dotProduct_neg, ← hJ,
      LinearMap.BilinForm.dotProduct_toMatrix_mulVec, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  refine ⟨τ, bs'.equivFun, hτc, hSp, hX3, ?_⟩
  let κ : D.map Q.subtype ≃* D := (D.equivMapOfInjective Q.subtype Q.subtype_injective).symm
  have hκ : ∀ x : D.map Q.subtype, (((κ x : D) : Q) : L) = x := by
    intro x
    have h := Subgroup.coe_equivMapOfInjective_apply D Q.subtype Q.subtype_injective (κ x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  let π : D.map Q.subtype →* Multiplicative (Fin 2 ⊕ Fin 2 → ZMod q) :=
    (AddEquiv.toMultiplicative bs'.equivFun.toAddEquiv).toMonoidHom.comp
      (e.toMonoidHom.comp ((QuotientGroup.mk' (frattini D)).comp κ.toMonoidHom))
  have hπ : ∀ x : D.map Q.subtype, Multiplicative.toAdd (π x) =
      bs'.equivFun (ℓ (Additive.ofMul (Abelianization.of (κ x)))) := fun x => rfl
  refine ⟨D.map Q.subtype, inferInstance, (map_subtype_le D).trans hQX, ?_, ?_, π, ?_, ?_, ?_,
    ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h := hDexp x hx
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, h, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hD5]
  · intro w
    obtain ⟨x, hx⟩ := hℓs (bs'.equivFun.symm (Multiplicative.toAdd w))
    refine ⟨κ.symm x, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hπ, MulEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply]
  · intro x hx g
    have h1 : bs'.equivFun (ℓ (Additive.ofMul (Abelianization.of (κ x)))) = 0 := by
      rw [← hπ, hx, toAdd_one]
    rw [LinearEquiv.map_eq_zero_iff, hℓ, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, hΦ, ← hZ] at h1
    have h2 := commute_of_mem_center g h1
    rwa [hκ] at h2
  · intro g x y hxy
    rw [hπ, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hτc, hℓ, hℓ]
    congr 1
    exact he g (κ x) (κ y) (by rw [hκ, hκ]; exact hxy)
  · intro x y
    rw [hπ, hπ, hBsp, neg_eq_zero, hB', ← hval, commutatorElement_eq_one_iff_mul_comm,
      ← map_mul κ, ← map_mul κ, κ.injective.eq_iff]

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
