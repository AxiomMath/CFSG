module

public import CFSG.RankThree.PartOne.KS.HNFiveBasic

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

variable {G : Type*} [Group G]

theorem dot_single_single (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) (i j : Fin 4) :
    Pi.single i 1 ⬝ᵥ (F *ᵥ Pi.single j 1) = F i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem quad_skew (f : Fin 4 → Fin 4 → ZMod 5) (c : Fin 4 → ZMod 5)
    (hs : ∀ i j, f i j + f j i = 0) : ∑ i, c i * ∑ j, f i j * c j = 0 := by
  have h2' : (2 : ZMod 5) ≠ 0 := by decide
  have hS : ∑ i, c i * ∑ j, f i j * c j = ∑ i, ∑ j, c i * f i j * c j := by
    simp only [Finset.mul_sum, mul_assoc]
  have hS' : ∑ i, ∑ j, c i * f i j * c j = ∑ i, ∑ j, c j * f j i * c i := Finset.sum_comm
  have h2 : (2 : ZMod 5) * ∑ i, ∑ j, c i * f i j * c j = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS']
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    have e : c i * f i j * c j + c j * f j i * c i = (f i j + f j i) * (c i * c j) := by ring
    rw [e, hs i j, zero_mul]
  rw [hS]
  have := fact5
  exact (mul_eq_zero.1 h2).resolve_left h2'

theorem alt_iff (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    (∀ c : Fin 4 → ZMod 5, c ⬝ᵥ (F *ᵥ c) = 0) ↔ Fᵀ = -F ∧ ∀ i, F i i = 0 := by
  constructor
  · intro hF
    have hd : ∀ i, F i i = 0 := fun i => by
      have := hF (Pi.single i 1)
      rwa [dot_single_single] at this
    refine ⟨?_, hd⟩
    ext i j
    have h1 := hF (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, dot_single_single,
      dot_single_single, dot_single_single, dot_single_single, hd, hd, zero_add, add_zero] at h1
    rw [Matrix.transpose_apply, Matrix.neg_apply, eq_neg_iff_add_eq_zero]
    exact h1
  · rintro ⟨hT, -⟩ c
    have hs : ∀ i j, F i j + F j i = 0 := fun i j => by
      have h1 : F j i = -F i j := by
        have := congrFun (congrFun hT i) j
        simpa [Matrix.transpose_apply] using this
      rw [h1]
      exact add_neg_cancel _
    exact quad_skew F c hs

theorem mat_eq_of_forms {F F' : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    (h : ∀ c c' : Fin 4 → ZMod 5, c ⬝ᵥ (F *ᵥ c') = c ⬝ᵥ (F' *ᵥ c')) : F = F' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [dot_single_single, dot_single_single] at this

section Coordinates

variable {q : Fin 4 → G} {z : G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}

@[expose] def ab (u : QG q) : Additive (Abelianization (QG q)) :=
  Additive.ofMul (Abelianization.of u)

theorem ab_surjective : Function.Surjective (ab (q := q)) := by
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (commutator (QG q)) (Additive.toMul v)
  exact ⟨u, by rw [ab]; exact congrArg Additive.ofMul hu⟩

@[expose] noncomputable def cAb (hD : CommData 5 q z M) :
    Additive (Abelianization (QG q)) →+ (Fin 4 → ZMod 5) where
  toFun v := Multiplicative.toAdd (Abelianization.lift hD.coordHom (Additive.toMul v))
  map_zero' := by simp only [toMul_zero, map_one, toAdd_one]
  map_add' v w := by simp only [toMul_add, map_mul, toAdd_mul]

theorem cAb_ab (hD : CommData 5 q z M) (u : QG q) : cAb hD (ab u) = coord 5 q z M u := by
  simp [cAb, ab, Abelianization.lift_apply_of, CommData.coordHom_apply]

theorem cAb_surjective (hD : CommData 5 q z M) : Function.Surjective (cAb hD) := by
  intro c
  obtain ⟨u, hu⟩ := hD.coordHom_surjective (Multiplicative.ofAdd c)
  refine ⟨ab ⟨u.1, u.2⟩, ?_⟩
  rw [cAb_ab]
  rw [CommData.coordHom_apply] at hu
  exact Multiplicative.ofAdd.injective hu

theorem cAb_q (hD : CommData 5 q z M) (i : Fin 4) :
    cAb hD (ab ⟨q i, q_mem i⟩) = Pi.single i 1 := by
  rw [cAb_ab]
  exact hD.coord_q i

theorem cAb_smul [Module (ZMod 5) (Additive (Abelianization (QG q)))] (hD : CommData 5 q z M)
    (c : ZMod 5) (v : Additive (Abelianization (QG q))) : cAb hD (c • v) = c • cAb hD v := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

end Coordinates

namespace Rel

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}
  {XU : GL (Fin 4) (ZMod 5)} {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ} (hR : Rel q z x r M XU cx BU cr)
include hR

theorem cAb_injective [Finite G] : Function.Injective (cAb hR.commData) := by
  have := fact5
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨u, rfl⟩ := ab_surjective v
  rw [cAb_ab] at hv
  have hz : (u : G) ∈ zpowers z := by
    have hker : (⟨u.1, u.2⟩ : closure (Set.range q)) ∈ hR.commData.coordHom.ker := by
      rw [MonoidHom.mem_ker, CommData.coordHom_apply]
      exact (congrArg Multiplicative.ofAdd hv).trans ofAdd_zero
    rw [hR.commData.ker_coordHom, mem_subgroupOf] at hker
    exact hker
  have hcomm : u ∈ commutator (QG q) := by
    rw [hR.commData.commutator_eq hR.z_eq, mem_subgroupOf]
    exact hz
  rw [← Abelianization.ker_of, MonoidHom.mem_ker] at hcomm
  rw [ab, hcomm]
  rfl

theorem cAb_conj [Finite G] {g : G} (hg : g ∈ HG q x r) (u v : QG q)
    (hv : (v : G) = g * (u : G) * g⁻¹) :
    cAb hR.commData (ab v) =
      (CommData.actMat 5 q z M g⁻¹)ᵀ *ᵥ cAb hR.commData (ab u) := by
  rw [cAb_ab, cAb_ab, Matrix.mulVec_transpose]
  have e : g * (u : G) * g⁻¹ = (g⁻¹)⁻¹ * u * g⁻¹ := by rw [inv_inv]
  show coord 5 q z M (v : G) = _
  rw [hv, e]
  exact hR.commData.coord_conj (hR.conj_q_mem_H (inv_mem hg)) u.2

section Forms

variable [Module (ZMod 5) (Additive (Abelianization (QG q)))]

@[expose] noncomputable def cAbLin :
    Additive (Abelianization (QG q)) →ₗ[ZMod 5] (Fin 4 → ZMod 5) where
  toFun := cAb hR.commData
  map_add' := map_add (cAb hR.commData)
  map_smul' := cAb_smul hR.commData

@[expose] noncomputable def formOf (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    LinearMap.BilinForm (ZMod 5) (Additive (Abelianization (QG q))) :=
  LinearMap.mk₂ (ZMod 5) (fun v w => cAb hR.commData v ⬝ᵥ (F *ᵥ cAb hR.commData w))
    (fun v₁ v₂ w => by rw [map_add, add_dotProduct])
    (fun c v w => by rw [cAb_smul, smul_dotProduct])
    (fun v w₁ w₂ => by rw [map_add, Matrix.mulVec_add, dotProduct_add])
    (fun c v w => by rw [cAb_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem formOf_apply (F : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (v w : Additive (Abelianization (QG q))) :
    hR.formOf F v w = cAb hR.commData v ⬝ᵥ (F *ᵥ cAb hR.commData w) := rfl

@[expose] noncomputable def commForm :
    LinearMap.BilinForm (ZMod 5) (Additive (Abelianization (QG q))) :=
  hR.formOf M

theorem commForm_ab (u v : QG q) : hR.commForm (ab u) (ab v) = lg 5 z (bcomm (u : G) v) := by
  rw [commForm, hR.formOf_apply, cAb_ab, cAb_ab, hR.lg_bcomm u.2 v.2]

theorem formOf_alt_iff (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    (∀ v, hR.formOf F v v = 0) ↔ Fᵀ = -F ∧ ∀ i, F i i = 0 := by
  rw [← alt_iff]
  constructor
  · intro h c
    obtain ⟨v, rfl⟩ := cAb_surjective hR.commData c
    rw [← hR.formOf_apply]
    exact h v
  · intro h v
    rw [hR.formOf_apply]
    exact h _

theorem formOf_smul (c : ZMod 5) (F : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    hR.formOf (c • F) = c • hR.formOf F := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hR.formOf_apply, hR.formOf_apply,
    Matrix.smul_mulVec, dotProduct_smul]

@[expose] noncomputable def gram
    (β : LinearMap.BilinForm (ZMod 5) (Additive (Abelianization (QG q)))) :
    Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  Matrix.of fun i j => β (ab ⟨q i, q_mem i⟩) (ab ⟨q j, q_mem j⟩)

section FormsFinite

variable [Finite G]

@[expose] noncomputable def cAbEquiv :
    Additive (Abelianization (QG q)) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  LinearEquiv.ofBijective hR.cAbLin ⟨hR.cAb_injective, cAb_surjective hR.commData⟩

theorem cAbEquiv_apply (v : Additive (Abelianization (QG q))) :
    hR.cAbEquiv v = cAb hR.commData v := rfl

@[expose] noncomputable def basisV :
    Module.Basis (Fin 4) (ZMod 5) (Additive (Abelianization (QG q))) :=
  Module.Basis.ofEquivFun hR.cAbEquiv

theorem basisV_apply (i : Fin 4) : hR.basisV i = ab ⟨q i, q_mem i⟩ := by
  simp only [basisV, Module.Basis.coe_ofEquivFun]
  rw [LinearEquiv.symm_apply_eq, cAbEquiv_apply, cAb_q]

theorem eq_formOf_gram (β : LinearMap.BilinForm (ZMod 5) (Additive (Abelianization (QG q)))) :
    β = hR.formOf (gram β) := by
  apply LinearMap.ext_basis hR.basisV hR.basisV
  intro i j
  rw [hR.basisV_apply, hR.basisV_apply, hR.formOf_apply, cAb_q, cAb_q, Matrix.mulVec_single_one]
  simp [gram, single_dotProduct, Matrix.col_apply]

end FormsFinite

end Forms

end Rel

end CFSG.RankThree.PartOne.KS.HNFive
