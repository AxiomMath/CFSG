module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerElts

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover

namespace TwE6Per

theorem commute_rankOne_12 {k : Type} [Field k] {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k vb1) (hy : y ∈ rankOne k vb2) : Commute x y :=
  commute_rankOne isRoot_vb1 isRoot_vb2 (by decide) (by decide)
    (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx hy

theorem commute_rankOne_13 {k : Type} [Field k] {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k vb1) (hy : y ∈ rankOne k vb3) : Commute x y :=
  commute_rankOne isRoot_vb1 isRoot_vb3 (by decide) (by decide)
    (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx hy

theorem commute_rankOne_23 {k : Type} [Field k] {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k vb2) (hy : y ∈ rankOne k vb3) : Commute x y :=
  commute_rankOne isRoot_vb2 isRoot_vb3 (by decide) (by decide)
    (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx hy

theorem commute_rankOne_th {k : Type} [Field k] {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ = vb1 ∨ γ = vb2 ∨ γ = vb3) {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ)
    (c : k) : Commute x (e6Data_valid.xm k vth c) := by
  rcases hγ with rfl | rfl | rfl
  · exact commute_rankOne isRoot_vb1 isRoot_vth (by decide) (by decide)
      (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx (xm_mem_rankOne _ c)
  · exact commute_rankOne isRoot_vb2 isRoot_vth (by decide) (by decide)
      (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx (xm_mem_rankOne _ c)
  · exact commute_rankOne isRoot_vb3 isRoot_vth (by decide) (by decide)
      (not_isRoot_of_form' (by decide)) (not_isRoot_of_form' (by decide)) hx (xm_mem_rankOne _ c)

section Torus

variable {k : Type} [Field k]

theorem torusHom_eq_minTorus : torusHom k = minTorus e6Data_valid k := rfl

theorem rootChar_pair_eq_one (γ : Fin (Tag.rank .E6) → ℤ) {a b : Fin (Tag.rank .E6)}
    (h : cartanCoord γ a = cartanCoord γ b) (μ : kˣ) :
    rootChar k γ (Pi.mulSingle a μ * Pi.mulSingle b μ⁻¹) = 1 := by
  rw [map_mul, rootChar_mulSingle, rootChar_mulSingle, h, inv_zpow', zpow_neg, mul_inv_cancel]

theorem torusHom_conj_rankOne {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    {u : Fin (Tag.rank .E6) → kˣ} (h1 : rootChar k γ u = 1) (h2 : rootChar k (-γ) u = 1)
    {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ) :
    Commute (torusHom k u) x := by
  have hgen : ∀ c : k, ∀ δ, (δ = γ ∨ δ = -γ) →
      torusHom k u * e6Data_valid.xm k δ c * (torusHom k u)⁻¹ = e6Data_valid.xm k δ c := by
    rintro c δ (rfl | rfl)
    · rw [torusHom_eq_minTorus, minTorus_conj_xm e6Data_valid k u hγ, h1, Units.val_one, one_mul]
    · rw [torusHom_eq_minTorus, minTorus_conj_xm e6Data_valid k u (IsRoot.neg hγ), h2,
        Units.val_one, one_mul]
  have hle : rankOne k γ ≤ Subgroup.centralizer {torusHom k u} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl | rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (mul_inv_eq_iff_eq_mul.1 (hgen c γ (Or.inl rfl))).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (mul_inv_eq_iff_eq_mul.1 (hgen c (-γ) (Or.inr rfl))).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

@[expose] def uOne (μ : kˣ) : Fin (Tag.rank .E6) → kˣ :=
  Pi.mulSingle (nd 0) μ * Pi.mulSingle (nd 5) μ⁻¹

@[expose] def uTwo (μ : kˣ) : Fin (Tag.rank .E6) → kˣ :=
  Pi.mulSingle (nd 2) μ * Pi.mulSingle (nd 4) μ⁻¹

theorem rootChar_uOne {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ = vb1 ∨ γ = vb2 ∨ γ = vb3 ∨ γ = -vb1 ∨ γ = -vb2 ∨ γ = -vb3 ∨ γ = vth) (μ : kˣ) :
    rootChar k γ (uOne μ) = 1 :=
  rootChar_pair_eq_one γ (by rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) μ

theorem rootChar_uTwo {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ = vb1 ∨ γ = vb2 ∨ γ = vb3 ∨ γ = -vb1 ∨ γ = -vb2 ∨ γ = -vb3 ∨ γ = vth) (μ : kˣ) :
    rootChar k γ (uTwo μ) = 1 :=
  rootChar_pair_eq_one γ (by rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) μ

theorem commute_torus_rankOne {u : Fin (Tag.rank .E6) → kˣ} (μ : kˣ)
    (hu : u = uOne μ ∨ u = uTwo μ) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ = vb1 ∨ γ = vb2 ∨ γ = vb3) {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ) :
    Commute (torusHom k u) x := by
  have hr : ∀ γ' : Fin (Tag.rank .E6) → ℤ,
      (γ' = vb1 ∨ γ' = vb2 ∨ γ' = vb3 ∨ γ' = -vb1 ∨ γ' = -vb2 ∨ γ' = -vb3 ∨ γ' = vth) →
        rootChar k γ' u = 1 := fun γ' h => by
    rcases hu with rfl | rfl
    · exact rootChar_uOne h μ
    · exact rootChar_uTwo h μ
  have hroot : IsRoot .E6 γ := by
    rcases hγ with rfl | rfl | rfl
    · exact isRoot_vb1
    · exact isRoot_vb2
    · exact isRoot_vb3
  refine torusHom_conj_rankOne hroot (hr γ ?_) (hr (-γ) ?_) hx
  · rcases hγ with rfl | rfl | rfl <;> simp
  · rcases hγ with rfl | rfl | rfl <;> simp

theorem commute_torus_th {u : Fin (Tag.rank .E6) → kˣ} (μ : kˣ) (hu : u = uOne μ ∨ u = uTwo μ)
    (c : k) : Commute (torusHom k u) (e6Data_valid.xm k vth c) := by
  have h : rootChar k vth u = 1 := by
    rcases hu with rfl | rfl
    · exact rootChar_uOne (by simp) μ
    · exact rootChar_uTwo (by simp) μ
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul, torusHom_eq_minTorus,
    minTorus_conj_xm e6Data_valid k u isRoot_vth, h, Units.val_one, one_mul]

end Torus

end TwE6Per

end CFSG.StandardType
