module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTriangle
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.QTwoLin

open Module

private theorem ggQ2xr_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) a ha

private theorem ggQ2xr_sq_eq_one (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a * a = 1) a ha

private theorem ggQ2xr_mul_ne_neg_one (a b : ZMod 3) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (h : a * b ≠ -1) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso; exact h (by decide)
  · exfalso; exact h (by decide)
  · rfl

private theorem ggQ2xr_reflTransGen_const {κ : Type*} (r : κ → κ → Prop) (f : κ → ZMod 3)
    (hstep : ∀ a b, r a b → f a = f b) {a b : κ} (h : Relation.ReflTransGen r a b) :
    f a = f b := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (hstep _ _ hbc)

theorem refl_coeff_of_pairs {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type*}
    (h : ι → V) (α : ι → Dual (ZMod 3) V) (hα : ∀ γ, α γ (h γ) = 2) (d : ι → ZMod 3)
    (hd : ∀ γ, d γ ≠ 0) (hsym : ∀ γ δ, d γ * α γ (h δ) = d δ * α δ (h γ))
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : TransvectionFree A)
    (hW : ∀ γ, Module.reflection (hα γ) ∈ A)
    {c : V} {φ : Dual (ZMod 3) V} (hφ : φ c = 2) (ht : Module.reflection hφ ∈ A)
    (hS : ∃ γ, α γ c ≠ 0)
    (hconn : ∀ γ δ, α γ c ≠ 0 → α δ c ≠ 0 →
      Relation.ReflTransGen (fun γ' δ' => α γ' c ≠ 0 ∧ α δ' c ≠ 0 ∧ α γ' (h δ') ≠ 0) γ δ) :
    ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ γ, φ (h γ) = ε * (d γ * α γ c) := by
  have hpair : ∀ γ, φ (h γ) = 0 ↔ α γ c = 0 := by
    intro γ
    constructor
    · intro hφh
      by_contra hαc
      have htv : IsTransvectionLin ((Module.reflection hφ * Module.reflection (hα γ)) ^ 2) :=
        transvection_of_pair (K := ZMod 3) (c := c) (h := h γ) (φ := φ) (α := α γ)
          hφ (hα γ) hφh hαc
      have hmem : (Module.reflection hφ * Module.reflection (hα γ)) ^ 2 ∈ A :=
        pow_mem (A.mul_mem ht (hW γ)) 2
      exact hA _ hmem htv
    · intro hαc
      by_contra hφh
      have htv : IsTransvectionLin ((Module.reflection (hα γ) * Module.reflection hφ) ^ 2) :=
        transvection_of_pair (K := ZMod 3) (c := h γ) (h := c) (φ := α γ) (α := φ)
          (hα γ) hφ hαc hφh
      have hmem : (Module.reflection (hα γ) * Module.reflection hφ) ^ 2 ∈ A :=
        pow_mem (A.mul_mem (hW γ) ht) 2
      exact hA _ hmem htv
  obtain ⟨γ₀, hγ₀⟩ := hS
  let ε : ι → ZMod 3 := fun γ => φ (h γ) / (d γ * α γ c)
  have hφh_of_ne : ∀ γ, α γ c ≠ 0 → φ (h γ) ≠ 0 := by
    intro γ hγ h0
    exact hγ ((hpair γ).mp h0)
  have hεmul : ∀ γ (hγ : α γ c ≠ 0), ε γ * (d γ * α γ c) = φ (h γ) := by
    intro γ hγ
    exact div_mul_cancel₀ (φ (h γ)) (mul_ne_zero (hd γ) hγ)
  have hεne : ∀ γ (hγ : α γ c ≠ 0), ε γ ≠ 0 := by
    intro γ hγ
    exact div_ne_zero (hφh_of_ne γ hγ) (mul_ne_zero (hd γ) hγ)
  have hεone : ∀ γ (hγ : α γ c ≠ 0), ε γ = 1 ∨ ε γ = -1 :=
    fun γ hγ => ggQ2xr_eq_one_or_neg_one (ε γ) (hεne γ hγ)
  have hC : ∀ γ (hγ : α γ c ≠ 0), φ (h γ) * α γ c = ε γ * d γ := by
    intro γ hγ
    rw [← hεmul γ hγ]
    calc ε γ * (d γ * α γ c) * α γ c
        = ε γ * d γ * (α γ c * α γ c) := by ring
      _ = ε γ * d γ := by rw [ggQ2xr_sq_eq_one (α γ c) hγ, mul_one]
  have hadj : ∀ γ δ, α γ c ≠ 0 → α δ c ≠ 0 → α γ (h δ) ≠ 0 → ε γ = ε δ := by
    intro γ δ hγ hδ hαγhδ
    have hsne : d γ * α γ (h δ) ≠ 0 := mul_ne_zero (hd γ) hαγhδ
    have hs2 : (d γ * α γ (h δ)) * (d γ * α γ (h δ)) = 1 :=
      ggQ2xr_sq_eq_one _ hsne
    have hαδhγ : α δ (h γ) ≠ 0 := by
      intro h0
      exact hsne (by rw [hsym γ δ, h0, mul_zero])
    have hprod3 : (d γ * d δ) * (α γ (h δ) * α δ (h γ)) = 1 := by
      calc (d γ * d δ) * (α γ (h δ) * α δ (h γ))
          = (d γ * α γ (h δ)) * (d δ * α δ (h γ)) := by ring
        _ = (d γ * α γ (h δ)) * (d γ * α γ (h δ)) := by rw [← hsym γ δ]
        _ = 1 := hs2
    let c' : Fin 3 → V := ![c, h γ, h δ]
    let φ' : Fin 3 → Dual (ZMod 3) V := ![φ, α γ, α δ]
    have hφ' : ∀ i, φ' i (c' i) = 2 := by
      intro i
      fin_cases i <;> simp [c', φ', hφ, hα]
    have hoff : ∀ i j, i ≠ j → φ' i (c' j) ≠ 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [c', φ']
      · exact absurd rfl hij
      · exact hφh_of_ne γ hγ
      · exact hφh_of_ne δ hδ
      · exact hγ
      · exact absurd rfl hij
      · exact hαγhδ
      · exact hδ
      · exact hαδhγ
      · exact absurd rfl hij
    have hnot : ε γ * ε δ ≠ -1 := by
      intro hneg
      have hprodval :
          (φ' 0 (c' 1) * φ' 1 (c' 0)) * (φ' 0 (c' 2) * φ' 2 (c' 0)) *
            (φ' 1 (c' 2) * φ' 2 (c' 1)) = ε γ * ε δ := by
        rw [show φ' 0 (c' 1) = φ (h γ) from rfl, show φ' 1 (c' 0) = α γ c from rfl,
          show φ' 0 (c' 2) = φ (h δ) from rfl, show φ' 2 (c' 0) = α δ c from rfl,
          hC γ hγ, hC δ hδ]
        calc (ε γ * d γ) * (ε δ * d δ) * (α γ (h δ) * α δ (h γ))
            = ε γ * ε δ * ((d γ * d δ) * (α γ (h δ) * α δ (h γ))) := by ring
          _ = ε γ * ε δ * 1 := by rw [hprod3]
          _ = ε γ * ε δ := by ring
      have hprod :
          (φ' 0 (c' 1) * φ' 1 (c' 0)) * (φ' 0 (c' 2) * φ' 2 (c' 0)) *
            (φ' 1 (c' 2) * φ' 2 (c' 1)) = -1 := by
        rw [hprodval, hneg]
      have hclosure : Subgroup.closure (Set.range fun i => Module.reflection (hφ' i)) ≤ A := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ht
        · exact hW γ
        · exact hW δ
      obtain ⟨g, hgmem, hgtv⟩ := transvection_of_triangle c' φ' hφ' hoff hprod
      exact hA g (hclosure hgmem) hgtv
    exact ggQ2xr_mul_ne_neg_one (ε γ) (ε δ) (hεone γ hγ) (hεone δ hδ) hnot
  have hconst : ∀ γ, α γ c ≠ 0 → ε γ = ε γ₀ := by
    intro γ hγ
    have hstep : ∀ a b, (α a c ≠ 0 ∧ α b c ≠ 0 ∧ α a (h b) ≠ 0) → ε a = ε b := by
      rintro a b ⟨ha, hb, hab⟩
      exact hadj a b ha hb hab
    exact ggQ2xr_reflTransGen_const _ ε hstep (hconn γ γ₀ hγ hγ₀)
  refine ⟨ε γ₀, hεone γ₀ hγ₀, ?_⟩
  intro γ
  by_cases hγ : α γ c = 0
  · have hφh : φ (h γ) = 0 := (hpair γ).mpr hγ
    rw [hφh, hγ, mul_zero, mul_zero]
  · rw [← hεmul γ hγ, hconst γ hγ]

end CFSG.StandardType.QTwoLin

end
