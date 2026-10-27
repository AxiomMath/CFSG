module

public import CFSG.Quasithin.H13.L32AL2y

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

namespace L2Cfg

variable {Hs Ts Ls Rs O : Subgroup (MulAut (VM F))} {Vs : Subgroup (VM F)} {t : MulAut (VM F)}
  {a : VM F} [Finite F] [CharP F 2]

theorem ls_le_normalizer_sZero (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    Ls ≤ Subgroup.normalizer ((sZero : Subgroup (MulAut (VM F))) : Set (MulAut (VM F))) := by
  intro y hy
  obtain ⟨g, h, hg, hh, rfl⟩ := C.ls_borel hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨p, q, rfl⟩
    rw [borel_conj_sZero hg hh]
    exact ⟨_, _, rfl⟩
  · intro hx
    obtain ⟨p, q, hpq⟩ := hx
    have e : x = (rho (g, h))⁻¹ * rho (utS p, utS q) * rho (g, h) := by
      rw [← hpq]
      group
    rw [e, ← map_inv, Prod.inv_mk]
    have hg' : (((g⁻¹ : SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [hg]
    have hh' : (((h⁻¹ : SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [hh]
    have := borel_conj_sZero hg' hh' p q
    rw [← map_inv, Prod.inv_mk, inv_inv, inv_inv] at this
    rw [this]
    exact ⟨_, _, rfl⟩

theorem exists_sZero_move (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : ∃ s ∈ sZero, s a ≠ a := by
  by_contra hall
  push Not at hall
  have hV : ∀ w : VM F, w * w = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcl : Subgroup.closure {w | ∃ s ∈ sZero, w = s a} ≤ Subgroup.zpowers a := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [hall s hs]
    exact Subgroup.mem_zpowers a
  have hle := C.vs_le.trans hcl
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card (Subgroup.zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hV])
  rw [C.hVcard] at h1
  omega

theorem mem_rs_of_fix (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {x : MulAut (VM F)} (hx : x ∈ Ts)
    (hfix : ∀ v ∈ Vs, x v = v) : x ∈ Rs := by
  obtain ⟨τ, hτ⟩ := isSemi_of_mem_normalizer (by rw [C.card]) (C.mem_gamma hx)
  have hτ1 : τ = 1 := by
    refine RingEquiv.ext fun c => ?_
    have e1 := hfix _ (C.e11_mem c)
    have e2 := hfix _ (C.e11_mem 1)
    have e3 := hτ c matE
    rw [one_smul] at e2
    rw [e1, toAdd_ofAdd, e2, toAdd_ofAdd] at e3
    have := congrFun (congrFun e3 0) 0
    simpa [matE] using this.symm
  rcases C.lin_cases hx (hτ1 ▸ hτ) with h | h
  · exact C.sZero_le_rs h
  · have e : x = (x * t) * t := by rw [mul_assoc, C.ht2, mul_one]
    rw [e]
    exact Rs.mul_mem (C.sZero_le_rs h) C.ht

end L2Cfg

end CFSG.Quasithin.H13.L32A.L2
